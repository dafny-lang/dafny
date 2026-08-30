// Turn a failed nightly run into a deduplicated issue naming the test that failed.
//
// Failing job and step names survive in the API for about a year, but the *test* name only
// exists in the job log, which expires after 90 days. Recovering it later is disproportionately
// hard, so grab it while it is still there.

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";
const FAILED_TEST = /([A-Za-z0-9_./-]+\.dfy) \[FAIL\]/g;

// A failing step whose name matches this is infrastructure, not a test, so there is no test
// name to look for in the log.
const NOT_A_TEST_STEP = /^(Set up job|Run actions\/|Post |Create release|Install |Setup |Upload )/;

function titleFor(key, count) {
  return `${TITLE_PREFIX}${key}` + (count > 1 ? ` (${count}x)` : "");
}

function countFromTitle(title) {
  const m = /\((\d+)x\)\s*$/.exec(title);
  return m ? parseInt(m[1], 10) : 1;
}

function keyFor(title) {
  return title.slice(TITLE_PREFIX.length).replace(/\s*\(\d+x\)\s*$/, "");
}

function failingStepsOf(job) {
  return (job.steps || [])
    .filter(s => s.conclusion === "failure" || s.conclusion === "timed_out")
    .map(s => s.name);
}

// The test names in a job log, or [] if the log has expired or cannot be read. A missing log
// must never fail this workflow: the fallback key is still useful.
async function testsInLog({ github, context, core }, job) {
  try {
    const res = await github.rest.actions.downloadJobLogsForWorkflowRun({
      owner: context.repo.owner,
      repo: context.repo.repo,
      job_id: job.id,
    });
    const text = typeof res.data === "string" ? res.data : Buffer.from(res.data).toString("utf8");
    return [...new Set([...text.matchAll(FAILED_TEST)].map(m => m[1]))];
  } catch (e) {
    core.warning(`could not read the log for job ${job.id} (${job.name}): ${e.message}`);
    return [];
  }
}

// One key per thing worth tracking: a test name where we could find one, otherwise the job and
// step, so that infrastructure failures are still recorded.
async function keysForRun({ github, context, core }, run_id) {
  const { data } = await github.rest.actions.listJobsForWorkflowRunAttempt({
    owner: context.repo.owner,
    repo: context.repo.repo,
    run_id,
    attempt_number: 1,
    per_page: 100,
  });

  const keys = new Map();
  for (const job of data.jobs) {
    if (job.conclusion !== "failure" && job.conclusion !== "timed_out") {
      continue;
    }
    const steps = failingStepsOf(job);
    const shortName = job.name.split(" / ").pop();
    const infrastructure = steps.length > 0 && steps.every(s => NOT_A_TEST_STEP.test(s));

    const tests = infrastructure ? [] : await testsInLog({ github, context, core }, job);
    if (tests.length > 0) {
      for (const test of tests) {
        keys.set(test, `\`${shortName}\`, step \`${steps.join("`, `") || "unknown"}\``);
      }
    } else {
      keys.set(`${shortName} - ${steps[0] || job.conclusion}`, `\`${shortName}\``);
    }
  }
  return keys;
}

// Listing by label is strongly consistent; the search API is not, and would double-file when
// two runs fail close together.
async function existingIssues({ github, context }) {
  const issues = await github.paginate(github.rest.issues.listForRepo, {
    owner: context.repo.owner,
    repo: context.repo.repo,
    labels: LABEL,
    state: "all",
    per_page: 100,
  });
  const byKey = new Map();
  for (const issue of issues) {
    if (issue.title.startsWith(TITLE_PREFIX)) {
      byKey.set(keyFor(issue.title), issue);
    }
  }
  return byKey;
}

module.exports = async ({ github, context, core }, run_id) => {
  const { owner, repo } = context.repo;
  const runUrl = `https://github.com/${owner}/${repo}/actions/runs/${run_id}`;
  const keys = await keysForRun({ github, context, core }, run_id);

  if (keys.size === 0) {
    core.info(`No failing jobs on attempt 1 of ${run_id}; nothing to triage.`);
    return;
  }

  const existing = await existingIssues({ github, context });

  for (const [key, where] of keys) {
    const body = `Failed in ${where} during ${runUrl} (attempt 1).`;
    const issue = existing.get(key);

    if (!issue) {
      const created = await github.rest.issues.create({
        owner, repo, labels: [LABEL],
        title: titleFor(key, 1),
        body:
          `${body}\n\n` +
          `Opened automatically because the nightly build failed. The test name above comes from ` +
          `the job log, which expires after 90 days, so it is recorded here while it still exists.\n\n` +
          `Further occurrences are added as comments and counted in the title.`,
      });
      core.info(`opened #${created.data.number} for ${key}`);
      continue;
    }

    // Re-running this workflow for the same run must not double-count.
    const comments = await github.paginate(github.rest.issues.listComments, {
      owner, repo, issue_number: issue.number, per_page: 100,
    });
    if (comments.some(c => c.body.includes(runUrl))) {
      core.info(`#${issue.number} already records ${runUrl}; skipping`);
      continue;
    }

    await github.rest.issues.createComment({ owner, repo, issue_number: issue.number, body });
    // Bump the count in the title, and reopen: a comment on a closed issue is easy to miss.
    await github.rest.issues.update({
      owner, repo, issue_number: issue.number,
      title: titleFor(key, countFromTitle(issue.title) + 1),
      state: "open",
    });
    core.info(`updated #${issue.number} for ${key}`);
  }
};
