// Turn a failed nightly run into a deduplicated issue naming the test that failed.
//
// Failing job and step names survive in the API for about a year, but the *test* name only
// exists in the job log, which expires after 90 days. Recovering it later is disproportionately
// hard, so grab it while it is still there.

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";
const FAILED_TEST = /([A-Za-z0-9_./-]+\.dfy) \[FAIL\]/g;

// Only these steps run tests, so only these have a test name to find in the log. An allowlist
// rather than a list of infrastructure steps to skip: new setup steps get added to these
// workflows regularly, and the failure mode of a stale allowlist (no test name, fall back to
// job+step) is much kinder than that of a stale denylist (download every log for nothing).
const TEST_STEP = /^Run integration tests/;

// Human triage wins: if someone has closed an issue with one of these, keep recording
// occurrences but do not reopen it.
const NO_REOPEN_LABELS = ["wontfix", "known-flake"];

// Dedupe on a marker in the body, not on the title. Titles are human-editable and this script
// rewrites them to carry the count, so the two would fight.
const marker = key => `<!-- nightly-flake-key: ${key} -->`;

function titleFor(key, count) {
  return `${TITLE_PREFIX}${key}` + (count > 1 ? ` (${count}x)` : "");
}

function countFromTitle(title) {
  const m = /\((\d+)x\)\s*$/.exec(title);
  return m ? parseInt(m[1], 10) : 1;
}

function failingStepsOf(job) {
  return (job.steps || [])
    .filter(s => s.conclusion === "failure" || s.conclusion === "timed_out")
    .map(s => s.name);
}

// The test names in a job log. Returns null if the log could not be read, which is different
// from "read it and found no test": the caller counts those to spot a systemic problem.
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
    return null;
  }
}

// One key per thing worth tracking: a test name where we could find one, otherwise the job and
// step, so that infrastructure failures are still recorded.
//
// Only attempt 1 is read. A re-run overwrites the visible conclusion, so attempt 1 is what makes
// the failure rate honest; failures unique to a later attempt are not recorded, which has not
// happened once in the run history to date.
async function keysForRun({ github, context, core }, run_id) {
  const jobs = await github.paginate(github.rest.actions.listJobsForWorkflowRunAttempt, {
    owner: context.repo.owner,
    repo: context.repo.repo,
    run_id,
    attempt_number: 1,
    per_page: 100,
  });

  const keys = new Map();
  let logsAttempted = 0;
  let logsFailed = 0;

  for (const job of jobs) {
    if (job.conclusion !== "failure" && job.conclusion !== "timed_out") {
      continue;
    }
    const steps = failingStepsOf(job);
    const shortName = job.name.split(" / ").pop();

    let tests = [];
    if (steps.some(s => TEST_STEP.test(s))) {
      logsAttempted++;
      tests = await testsInLog({ github, context, core }, job);
      if (tests === null) {
        logsFailed++;
        tests = [];
      }
    }

    if (tests.length > 0) {
      for (const test of tests) {
        keys.set(test, `\`${shortName}\`, step \`${steps.join("`, `")}\``);
      }
    } else {
      keys.set(`${shortName} - ${steps[0] || job.conclusion}`, `\`${shortName}\``);
    }
  }

  // Reading the log is the whole point of this job, so a total failure must be loud rather than
  // quietly degrading to job+step keys that look like a successful run.
  if (logsAttempted > 0 && logsFailed === logsAttempted) {
    core.warning(
      `Could not read any of the ${logsAttempted} test job logs for run ${run_id}. Test names ` +
      `will be missing from the issues below. Check that this workflow still has actions: read ` +
      `and that the logs have not passed their 90-day retention.`);
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
    const m = /<!-- nightly-flake-key: (.*?) -->/.exec(issue.body || "");
    if (m) {
      byKey.set(m[1], issue);
    }
  }
  return byKey;
}

module.exports = async ({ github, context, core }, run_id) => {
  if (!Number.isInteger(run_id) || run_id <= 0) {
    throw new Error(`not a workflow run id: ${JSON.stringify(run_id)}`);
  }

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
          `Opened automatically because the nightly build failed. The name above comes from the ` +
          `job log, which expires after 90 days, so it is recorded here while it still exists.\n\n` +
          `Further occurrences are added as comments and counted in the title. Close this with ` +
          `\`${NO_REOPEN_LABELS.join("` or `")}\` to stop it being reopened.\n\n` +
          marker(key),
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

    const labels = (issue.labels || []).map(l => (typeof l === "string" ? l : l.name));
    const declined = labels.some(l => NO_REOPEN_LABELS.includes(l));
    const update = {
      owner, repo, issue_number: issue.number,
      title: titleFor(key, countFromTitle(issue.title) + 1),
    };
    // Reopen so the occurrence is visible, unless a human has deliberately closed it.
    if (!declined) {
      update.state = "open";
    }
    await github.rest.issues.update(update);
    core.info(`updated #${issue.number} for ${key}${declined ? " (left closed)" : ""}`);
  }
};
