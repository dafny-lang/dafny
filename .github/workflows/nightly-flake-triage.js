// Record which test failed when the nightly build goes red, into one issue per test.
// The failing test's name only exists in the run's own output, which expires after 90 days.

const fs = require("fs");
const path = require("path");

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";
const RESULTS_DIR = "test-results";

// Fallback only: this is xUnit console formatting, not a contract. Extensions match the
// FileData includes in LitTests.cs.
const FAILED_TEST_IN_LOG = /([A-Za-z0-9_./-]+\.(?:dfy|transcript)) \[FAIL\]/g;

// Which steps are worth fetching a log for. Only an optimisation, since .trx comes first.
const TEST_STEP = /^Run integration tests/;

const marker = key => `<!-- nightly-flake-key: ${key} -->`;

function titleFor(key, count) {
  return `${TITLE_PREFIX}${key}` + (count > 1 ? ` (${count}x)` : "");
}

function countFromTitle(title) {
  const m = /\((\d+)x\)\s*$/.exec(title);
  return m ? parseInt(m[1], 10) : 1;
}

function keyFromTitle(title) {
  return title.startsWith(TITLE_PREFIX)
    ? title.slice(TITLE_PREFIX.length).replace(/\s*\(\d+x\)\s*$/, "")
    : null;
}

function failingStepsOf(job) {
  return (job.steps || [])
    .filter(s => s.conclusion === "failure" || s.conclusion === "timed_out")
    .map(s => s.name);
}

// `test (macos-14, 6)` -> the artifact name integration-tests-reusable.yml uploads.
function artifactNameFor(shortJobName) {
  const m = /^test \(([^,]+), *(\d+)\)/.exec(shortJobName);
  return m ? `integration-test-results-${m[1]}-${m[2]}` : null;
}

function trxFilesUnder(dir) {
  if (!fs.existsSync(dir)) {
    return [];
  }
  const found = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      found.push(...trxFilesUnder(full));
    } else if (entry.name.endsWith(".trx")) {
      found.push(full);
    }
  }
  return found;
}

// Attributes are read individually; their order is not part of the trx format.
function failedTestsInTrx(xml) {
  const names = [];
  for (const element of xml.split("<UnitTestResult").slice(1)) {
    const head = element.slice(0, element.indexOf(">"));
    const outcome = /\boutcome="([^"]*)"/.exec(head);
    const name = /\btestName="([^"]*)"/.exec(head);
    if (outcome && name && outcome[1] === "Failed") {
      names.push(name[1]);
    }
  }
  return names;
}

// Preferred source: `--logger trx` is an explicit contract in the test workflow. null means
// there is no .trx for this job, which is normal - the upload is best effort.
function testsFromArtifact({ core }, shortJobName) {
  const name = artifactNameFor(shortJobName);
  if (!name) {
    return null;
  }
  const files = trxFilesUnder(path.join(RESULTS_DIR, name));
  if (files.length === 0) {
    return null;
  }
  const failed = new Set();
  for (const file of files) {
    for (const test of failedTestsInTrx(fs.readFileSync(file, "utf8"))) {
      failed.add(test);
    }
  }
  core.info(`${shortJobName}: ${failed.size} failed test(s) from ${files.length} .trx file(s)`);
  return [...failed];
}

// null distinguishes "could not read" from "read it, found nothing", which the caller counts.
async function testsFromLog({ github, context, core }, job) {
  try {
    const res = await github.rest.actions.downloadJobLogsForWorkflowRun({
      owner: context.repo.owner,
      repo: context.repo.repo,
      job_id: job.id,
    });
    const text = typeof res.data === "string" ? res.data : Buffer.from(res.data).toString("utf8");
    return [...new Set([...text.matchAll(FAILED_TEST_IN_LOG)].map(m => m[1]))];
  } catch (e) {
    core.warning(`could not read the log for job ${job.id} (${job.name}): ${e.message}`);
    return null;
  }
}

// A test name where one could be found, otherwise job and step so infrastructure failures are
// still recorded. Attempt 1 only: a re-run overwrites the visible conclusion, so attempt 1 is
// what keeps the failure rate honest.
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

    let tests = testsFromArtifact({ core }, shortName);
    let degraded = false;

    if (tests === null && steps.some(s => TEST_STEP.test(s))) {
      logsAttempted++;
      tests = await testsFromLog({ github, context, core }, job);
      if (tests === null) {
        logsFailed++;
        degraded = true;
        tests = [];
      }
    }

    if (tests && tests.length > 0) {
      for (const test of tests) {
        keys.set(test, { where: `\`${shortName}\`, step \`${steps.join("`, `")}\``, degraded: false });
      }
    } else {
      keys.set(`${shortName} - ${steps[0] || job.conclusion}`, { where: `\`${shortName}\``, degraded });
    }
  }

  // Naming the test is the point of this job, so losing every source must not look like success.
  if (logsAttempted > 0 && logsFailed === logsAttempted) {
    core.warning(
      `Could not read any of the ${logsAttempted} test job logs for run ${run_id}, and no .trx ` +
      `artifacts were available either. Check actions: read, and the 90-day retention.`);
  }

  return keys;
}

// Listing by label is strongly consistent; /search/issues is not, and would double-file. Match
// on marker or title so a human editing either does not cause a duplicate.
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
    const fromBody = /<!-- nightly-flake-key: (.*?) -->/.exec(issue.body || "");
    for (const key of [fromBody && fromBody[1], keyFromTitle(issue.title)]) {
      if (key && !byKey.has(key)) {
        byKey.set(key, issue);
      }
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

  for (const [key, { where, degraded }] of keys) {
    const note = degraded
      ? "\n\nThe failing test could not be identified: no `.trx` artifact was available and the " +
        "job log could not be read. Only the job and step are recorded."
      : "";
    const body = `Failed in ${where} during ${runUrl} (attempt 1).${note}`;
    const issue = existing.get(key);

    if (!issue) {
      const created = await github.rest.issues.create({
        owner, repo, labels: [LABEL],
        title: titleFor(key, 1),
        body:
          `${body}\n\n` +
          `Opened automatically because the nightly build failed. The name above comes from the ` +
          `run's test results, which expire after 90 days.\n\n` +
          `Further occurrences are added as comments and counted in the title. Closing this as ` +
          `"not planned" stops it being reopened; closing it as completed does not, so a ` +
          `recurrence after a fix still surfaces.\n\n` +
          marker(key),
      });
      core.info(`opened #${created.data.number} for ${key}`);
      continue;
    }

    // Makes re-dispatching for the same run a no-op.
    const comments = await github.paginate(github.rest.issues.listComments, {
      owner, repo, issue_number: issue.number, per_page: 100,
    });
    if (comments.some(c => c.body.includes(runUrl))) {
      core.info(`#${issue.number} already records ${runUrl}; skipping`);
      continue;
    }

    await github.rest.issues.createComment({ owner, repo, issue_number: issue.number, body });

    const update = {
      owner, repo, issue_number: issue.number,
      title: titleFor(key, countFromTitle(issue.title) + 1),
    };
    // Closed as "not planned" is a decision; closed as completed means a fix that did not hold.
    if (!(issue.state === "closed" && issue.state_reason === "not_planned")) {
      update.state = "open";
    }
    await github.rest.issues.update(update);
    core.info(`updated #${issue.number} for ${key}`);
  }
};
