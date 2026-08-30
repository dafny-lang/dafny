// Turn a failed nightly run into a deduplicated issue naming the test that failed.
//
// Failing job and step names survive in the API for about a year, but the failing *test* name
// only exists in the run's own output, which expires after 90 days. Recovering it later is
// disproportionately hard, so record it while it is still there.

const fs = require("fs");
const path = require("path");

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";

// Where the workflow put the run's test-result artifacts, if it managed to download any.
const RESULTS_DIR = "test-results";

// Fallback only, for when no .trx is available. This parses xUnit's console output, which is a
// formatting detail of a third-party logger rather than a contract: it depends on `[FAIL]` and
// on `--logger "console;verbosity=normal"` staying put. The .trx path below is preferred for
// exactly that reason. Extensions match LitTests.cs's FileData includes.
const FAILED_TEST_IN_LOG = /([A-Za-z0-9_./-]+\.(?:dfy|transcript)) \[FAIL\]/g;

// Only these steps run tests, so only these are worth fetching a log for. With .trx as the
// primary source this is just an optimisation - a stale entry costs a wasted lookup, not a
// misclassification.
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

// `test (macos-14, 6)` -> `integration-test-results-macos-14-6`, matching the artifact name
// that integration-tests-reusable.yml uploads.
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

// Failed test names from a .trx. Attributes are read individually rather than in a fixed order,
// since their order is not part of the format.
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

// The preferred source: `--logger trx` is an explicit contract in the test workflow, the format
// is structured, and it names tests of any extension. Returns null when there is no .trx for
// this job, which is not an error: the upload is best-effort and may have been skipped.
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

// Fallback source. Returns null if the log could not be read at all, which the caller counts so
// that a systemic failure is reported rather than silently degrading.
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

// One key per thing worth tracking: a test name where one could be found, otherwise job and
// step so that infrastructure failures are still recorded.
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
      keys.set(`${shortName} - ${steps[0] || job.conclusion}`, {
        where: `\`${shortName}\``,
        degraded,
      });
    }
  }

  if (logsAttempted > 0 && logsFailed === logsAttempted) {
    core.warning(
      `Could not read any of the ${logsAttempted} test job logs for run ${run_id}, and no .trx ` +
      `artifacts were available either. Test names are missing from the issues below. Check that ` +
      `this workflow still has actions: read, and that the run is inside its 90-day retention.`);
  }

  return keys;
}

// Listing by label is strongly consistent; the search API is not, and would double-file when two
// runs fail close together. Match on the body marker or the title, so that a human editing
// either one does not cause a duplicate.
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
    // Say so in the issue, not only in a log nobody reads, when the test name is missing.
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
          `Opened automatically because the nightly build failed. The name above is taken from the ` +
          `run's test results, which expire after 90 days, so it is recorded here while it still ` +
          `exists.\n\n` +
          `Further occurrences are added as comments and counted in the title. Closing this as ` +
          `"not planned" stops it being reopened; closing it as completed does not, so a ` +
          `recurrence after a fix still surfaces.\n\n` +
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

    const update = {
      owner, repo, issue_number: issue.number,
      title: titleFor(key, countFromTitle(issue.title) + 1),
    };
    // Reopen so the occurrence is visible - unless a human closed it as "not planned", which is
    // GitHub's own way of saying they have decided against it. Closed as completed is different:
    // a recurrence means the fix did not hold, so that should reopen.
    if (!(issue.state === "closed" && issue.state_reason === "not_planned")) {
      update.state = "open";
    }
    await github.rest.issues.update(update);
    core.info(`updated #${issue.number} for ${key}`);
  }
};
