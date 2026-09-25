// Record which test failed when the nightly build goes red, into one issue per test.
// The failing test's name only exists in the run's test results, which expire after 90 days.

const fs = require("fs");
const path = require("path");

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";
const RESULTS_DIR = "test-results";

// Distinguishes a job that failed before testing from one whose tests failed silently.
const TEST_STEP = /^Run integration tests/;

const marker = key => `<!-- nightly-flake-key: ${key} -->`;

function titleFor(key, count) {
  return `${TITLE_PREFIX}${key}` + (count > 1 ? ` (${count}x)` : "");
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

// The only source of test names. `--logger trx` is a contract in the test workflow; xUnit's
// console output is not.
function failedTestsFor({ core }, shortJobName) {
  const name = artifactNameFor(shortJobName);
  if (!name) {
    return [];
  }
  const files = trxFilesUnder(path.join(RESULTS_DIR, name));
  const failed = new Set();
  for (const file of files) {
    for (const test of failedTestsInTrx(fs.readFileSync(file, "utf8"))) {
      failed.add(test);
    }
  }
  if (files.length > 0) {
    core.info(`${shortJobName}: ${failed.size} failed test(s) from ${files.length} .trx file(s)`);
  }
  return [...failed];
}

// A test name where the results named one, otherwise job and step. Attempt 1 only: a re-run
// overwrites the visible conclusion, so attempt 1 is what keeps the failure rate honest.
async function keysForRun({ github, context, core }, run_id) {
  const jobs = await github.paginate(github.rest.actions.listJobsForWorkflowRunAttempt, {
    owner: context.repo.owner,
    repo: context.repo.repo,
    run_id,
    attempt_number: 1,
    per_page: 100,
  });

  const keys = new Map();

  for (const job of jobs) {
    if (job.conclusion !== "failure" && job.conclusion !== "timed_out") {
      continue;
    }
    const steps = failingStepsOf(job);
    const shortName = job.name.split(" / ").pop();
    const tests = failedTestsFor({ core }, shortName);

    // One test can fail in several jobs, so collect jobs per key rather than overwriting.
    const add = (key, unexplained) => {
      const entry = keys.get(key) || { jobs: [], unexplained: false };
      entry.jobs.push(`\`${shortName}\``);
      entry.unexplained = entry.unexplained || unexplained;
      keys.set(key, entry);
    };

    if (tests.length > 0) {
      // No step: the failing step may be a later one that did not cause the test failure.
      for (const test of tests) {
        add(test, false);
      }
    } else {
      // Flag a test step that failed without naming a test, so the reader checks the log.
      add(`${shortName} - ${steps[0] || job.conclusion}`, steps.some(s => TEST_STEP.test(s)));
    }
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

  for (const [key, { jobs, unexplained }] of keys) {
    const note = unexplained
      ? "\n\nThe tests failed but left no results behind, so the failing test is not named here. " +
        "The job log for that run will say which it was."
      : "";
    const body = `Failed in ${jobs.join(", ")} during ${runUrl} (attempt 1).${note}`;
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

    // From the comments, not the title, which anyone may rename: the body plus one per run.
    const occurrences = 2 + comments.filter(c => /\/actions\/runs\/\d+/.test(c.body)).length;
    const update = {
      owner, repo, issue_number: issue.number,
      title: titleFor(key, occurrences),
    };
    // Closed as "not planned" is a decision; closed as completed means a fix that did not hold.
    if (!(issue.state === "closed" && issue.state_reason === "not_planned")) {
      update.state = "open";
    }
    await github.rest.issues.update(update);
    core.info(`updated #${issue.number} for ${key}`);
  }
};
