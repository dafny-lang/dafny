// Turns a failed nightly run into one issue per failing test. See nightly-flake-triage.yml.

const fs = require("fs");
const path = require("path");

const LABEL = "nightly-flake";
const TITLE_PREFIX = "nightly flake: ";
// Must match the `path:` the download step in nightly-flake-triage.yml unpacks into. A
// mismatch finds no results rather than failing, and every issue falls back to job and step.
const RESULTS_DIR = "test-results";

// Distinguishes a job that failed before testing from one whose tests failed silently.
const TEST_STEP = /^Run integration tests/;

const marker = key => `<!-- nightly-flake-key: ${key} -->`;

// The runs an issue already records, read back out of the text it records them in. Matching
// whole ids rather than a substring keeps run 123 out of a recorded run 1234.
function runsRecordedIn(texts) {
  const ids = texts.flatMap(text => [...(text || "").matchAll(/\/actions\/runs\/(\d+)/g)]);
  return new Set(ids.map(match => match[1]));
}

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

// `test (macos-15, 6)` -> the artifact name integration-tests-reusable.yml uploads. Null for
// jobs that run no tests. A `test (` job that does not parse means the matrix gained a
// dimension and the artifact name has to be rederived, so say so rather than only degrading.
function artifactNameFor(shortJobName, core) {
  const m = /^test \(([^,]+), *(\d+)\)/.exec(shortJobName);
  if (m) {
    return `integration-test-results-${m[1]}-${m[2]}`;
  }
  if (shortJobName.startsWith("test (")) {
    core.warning(`no results artifact derivable from the job name ${shortJobName}`);
  }
  return null;
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

// vstest's non-passing outcomes. "NotExecuted" is a skipped test, not a failure.
const FAILED = new Set(["Failed", "Error", "Timeout", "Aborted"]);

// Attributes are read individually; their order is not part of the trx format.
function failedTestsInTrx(xml) {
  const names = [];
  for (const element of xml.split("<UnitTestResult").slice(1)) {
    const head = element.slice(0, element.indexOf(">"));
    const outcome = /\boutcome="([^"]*)"/.exec(head);
    const name = /\btestName="([^"]*)"/.exec(head);
    if (outcome && name && FAILED.has(outcome[1])) {
      names.push(name[1]);
    }
  }
  return names;
}

// The only source of test names. `--logger trx` is a contract in the test workflow; xUnit's
// console output is not.
function failedTestsFor({ core }, shortJobName) {
  const name = artifactNameFor(shortJobName, core);
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
  const owner = context.repo.owner;
  const repo = context.repo.repo;
  const { data: attempt } = await github.rest.actions.getWorkflowRunAttempt({
    owner, repo, run_id, attempt_number: 1,
  });
  const jobs = await github.paginate(github.rest.actions.listJobsForWorkflowRunAttempt, {
    owner, repo, run_id, attempt_number: 1, per_page: 100,
  });

  // A job-level timeout reports as `cancelled` with no failed step, so in a run that failed
  // anyway a cancelled job is the cause. In a run that was itself cancelled it is just that.
  const triaged = ["failure", "timed_out"];
  if (attempt.conclusion === "failure") {
    triaged.push("cancelled");
  }

  const keys = new Map();

  for (const job of jobs) {
    if (!triaged.includes(job.conclusion)) {
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
      ? "\n\nThe tests failed but left no results behind, so the failing test is not named " +
        "here; see the job log for that run."
      : "";
    const body = `Failed in ${jobs.join(", ")} during ${runUrl} (attempt 1).${note}`;
    const issue = existing.get(key);

    if (!issue) {
      const created = await github.rest.issues.create({
        owner, repo, labels: [LABEL],
        title: titleFor(key, 1),
        body:
          `${body}\n\n` +
          `Filed automatically: the name above comes from the run's test results, which are ` +
          `deleted after 90 days.\n\n` +
          `Further occurrences are added as comments and counted in the title. Closing this as ` +
          `"not planned" stops it being reopened; closing it as completed does not, so a ` +
          `recurrence after a fix still surfaces.\n\n` +
          marker(key),
      });
      core.info(`opened #${created.data.number} for ${key}`);
      continue;
    }

    const comments = await github.paginate(github.rest.issues.listComments, {
      owner, repo, issue_number: issue.number, per_page: 100,
    });
    // The opening run is recorded in the body, later ones in comments, so both are read.
    const recorded = runsRecordedIn([issue.body, ...comments.map(c => c.body)]);
    // Makes re-dispatching for the same run a no-op.
    if (recorded.has(String(run_id))) {
      core.info(`#${issue.number} already records ${runUrl}; skipping`);
      continue;
    }

    await github.rest.issues.createComment({ owner, repo, issue_number: issue.number, body });

    const update = {
      owner, repo, issue_number: issue.number,
      // Counted from the runs recorded, not from a title anyone may rename.
      title: titleFor(key, recorded.size + 1),
    };
    // Closed as "not planned" is a decision; closed as completed means a fix that did not hold.
    if (!(issue.state === "closed" && issue.state_reason === "not_planned")) {
      update.state = "open";
    }
    await github.rest.issues.update(update);
    core.info(`updated #${issue.number} for ${key}`);
  }
};
