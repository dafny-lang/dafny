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

const runMarker = run_id => `<!-- nightly-flake-run: ${run_id} -->`;

// The runs an issue already records. Read from the marker rather than from any run link in
// the text, so that someone linking a run while discussing the issue neither blocks that run
// from being recorded later nor inflates the count.
function runsRecordedIn(texts) {
  const pattern = /<!-- nightly-flake-run: (\d+) -->/g;
  const ids = texts.flatMap(text => [...(text || "").matchAll(pattern)]);
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
  const steps = job.steps || [];
  const failed = steps.filter(s => s.conclusion === "failure" || s.conclusion === "timed_out");
  if (failed.length > 0) {
    return failed.map(s => s.name);
  }
  // A job whose runner is lost leaves its current step in_progress and the rest pending, so
  // nothing is marked failed and the step it was on is the only name available.
  return steps.filter(s => s.status === "in_progress").map(s => s.name);
}

// `test (macos-15, 6)` -> os and shard.
const TEST_JOB = /^test \(([^,]+), *(\d+)\)/;

// `test (macos-15, 6)` -> `test (macos-15)`, so per-shard keys can be collapsed.
function platformOf(shortJobName) {
  const m = TEST_JOB.exec(shortJobName);
  return m ? `test (${m[1]})` : shortJobName;
}

// The artifact directories integration-tests-reusable.yml may hold a shard's .trx in. Empty
// for jobs that run no tests. A `test (` job that does not parse means the matrix gained a
// dimension and these names have to be rederived, so say so rather than only degrading.
function artifactDirsFor(shortJobName, core) {
  const m = TEST_JOB.exec(shortJobName);
  if (m) {
    // Both names are tried because #6517 moves the .trx out of the coverage artifact; this
    // way neither merge order leaves the .trx unfound.
    return ["integration-test-diagnostics", "integration-test-results"].map(
      prefix => `${prefix}-${m[1]}-${m[2]}`
    );
  }
  if (shortJobName.startsWith("test (")) {
    core.warning(`no results artifact derivable from the job name ${shortJobName}`);
  }
  return [];
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

// A .trx records when its own test run started.
function trxStartedAt(xml) {
  const m = /<Times\b[^>]*\bstart="([^"]*)"/.exec(xml);
  return m ? Date.parse(m[1]) : NaN;
}

// The only source of test names. `--logger trx` is a contract in the test workflow; xUnit's
// console output is not.
function failedTestsFor({ core }, shortJobName, attemptWindow) {
  const dirs = artifactDirsFor(shortJobName, core);
  let results = dirs
    .flatMap(dir => trxFilesUnder(path.join(RESULTS_DIR, dir)))
    .map(file => fs.readFileSync(file, "utf8"));

  // A re-run uploads a second artifact under the same name, so one shard's directory can
  // hold a .trx per attempt. Only then is the window needed to drop the later attempt's.
  if (results.length > 1) {
    const ofAttempt = results.filter(xml => {
      const started = trxStartedAt(xml);
      return !(started > attemptWindow.until) && !(started < attemptWindow.from);
    });
    if (ofAttempt.length > 0) {
      core.info(`${shortJobName}: ${results.length} .trx file(s), ${ofAttempt.length} from attempt 1`);
      results = ofAttempt;
    }
  }

  const failed = new Set();
  for (const xml of results) {
    for (const test of failedTestsInTrx(xml)) {
      failed.add(test);
    }
  }
  if (results.length > 0) {
    core.info(`${shortJobName}: ${failed.size} failed test(s) from ${results.length} .trx file(s)`);
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

  const attemptWindow = {
    from: Date.parse(attempt.run_started_at),
    until: Date.parse(attempt.updated_at),
  };

  const keys = new Map();

  for (const job of jobs) {
    if (!triaged.includes(job.conclusion)) {
      continue;
    }
    const steps = failingStepsOf(job);
    const shortName = job.name.split(" / ").pop();
    const tests = failedTestsFor({ core }, shortName, attemptWindow);

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
    } else if (job.conclusion === "cancelled") {
      // Runner capacity, not this shard: the shard is dropped so the arbitrary set of shards
      // that went unacquired on one night shares a key and accumulates.
      add(`${platformOf(shortName)} - cancelled`, false);
    } else {
      // A step before the tests fails the same way on every shard it hits, so it is keyed by
      // platform to accumulate; a failing test step keeps its shard, which is where its log
      // is, and is flagged so the issue says the tests named no failure.
      const duringTests = steps.some(s => TEST_STEP.test(s));
      const scope = duringTests ? shortName : platformOf(shortName);
      add(`${scope} - ${steps[0] || job.conclusion}`, duringTests);
    }
  }

  return keys;
}

// Which of two issues for one key is the live record. Closing as "not planned" is a decision
// to stop tracking, so another issue supersedes it; otherwise the older one holds the history
// and stays canonical, rather than the target moving to whatever was filed most recently.
function liveRecord(a, b) {
  const parked = i => i.state === "closed" && i.state_reason === "not_planned";
  if (parked(a) !== parked(b)) {
    return parked(a) ? b : a;
  }
  return a.number <= b.number ? a : b;
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
    // This endpoint lists pull requests as issues too.
    if (issue.pull_request) {
      continue;
    }
    const fromBody = /<!-- nightly-flake-key: (.*?) -->/.exec(issue.body || "");
    for (const key of [fromBody && fromBody[1], keyFromTitle(issue.title)]) {
      if (!key) {
        continue;
      }
      const seen = byKey.get(key);
      // Chosen explicitly rather than taking the first match, which would depend on the
      // order the API happens to list issues in.
      byKey.set(key, seen ? liveRecord(seen, issue) : issue);
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
    const body =
      `Failed in ${jobs.join(", ")} during ${runUrl} (attempt 1).${note}\n\n` + runMarker(run_id);
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
          `Recurrences are matched by searching the \`${LABEL}\` label, so removing it files a ` +
          `new issue next time instead of adding to this one. The title is free to change.\n\n` +
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
