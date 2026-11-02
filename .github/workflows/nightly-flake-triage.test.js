const test = require("node:test");
const assert = require("node:assert");
const fs = require("fs");
const os = require("os");
const path = require("path");

const triage = require("./nightly-flake-triage.js");

const RUN = 32493733431;
const runUrl = id => `https://github.com/dafny-lang/dafny/actions/runs/${id}`;
const RUN_URL = runUrl(RUN);
const WINDOWS_STEP = "Run integration tests (Windows)";
const MACOS_STEP = "Run integration tests (non-Windows)";

// Element order, attribute order and the stray outcome="..." on <RunInfo>/<ResultSummary> are
// copied from a real integration-test-results artifact, so the parser is held to that shape.
function trx(results) {
  const rows = results.map(
    ([testName, outcome]) =>
      `<UnitTestResult executionId="7283165d" testId="dc633613" testName="${testName}" ` +
      `computerName="runnervm5yrfj" duration="00:00:08.68" startTime="2026-08-21T15:02:16Z" ` +
      `endTime="2026-08-21T15:02:16Z" testType="13cdc9d9" outcome="${outcome}" ` +
      `testListId="8c84fa94" relativeResultsDirectory="7283165d">` +
      `<Output><ErrorInfo><Message>boom</Message></ErrorInfo></Output></UnitTestResult>`
  );
  return (
    `<?xml version="1.0" encoding="UTF-8"?>\n<TestRun id="r">` +
    `<RunInfos><RunInfo computerName="runnervm5yrfj" outcome="Error"><Text>w</Text></RunInfo></RunInfos>` +
    `<Results>${rows.join("")}</Results>` +
    `<ResultSummary outcome="Failed"><Counters total="${results.length}" /></ResultSummary></TestRun>`
  );
}

// download-artifact unpacks each artifact under <path>/<artifact name>/, keeping the uploaded
// tree: IntegrationTests/TestResults/*.trx next to a coverage report in a GUID directory.
function workspace(artifacts) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "flake-triage-"));
  for (const [name, results] of Object.entries(artifacts)) {
    const results_dir = path.join(dir, "test-results", name, "IntegrationTests", "TestResults");
    fs.mkdirSync(path.join(results_dir, "8c37de43-d946"), { recursive: true });
    fs.writeFileSync(path.join(results_dir, "run.trx"), trx(results));
    fs.writeFileSync(path.join(results_dir, "8c37de43-d946", "coverage.cobertura.xml"), "<coverage/>");
  }
  return dir;
}

function job(name, conclusion, steps = []) {
  return {
    name: `nightly-build-for-master / deep-integration-tests / ${name}`,
    conclusion,
    steps: steps.map(([n, c]) => ({ name: n, conclusion: c })),
  };
}

// Records what the script asked GitHub to write, and serves the reads from fixtures.
function run({ jobs = [], issues = [], comments = {}, artifacts = {}, run_id = RUN } = {}) {
  const wrote = { created: [], commented: [], updated: [], warnings: [] };
  const github = {
    rest: {
      actions: { listJobsForWorkflowRunAttempt: "jobs" },
      issues: {
        listForRepo: "issues",
        listComments: "comments",
        create: async a => (wrote.created.push(a), { data: { number: 900 } }),
        createComment: async a => void wrote.commented.push(a),
        update: async a => void wrote.updated.push(a),
      },
    },
    paginate: async (route, params) => {
      if (route === "jobs") {
        assert.strictEqual(params.attempt_number, 1);
        return jobs;
      }
      if (route === "issues") {
        assert.strictEqual(params.state, "all");
        return issues;
      }
      return comments[params.issue_number] || [];
    },
  };
  const core = { info() {}, warning: m => wrote.warnings.push(m) };
  process.chdir(workspace(artifacts));
  return triage({ github, context: { repo: { owner: "dafny-lang", repo: "dafny" } }, core }, run_id).then(
    () => wrote
  );
}

// As the script leaves it: the run that opened the issue is recorded in the body.
const OPENING_RUN = 31503545170;
const issue = extra => ({
  number: 10,
  title: "nightly flake: logger/JsonLogger.dfy",
  state: "open",
  body:
    `Failed in \`test (macos-15, 6)\` during ${runUrl(OPENING_RUN)} (attempt 1).\n\n` +
    "<!-- nightly-flake-key: logger/JsonLogger.dfy -->",
  ...extra,
});

const windowsShard6 = [job("test (windows-2022, 6)", "failure", [[WINDOWS_STEP, "failure"]])];
const jsonLoggerFailed = {
  "integration-test-results-windows-2022-6": [
    ["dafny4/gcd.dfy", "Passed"],
    ["logger/JsonLogger.dfy", "Failed"],
  ],
};

test("names the failing test, and the job it failed in, from the .trx", async () => {
  const wrote = await run({ jobs: windowsShard6, artifacts: jsonLoggerFailed });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    ["nightly flake: logger/JsonLogger.dfy"]
  );
  assert.match(wrote.created[0].body, /`test \(windows-2022, 6\)` during .*\/runs\/32493733431/);
  assert.deepStrictEqual(wrote.created[0].labels, ["nightly-flake"]);
});

test("the failing step is not named, because a later step may be the one that failed", async () => {
  const jobs = [job("test (windows-2022, 6)", "failure", [["Upload artifact", "failure"]])];
  const wrote = await run({ jobs, artifacts: jsonLoggerFailed });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    ["nightly flake: logger/JsonLogger.dfy"]
  );
});

test("a test that errored or timed out is a failing test", async () => {
  for (const outcome of ["Error", "Timeout", "Aborted"]) {
    const artifacts = { "integration-test-results-windows-2022-6": [["comp/slow.dfy", outcome]] };
    const wrote = await run({ jobs: windowsShard6, artifacts });
    assert.deepStrictEqual(
      wrote.created.map(c => c.title),
      ["nightly flake: comp/slow.dfy"],
      outcome
    );
  }
});

test("a skipped test is not a failing test", async () => {
  const artifacts = { "integration-test-results-windows-2022-6": [["comp/rust/x.dfy", "NotExecuted"]] };
  const wrote = await run({ jobs: windowsShard6, artifacts });
  assert.match(wrote.created[0].title, /Run integration tests/);
});

test("one issue, naming both jobs, when a test fails on two platforms", async () => {
  const wrote = await run({
    jobs: [...windowsShard6, job("test (macos-15, 6)", "failure", [[MACOS_STEP, "failure"]])],
    artifacts: {
      ...jsonLoggerFailed,
      "integration-test-results-macos-15-6": [["logger/JsonLogger.dfy", "Failed"]],
    },
  });
  assert.strictEqual(wrote.created.length, 1);
  assert.match(wrote.created[0].body, /`test \(windows-2022, 6\)`, `test \(macos-15, 6\)`/);
});

test("a test step that failed leaving no results points at the job log", async () => {
  const wrote = await run({ jobs: windowsShard6 });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    [`nightly flake: test (windows-2022, 6) - ${WINDOWS_STEP}`]
  );
  assert.match(wrote.created[0].body, /left no results behind/);
});

test("the fallback key names the earliest failing step, not a later consequence", async () => {
  const jobs = [
    job("test (macos-15, 2)", "failure", [[MACOS_STEP, "failure"], ["Upload artifact", "failure"]]),
  ];
  const wrote = await run({ jobs });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    [`nightly flake: test (macos-15, 2) - ${MACOS_STEP}`]
  );
});

test("a job that timed out is triaged like one that failed", async () => {
  const jobs = [job("test (windows-2022, 6)", "timed_out", [[WINDOWS_STEP, "timed_out"]])];
  const wrote = await run({ jobs, artifacts: jsonLoggerFailed });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    ["nightly flake: logger/JsonLogger.dfy"]
  );
});

test("a job that failed before running tests names its step and claims nothing more", async () => {
  const wrote = await run({ jobs: [job("publish-release", "failure", [["Build", "failure"]])] });
  assert.deepStrictEqual(
    wrote.created.map(c => c.title),
    ["nightly flake: publish-release - Build"]
  );
  assert.doesNotMatch(wrote.created[0].body, /left no results behind/);
  assert.deepStrictEqual(wrote.warnings, [], "a job running no tests is not a staleness signal");
});

test("a test job whose name stopped parsing warns instead of quietly degrading", async () => {
  // A third matrix dimension would name jobs `test (os, shard, runtime)`.
  const jobs = [job("test (windows-2022, 6, newest)", "failure", [[WINDOWS_STEP, "failure"]])];
  const wrote = await run({ jobs, artifacts: jsonLoggerFailed });
  assert.match(wrote.warnings.join(), /test \(windows-2022, 6, newest\)/);
  assert.match(wrote.created[0].title, /Run integration tests/);
});

test("a second run comments on the open issue and counts the occurrence", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue()],
    comments: { 10: [] },
  });
  assert.strictEqual(wrote.created.length, 0);
  assert.strictEqual(wrote.commented.length, 1);
  assert.strictEqual(wrote.updated[0].title, "nightly flake: logger/JsonLogger.dfy (2x)");
});

test("the count comes from the runs recorded, not from a title anyone may rename", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ title: "nightly flake: logger/JsonLogger.dfy (97x)" })],
    comments: { 10: [{ body: `during ${runUrl(30642186569)} (attempt 1).` }] },
  });
  assert.strictEqual(wrote.updated[0].title, "nightly flake: logger/JsonLogger.dfy (3x)");
});

test("a run recorded twice is counted once", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue()],
    comments: { 10: [{ body: `also seen in ${runUrl(OPENING_RUN)}` }] },
  });
  assert.strictEqual(wrote.updated[0].title, "nightly flake: logger/JsonLogger.dfy (2x)");
});

test("re-dispatching the run that opened the issue changes nothing", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ body: `Failed in \`x\` during ${RUN_URL} (attempt 1).\n<!-- nightly-flake-key: logger/JsonLogger.dfy -->` })],
    comments: { 10: [] },
  });
  assert.deepStrictEqual(wrote, { created: [], commented: [], updated: [], warnings: [] });
});

test("re-dispatching a run already commented on changes nothing", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue()],
    comments: { 10: [{ body: `during ${RUN_URL} (attempt 1).` }] },
  });
  assert.deepStrictEqual(wrote, { created: [], commented: [], updated: [], warnings: [] });
});

test("a run whose id merely starts with a recorded one is a new occurrence", async () => {
  const wrote = await run({
    run_id: 3249373343, // a prefix of 32493733431
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue()],
    comments: { 10: [{ body: `during ${RUN_URL} (attempt 1).` }] },
  });
  assert.strictEqual(wrote.commented.length, 1);
});

test("an issue renamed past recognition is still found by its marker", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ title: "JsonLogger is flaky on Windows" })],
    comments: { 10: [] },
  });
  assert.strictEqual(wrote.created.length, 0);
  assert.strictEqual(wrote.commented.length, 1);
});

test("an issue whose marker was edited away is still found by its title", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ body: "someone rewrote this" })],
    comments: { 10: [] },
  });
  assert.strictEqual(wrote.created.length, 0);
  assert.strictEqual(wrote.commented.length, 1);
});

test("closed as completed reopens, because the fix did not hold", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ state: "closed", state_reason: "completed" })],
    comments: { 10: [] },
  });
  assert.strictEqual(wrote.updated[0].state, "open");
});

test("closed as not planned stays closed, but the occurrence is still recorded", async () => {
  const wrote = await run({
    jobs: windowsShard6,
    artifacts: jsonLoggerFailed,
    issues: [issue({ state: "closed", state_reason: "not_planned" })],
    comments: { 10: [] },
  });
  assert.strictEqual(wrote.commented.length, 1);
  assert.strictEqual(wrote.updated[0].state, undefined);
});

test("nothing is filed for jobs that passed or were cancelled", async () => {
  const wrote = await run({
    jobs: [
      job("test (windows-2022, 6)", "success", [[WINDOWS_STEP, "success"]]),
      job("test (macos-15, 6)", "cancelled", [[MACOS_STEP, "cancelled"]]),
      job("publish-release", "skipped"),
    ],
    artifacts: jsonLoggerFailed,
  });
  assert.deepStrictEqual(wrote, { created: [], commented: [], updated: [], warnings: [] });
});

test("a run id that is not a positive integer is refused before any API call", async () => {
  for (const bad of ["12; rm -rf /", NaN, 0, -1, 1.5]) {
    await assert.rejects(() => run({ run_id: bad }), /not a workflow run id/, String(bad));
  }
});
