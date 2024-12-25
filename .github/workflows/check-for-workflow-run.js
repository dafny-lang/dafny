// Check for a successful previous run of a workflow.
// This could make a decent reusable action itself.
module.exports = async ({github, context, core, workflow_id, sha, ...config}) => {
  // This API doesn't support filtering by SHA, so we just
  // fetch the first page and scan manually.
  // That means if the run is fairly old it may be missed,
  // but that should be rare.
  const result = await github.rest.actions.listWorkflowRuns({
    owner: context.repo.owner,
    repo: context.repo.repo,
    workflow_id,
    ...config
  })
  // These are ordered by creation time, so decide based on the first
  // run for this SHA we see.
  const runFilterDesc = sha ? `${workflow_id} on ${sha}` : workflow_id
  const workflow_runs =  result.data.workflow_runs.filter(run => !sha || run.head_sha === sha)
  const workflow_runs_completed = workflow_runs.filter(run => run.status === "completed")
  // The status property can be one of: “queued”, “in_progress”, or “completed”.
  const workflow_runs_in_progress = workflow_runs.filter(run => run.status !== "completed")
  for (const run of workflow_runs_completed) {
    // The conclusion property can be one of:
    // “success”, “failure”, “neutral”, “cancelled”, “skipped”, “timed_out”, or “action_required”.
    if (run.conclusion === "success") {
      // The SHA is fully tested, exit with success
      console.log(`Last run of ${runFilterDesc} succeeded: ${run.html_url}`)
      return
    } else if (run.conclusion === "failure" || run.conclusion === "timed_out") {
      const extraMessage = workflow_runs_in_progress.length > 0 ?
        `\nA run of ${runFilterDesc} is currently ${workflow_runs_in_progress[0].status}:`+
        ` ${workflow_runs_in_progress[0].html_url}, just re-run this test once it is finished.` :
        `\nAt the time of checking, no fix was underway.\n`+
        `- Please first check https://github.com/dafny-lang/dafny/actions/workflows/nightly-build.yml . `+
        `If you see any queued or in progress run on ${runFilterDesc}, just re-run this test once it is finished.`+
        `- If not, and you are a Dafny developer, please fix the issue by creating a PR with the label [run-deep-tests], have it reviewed and merged, ` +
        `and then trigger the workflow on ${runFilterDesc} with the URL https://github.com/dafny-lang/dafny/actions/workflows/nightly-build.yml .\n`+
        `With such a label, you can merge a PR even if tests are not successful, but make sure the deeps one are!\n`+
        `If you do not have any clue on how to fix it, `+
        `at worst you can revert all PRs from the last successful run and indicate the authors they need to re-file`+
        ` their PRs and add the label [run-deep-tests] to their PRs`;
      core.setFailed(`Last run of ${runFilterDesc} did not succeed: ${run.html_url}${extraMessage}`)
      return
    }
  }
  core.setFailed(`No completed runs of ${runFilterDesc} found!`)
}
