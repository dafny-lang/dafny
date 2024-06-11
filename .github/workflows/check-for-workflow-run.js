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
  for (const run of result.data.workflow_runs) {
    if ((!sha || run.head_sha === sha)) {
      // The status property can be one of: “queued”, “in_progress”, or “completed”.
      if (run.status === "completed") {
        // The conclusion property can be one of:
        // “success”, “failure”, “neutral”, “cancelled”, “skipped”, “timed_out”, or “action_required”.
        if (run.conclusion === "success") {
          // The SHA is fully tested, exit with success
          console.log(`Last run of ${runFilterDesc} succeeded: ${run.html_url}`)
          return
        } else if (run.conclusion === "failure" || run.conclusion === "timed_out") {
          core.setFailed(`Last run of ${runFilterDesc} did not succeed: ${run.html_url}`)
          return
        }
      }
    }
  }
  core.setFailed(`No completed runs of ${runFilterDesc} found!`)
}
