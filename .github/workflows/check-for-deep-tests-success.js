module.exports = ({github, context, core}) => {
  // This API doesn't support filtering by SHA, so we just
  // fetch the first page and scan manually.
  // That means if the run is fairly old it may be missed,
  // but that should be rare.
  const result = await github.rest.actions.listWorkflowRuns({
    owner: context.repo.owner,
    repo: context.repo.repo,
    workflow_id: 'deep-tests.yml',

  })
  // These are ordered by creation time, so decide based on the first
  // run for this SHA we see.
  console.log(result)
  for (const run of result.data.workflow_runs) {
    console.log(run)
    if (run.sha == context.sha) {
      if (run.conclusion != "success") {
        core.setFailed(`Last run of deep tests on $context.sha did not succeed!`)
      } else {
        // The SHA is fully-tested, exit with success
        return
      }
    }
  }
  core.setFailed(`No run of deep tests found for $context.sha!`)
}
