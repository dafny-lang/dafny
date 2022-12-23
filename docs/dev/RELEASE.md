# Preparing a new Dafny release

## Making a new Github release

1. Ensure that you are in a repository that:
   * is clean and up-to-date with no uncommitted changes,
   * was cloned with SSH so that you can push to it, and
   * has the `master` branch checked out.

1. Select a version number `$VER` (e.g., "3.0.0" or "3.0.0-alpha"). 
   The `major`.`minor`.`patch` numbers may already have been
   incremented since the last release, so they do not necessarily need
   to be updated. However, you may want to increment them further
   depending the types of changes that are in the release.
1. Run `Scripts/prepare_release.py $VER prepare` from the root of the
   repository. The script will check that the repository is in a good
   state, create and check out a new release branch, update
   `Source/Directory.Build.props` and `RELEASE_NOTES.md`, prepare a release commit,
   and push it.

1. Kick off the deep test suite by navigating to
   <https://github.com/dafny-lang/dafny/actions/workflows/deep-tests.yml>,
   clicking the "Run workflow" dropdown, selecting the newly created branch, and
   clicking the "Run workflow" button. The automation for releasing below will
   check for a run of this workflow on the exact commit to release.  (TODO:
   Run this automatically as part of the prepare-release script.)

1. Once the the tests complete, run `Scripts/prepare_release.py $VER
   release` from the root of the repository. The script will tag the
   current commit and push it. (TODO: Merge with the two steps above.) A
   GitHub action will automatically run in reaction to the tag being
   pushed, which will build the artifacts and reference manual and then
   create a draft GitHub release. You can find and watch the progress of
   this workflow at <https://github.com/dafny-lang/dafny/actions>.

1. Once the action completes, you should find the draft release at
   <https://github.com/dafny-lang/dafny/releases>. Edit the release body to add in
   the release notes from `RELEASE_NOTES.md`.  If this is not a pre-release,
   check the box to create a new discussion based on the release.

1. Push the "Publish" button. This will trigger yet another workflow
   that will download the published artifacts and run a smoke test
   on multiple platforms. Again you can watch for this workflow at
   <https://github.com/dafny-lang/dafny/actions>.

1. Create a pull request to merge the newly created branch into `master` (the
   script will give you a link to do so).  Get it approved and merged.

1. Clone <https://github.com/dafny-lang/ide-vscode> and run `publish_process.js`
   to create a new release of the VSCode plugin.

1. Update the Homebrew formula for Dafny (see below).
   Note that it is fine to leave this for the next day,
   and other members of the community may update the formula
   in the meantime anyway.

1. Announce the new release to the world!

If something goes wrong with the `prepare` step:

- Remove the release commit (`git reset --hard HEAD~1`)
- Commit fixes
- Re-run the `prepare` step; the script will recognize the `release-` branch and will not recreate it.

If something goes wrong with the `release` step:

- Delete the local tag: `git tag -d vA.B.C`
- Delete the remote tag: `git push --delete origin vA.B.C`
- Return to the `prepare` step.

## Updating Dafny on Homebrew

Homebrew (`brew`) is a package manager for macOS. The Dafny project
maintains a brew "formula" that allows easy installation of Dafny and
its dependencies on macOS.

These are the instructions for updating the formula, which must be done
each time a new release is issued.

These instructions are meant to be executed on a Mac, in a Terminal shell.
All the Homebrew formulas are held in a GitHub repo, so some familiarity
with git commands and concepts is helpful.

0. Install Homebrew if it is not already present on your machine.
   Running `which brew` will tell you if it is. See
   <https://docs.brew.sh/Installation> if not.

1. Create a GitHub personal access token (if you don't have one handy),
   and put it in an environment variable:

   ```
   export HOMEBREW_GITHUB_API_TOKEN=your_token_here
   ```

2. Create a pull request following the instructions here:

    <https://docs.brew.sh/How-To-Open-a-Homebrew-Pull-Request>

   These instructions currently involve the following command:

```
  brew bump-formula-pr \
    --url <source .tar.gz for the release> \
    --sha256 <sha256 of the source .tar.gz for the release>
```

3. Expect comments from the reviewers. If changes are needed, do 4-6
   again. Eventually the reviewers will accept and merge the PR.

4. Test the installation by running

        brew reinstall dafny

   and then execute `dafny /version` see if it has the correct version
   number. Even better is to try this step on a different machine than
   the one on which the `dafny.rb` file was edited
