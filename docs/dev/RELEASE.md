# Preparing a new Dafny release

## Making a new Github release

1. Ensure that you are in a repository that:
   * is clean and up-to-date with no uncommitted changes,
   * was cloned with SSH so that you can push to it, and
   * has the intended branch checked out (usually `master`,
     but may be another mainline branch such as `main-3.x`).

1. Get the version number from `Source/Directory.Build.props`.
   It should look like "3.0.0" (or "3.0.0-alpha"). It's referred to as
   `$VER` in the following. 
   The `major`.`minor`.`patch` numbers should already have been
   incremented since the last release, so they do not need
   to be updated. However, you may want to increment the minor
   or major version depending the types of changes that are in the release.

1. Run `Scripts/prepare_release.py $VER prepare --source-branch <this
   branch>` (`--source-branch` is optional and defaults to 'master')
   from the root of the repository. The script will check that the
   repository is in a good state, create and check out a new release
   branch, update `Source/Directory.Build.props` and `RELEASE_NOTES.md`.

1. You don't need to update the version number as the patch number
   is already set for the next release. However, if you wish to change the
   minor or major version, see [VERSIONBUMP.md](VERSIONBUMP.md)

1. Run `./Scripts/prepare_release.py $VER
   release` from the root of the repository. The script will tag the
   current commit and push it. A
   GitHub action will automatically run in reaction to the tag being
   pushed, which will run the deep integration test suite,
   build the artifacts and reference manual,
   publish artifacts to nuget.org, and then
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

1. We are going to merge the release branch into master to take into account
   any fix that was implemented there, and also update the version number.
   With the release branch checked out, run `./Scripts/prepare_release.py
   $NEXT_VER set-next version` to set the version number for the next
   release, where `$NEXT_VER` is `$VER` with the patch incremented.
   Then follow the instructions [VERSIONBUMP.md](VERSIONBUMP.md) to keep Dafny
   up-to-date with the new version number.
   Create a new pull request for this change, have it approved and merged.

1. Clone <https://github.com/dafny-lang/ide-vscode> and run `publish_process.js`
   to create a new release of the VSCode plugin.

1. Make a documentation snapshot
   1. Run the (bash) command `dafny/docs/make-snapshot -b <branch> x.y.z`
      where `x.y.z` is the new version number
      and <branch> is the branch used (defaults to 'master')
   1. The script creates new PRs in dafny-lang/dafny
      and dafny-lang/dafny-lang.github.io.
      Approve and merge these PRs.

1. Add the new version to the list of versions to be checked in the library repo,
   namely the list in the file libraries/.github/workflows/tests.yml.

1. Update the Homebrew formula for Dafny (see below).
    Note that it is fine to leave this for the next day,
    and other members of the community may update the formula
    in the meantime anyway.

1. Once the Homebrew formula is merged, test that it works correctly by
   going to <https://github.com/dafny-lang/dafny/actions> and manually
   running the "Test Brew release on Mac" workflow. It doesn't matter
   what branch you run it on because it won't actually check out the
   code. It will just install Dafny from Homebrew and run it on some
   examples.

If something goes wrong with the `prepare` step:

- Remove the release commit (`git reset --hard HEAD~1`)
- Commit fixes
- Re-run the `prepare` step; the script will recognize the `release-` branch and will not recreate it.

If something goes wrong with the `release` step:
- Delete the local tag: `git tag -d vA.B.C`
- Delete the remote tag: `git push --delete origin vA.B.C`
- Return to the `prepare` step.

1. Announce the new release to the world.

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
