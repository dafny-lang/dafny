# Preparing a new Dafny release

## Making a new Github release

0. Check that there are no open issues with the `release-blocker` label:
   https://github.com/dafny-lang/dafny/issues?q=is%3Aopen+is%3Aissue+label%3Arelease-blocker

1. In an up-to-date repository, with the `master` branch checked out and
   up-to-date (e.g., after `git pull upstream`), checkout a new branch
   from `master` (e.g., `git checkout -b branchname master`) change to
   the root directory of the repository (i.e., `dafny`, which contains
   `Source`, `Binaries`, etc.)

2. Select a version number (descriptor) `$VER` (e.g., "3.0.0" or
   "3.0.0-alpha") and select an internal version number (e.g.,
   "3.0.0.30203"). The major.minor.patch numbers may already have been
   incremented since the last release, so they do not necessarily need
   to be updated, but you may want to increment them further,
   use judgement. The last section is in "ymmdd" format, where "y" is
   the number of years since 2018 and "mmdd" the month and day portions
   of the release date (e.g., a release on January 12th, 2022 would be
   x.y.z.40112). Edit the internal version number in the following
   places:

   * `Source/version.cs`

   * `Source/DafnyDriver/DafnyDriver.csproj`

   * `Source/Dafny/DafnyPipeline.csproj`

   Put the public version number in place of the "Upcoming" header in
   `RELEASE_NOTES.md`, and add a new "Upcoming" header above it.

   Push and cut a PR, get it approved, and squash and merge those
   changes to the `master` branch.

3. Kick off the deep test suite by navigating to
   https://github.com/dafny-lang/dafny/actions/workflows/deep-tests.yml,
   clicking the "Run workflow" dropdown, ensuring `master` is selected,
   and clicking the "Run workflow" button. The automation for releasing
   below will check for a run of this workflow on the exact commit
   to release.

4. Create a fresh clone of the repo locally, making sure the latest commit
   is the squashed commit you just merged and tested, and push the tag for this release.

   ```
   git clone git@github.com:dafny-lang/dafny.git dafny-for-tagging
   cd dafny-for-tagging
   git tag v<$VER>
   git push origin v<$VER>
   ```

5. A GitHub action will automatically run in reaction to the tag being pushed,
   which will build the artifacts and reference manual and then create a draft
   GitHub release. You can find and watch the progress of this workflow at
   https://github.com/dafny-lang/dafny/actions.

6. Once the action completes, you should find the draft release at
   https://github.com/dafny-lang/dafny/releases. Edit the release body
   to add in the release notes from `RELEASE_NOTES.md`.
   Also check the box to create a new discussion based on
   the release, if this is not a pre-release.

7. Push the "Publish" button. This will trigger yet another workflow
   that will download the published artifacts and run a smoke test
   on multiple platforms. Again you can watch for this workflow at
   https://github.com/dafny-lang/dafny/actions.

8. Manually upload packages to NuGet, from the fresh checkout of the
   repository used for tagging.

   ```
   dotnet build Source/Dafny.sln
   dotnet pack --no-build dafny/Source/Dafny.sln
   dotnet nuget push --skip-duplicate "Binaries/Dafny*.nupkg" -k $A_VALID_API_KEY -s https://api.nuget.org/v3/index.json
   ```

9. Manually trigger the "Test NuGet Tool Installation" workflow on the
   `master` branch (following the same process as for step 3).

10. If preparing a pre-release, stop here, as
    the following steps declare the release as the latest version, which
    is not the intention.

11. If something goes wrong, delete the tag and release in GitHub, fix the
    problem and try again.

12. Update the Homebrew formula for Dafny (see below).
    Note that it is fine to leave this for the next day,
    and other members of the community may update the formula
    in the meantime anyway.

13. Announce the new release to the world.

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

## Updating and releasing a new version of VSCode plugin

1. Build ide-vscode locally from https://github.com/dafny-lang/ide-vscode .

2. Prepare the repository:

       git checkout master
       git pull origin
       git checkout -b <some new branch name>

3. Add the new Dafny version number to the `dafny.preferredVersion` list in the `package.json` file.

4. Update the value of the constant `LatestVersion` in the file `src/constants.ts` to the new version number.

5. Before releasing a new version of the VSCode plugin, make sure to add to the release notes in `CHANGELOG.md`

6. Follow the release process detailed in the plugin's repository:

   <https://github.com/dafny-lang/ide-vscode/blob/master/CONTRIBUTING.md>
