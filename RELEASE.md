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
   "3.0.0.30203"). The last section is in "ymmdd" format, where "y" is
   the number of years since 2018 and "mmdd" the month and day portions
   of the release date (e.g., a release on January 12th, 2022 would be
   x.y.z.40112). Edit the internal version number in
   `Source/version.cs`, replace the "Upcoming" header in `RELEASE_NOTES.md`
   with the the public version number, and add a new "Upcoming" header above it.
   Push and cut a PR, get it approved,
   and squash and merge those changes to the `master` branch.

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
   git push v<$VER>
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

8. If preparing a pre-release, stop here, as
   the following steps declare the release as the latest version, which
   is not the intention.

9. If something goes wrong, delete the tag and release in GitHub, fix the
   problem and try again.

10. Update the Homebrew formula for Dafny (see below).
   Note that it is fine to leave this for the next day,
   and other members of the community may update the formula
   in the meantime anyway.

11. Announce the new release to the world.

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

1. Update brew: `brew update`

2. Find the formula: `cd $(brew --repo)/Library/Taps/homebrew/homebrew-core/Formula`

3. Prepare the repository:

        git checkout master
        git pull origin
        git checkout -b <some new branch name>

   The branch name is needed in various places below

4. Edit the formula (e.g., `vi dafny.rb`). For a normal release change,
   all that is needed is to change the name of the archive file for the
   release and its SHA.

   a) Change the line near the top of the file that looks like

          url "https://github.com/dafny-lang/dafny/archive/v2.3.0.tar.gz"

      to hold the actual release number (this is the url for the source
      asset; you can see the actual name on the Releases page for the
      latest build).
   b) Save the file
   c) Run `brew reinstall dafny`.
   d) The command will complain that the SHA does not match. Copy the
      correct SHA, reopen the file and paste the new SHA into the `sha`
      line after the `url` line.
   e) Bump up the revision number (by one) on the succeeding line.
   f) Save the file
   g) Check that you have not introduced any syntax errors by running
      `brew reinstall dafny` again. If you totally mess up the file,
      you can do `git checkout dafny.rb`.

5. Create a pull request following the instructions here:

    <https://docs.brew.sh/How-To-Open-a-Homebrew-Pull-Request>

6. Expect comments from the reviewers. If changes are needed, do 4-6
   again. Eventually the reviewers will accept and merge the PR.

7. Then bring your Homebrew installation back to normal:

        git checkout master
        git pull origin master

8. Test the installation by running

        brew reinstall dafny

   and then execute `dafny` on a sample file to see if it has the
   correct version number. Even better is to try this step on a
   different machine than the one on which the `dafny.rb` file was edited

9. If everything works you can, at your leisure do

        git branch -d <the branch name>
