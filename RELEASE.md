# Preparing a new Dafny release

## Making a new Github release

0. Write release notes about changes since the last release in
   `RELEASE_NOTES.md`.

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
   `Source/version.cs`. Push and merge that change to the `master`
   branch.

3. Run `Scripts/package.py $VER` (on a Linux or macOS system).
   Warnings about missing fonts can be ignored. Note: This step requires
   that you have installed pandoc, see:

   <https://github.com/dafny-lang/dafny/wiki/INSTALL#building-the-reference-manual>

4. Run `Scripts/publish-release.sh $VER` to create the GitHub release
   and upload files to it. You will need to have a GitHub Personal
   Authorization token stored in `~/github.token`. Also, this step
   requires the `jq` utility, which you can install with `brew install
   jq` on macOS (see <https://stedolan.github.io/jq/download/>). Note:
   Each upload of this step can take a couple of minutes, so be patient.

5. On the GitHub releases page, edit the new release to add in the
   release notes. Also check the box to create a new discussion based on
   the release.

6. Push the "Publish" button. If preparing a pre-release, stop here, as
   the following steps declare the release as the latest version, which
   is not the intention.

7. Edit `.github/workflows/release-downloads.yml` to set the for the
   `ver` variable to the value of `$VER`. Then commit this file along
   with any of those modified by the previous scripts, which may include

        .github/workflows/release-downloads,yml
        docs/DafnyRef/DafnyRef.pdf
        docs/DafnyRef/Options.txt

   Push the commit with `git push` and create a PR. The creation of a PR
   will cause the CI tests to be run, which includes downloading the
   most recent release (this one, once it is published) and running some
   quick tests.

8. If something goes wrong, delete the release in GitHub, fix the
   problem and try again.

9. Update the Homebrew formula for Dafny (see below).

10. Announce the new release to the world.

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
