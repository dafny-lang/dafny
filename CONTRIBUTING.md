# Guidelines for Contributing to Dafny

Thanks for contributing to Dafny!  Github is the right place to discuss feature requests, report issues with Dafny, or contact the Dafny developers.
Dafny is an Open Source project and welcomes contributions.

## Reporting issues

Before reporting an issue here, consider whether it would be better handled in one of the following places:

- [Stack Overflow](https://stackoverflow.com/questions/tagged/dafny), an online Q&A website, for help with writing and proving Dafny programs.
- [`dafny-lang/ide-vscode`](https://github.com/dafny-lang/ide-vscode), Dafny's VSCode plugin, for issues or feature requests specific to the plugin itself. Issues with the LSP should be reported to [`dafny-lang/dafny](https://github.com/dafny-lang/dafny/issues).
- [`boogie-org/boogie-friends`](https://github.com/boogie-org/boogie-friends/), Dafny's Emacs mode, for Emacs-specific problems.
- [`boogie-org/boogie`](https://github.com/boogie-org/boogie), Dafny's intermediate verification language, for questions and issues specific to Boogie.

Other issues can be reported to the [Dafny project](https://github.com/dafny-lang/dafny/issues).
Please include your Dafny version number, any relevant code, and expected results in the issue report.

## Contributing to the source code

Developers who would like to experiment with and perhaps modify Dafny source should note these resources:
- First, there are [resources to learn about Dafny as a user](https://dafny.org).
- And note the [community Code of Conduct](./CODE_OF_CONDUCT) expected of all participating in the project.
- The Dafny project is at [github](https://github.com/dafny-lang/dafny) with related [sibling repositories](https://github.com/dafny-lang).
- Instructions for compiling Dafny are on the [wiki](https://github.com/dafny-lang/dafny/wiki/INSTALL#building-and-developing-from-source-code)


If you want to propose code changes for the Dafny project, please note:
- The [Dafny License](./LICENSE.txt)
- The requirement that all contributions are made under the terms of that [MIT License](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).
- To propose code changes, use the standard Github multi-user project process, which is described for Dafny on the [wiki](https://github.com/dafny-lang/dafny/wiki/Setting-up-a-development-copy-of-Dafny).

If your change is user-visible, then part of the PR should be corresponding changes to the
[`RELEASE_NOTES.md`](../RELEASE_NOTES.md) file and to the 
[Dafny Reference Manual](./docs/DafnyRef).

Any PR should have tests that check whether the bug-fix fixes the problem addressed or that the new functionality 
is properly working.

  - Dafny's integration tests are in [`Test`](../Test).  PRs that fix issues reported on GitHub should include a test in [`Test/git-issues/`](../Test/git-issues/).

    Each `.dfy` file in `Test/` is a test, with a  [`lit`](https://llvm.org/docs/CommandGuide/lit.html) header describing how to run it and a `.expect` file indicating the expected output.  See [`Test/README.md`](../Test/README.md) for more info on running Dafny' integration tests.

  - Dafny's unit tests are in various `*.Test` directories in [`Source`](../Source).

  Our CI is configured to run all tests when you create a PR.  To run tests locally, use `dotnet test Source/Dafny.sln` (but note that running the tests for our compiler backends requires installing lots of additional software).

Pull Requests should be merged using 'Squash and merge' unless otherwise noted.

For pull requests that move more than a thousand lines of code from an existing to a new file, please take the following steps:
- Create a separate pull request that includes just the code move.
- Use the script found in Scripts/git-cp.sh. Running git-cp.sh src dst will copy file src to dst using a branch and a merge, and you can then remove the duplicated parts from src and dst to complete the code move (this process allows git to track the file copy, as described in this StackOverflow answer).
- Merge the pull request using 'Create a merge commit' instead of 'Squash and merge'.

## FAQ

### What to do if the nightly build failed but because of a "download failure"?

If the test in a PR named `Build and Test / check-deep-tests / check-deep-tests` failed, clicking on its "details" reveals a view (view 1) in which you can see a failed run with the failure being something like "Error: Last run of deep-tests.yml did not succeed (some URL in parentheses).

Clicking on this URL will reveal the deep tests that were run (view 2). If one of these tests is just a "download failure", then one simply needs to re-run it (button on the top right).
Once it succeeds, one has to go back to (view 1) and re-run the failed jobs, so that it will retrieve the latest successful deep tests.

After doing these steps once, for other PRs, one only needs to re-run deep checks in (view 1)

