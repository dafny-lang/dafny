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
[`RELEASE_NOTES.md`](./RELEASE_NOTES.md) file (by following [this](./docs/dev/README.md)) and to the 
[Dafny Reference Manual](./docs/DafnyRef).

Any PR should have tests that check whether the bug-fix fixes the problem addressed or that the new functionality 
is properly working.

  - Dafny's integration tests are in [this directory](Source/IntegrationTests/TestFiles/LitTests/LitTest).  PRs that fix issues reported on GitHub should include a test under [`git-issues/`](Source/IntegrationTests/TestFiles/LitTests/LitTest/git-issues/).

    Each `.dfy` file in this directory is a test, with a  [`lit`](https://llvm.org/docs/CommandGuide/lit.html) header describing how to run it and a `.expect` file indicating the expected output.  See [this README.md file](Source/IntegrationTests/TestFiles/LitTests/LitTest/README.md) for more info on running Dafny' integration tests.

  - Dafny's unit tests are in various `*.Test` directories in [`Source`](./Source).

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

### How to fix nightly build failures / check deep tests?

- Create a branch (e.g. `fix-ci-<date>`) that should fix the nightly build.
  (Either an actual fix, or reverting a PR that caused the problem - look at the logs)
- Push your branch to the main Dafny repository.
- After pushing, you'll get a link to create a PR, click on it.
- **Before clicking on the "Create PR" button**, add the label `run-deep-tests`. If you add it later, you will have to push a new commit to trigger the deep tests.
- Click on the "Create PR" button.
  The CI will run the deep tests within this PR (and for every new commit pushed to the branch). Note that only the "required" tests block merging.
- If some required tests fail, investigate and push more commits, but know that each CI run takes a lot of time, so try to fix the problem with as few commits as possible (ideally 1)
  It is also possible you find some tests that fail randomly, in that case, re-run them and report to the team. Avoid using the re-run all failed jobs here, because it will re-run _all_ jobs, so select them individually instead.
- Have someone approve the PR and merge it (or auto-merge).
- Once the PR with the fix to the CI is merged to master, go to https://github.com/dafny-lang/dafny/actions/workflows/nightly-build.yml
- Select "Run workflow..."
- Select master
- Wait for this new run to succeed.
- Now go back to all the PRs where `check-deep-tests` were failing and re-run the failing tests by updating the PRs.

Subsequent CI runs should pick up the successful `deep-tests` run and make the `check-deep-tests` jobs succeed.

### How can I write portions of Dafny in Dafny itself?

Since https://github.com/dafny-lang/dafny/pull/2399, it is possible to add \*.dfy files next to other source files.
The plugin `dafny-msbuild` takes all the dafny files and compiles them into a single file `Source/DafnyCore/obj/Debug/net8.0/GeneratedFromDafny.cs`
that is automatically included in the build process. This file contains also the Dafny run-time in C#.
One example of such file is `Source/DafnyCore/AST/Formatting.dfy`, and you can use it as a starting point.

Since Dafny cannot read C# files directly, you have to declare the C# functions it is calling using the `{:extern}` attribute to
interoperate with Dafny.
For example, `Formatting.dfy`

- Defines `System.CsString` as an alias for c# strings and concatenation, so that we can interoperate with existing strings rather than using sequences of characters
- Defines `CsStringEmpty` as an alias for `System.String.Empty`
- Defines `Microsoft.Dafny.HelperString.FinishesByNewline` by also using externs. That helper is defined in `IndentationFormatter.cs`
- Defines a trait `IIndentationFormatter` that Dafny can extend and provide to `ReindentProgramFromFirstToken`

### What is the release process?

You can find a description of the release process in [docs/dev/RELEASE.md](https://github.com/dafny-lang/dafny/blob/master/docs/dev/RELEASE.md).

### Backwards compatibility

Dafny is still changing and backwards incompatible changes may be made. Any backwards compatibility breaking change must be easy to adapt to, such as by adding a command line option. In the future, we plan to add a `dafny migrate` command which should support migrating any Dafny codebase from the previous to the current CLI version. 

As rule, Dafny features must be marked as deprecated, including migration instructions, at least one release before they are removed.
