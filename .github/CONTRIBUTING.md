# Contributing Guidelines

Thanks for contributing to Dafny!  Github is the right place to discuss feature requests, report issues with Dafny, or contact the Dafny developers.

Before reporting an issue here, consider whether it would be better handled in one of the following places:

- [Stack Overflow](https://stackoverflow.com/questions/tagged/dafny), an online Q&A website, for help with writing and proving Dafny programs.
- [`dafny-lang/ide-vscode`](https://github.com/dafny-lang/ide-vscode), Dafny's VSCode plugin, for issues or feature requests specific to the plugin itself (however, issues with Dafny's LSP server should be reported here).
- [`boogie-org/boogie-friends`](https://github.com/boogie-org/boogie-friends/), Dafny's Emacs mode, for Emacs-specific problems.
- [`boogie-org/boogie`](https://github.com/boogie-org/boogie), Dafny's intermediate verification language, for questions and issues specific to Boogie.

All other pull requests and issues can be submitted here.

- For issues, please include your Dafny version number, any relevant code, and expected results.

- For pull requests, consider updating [`RELEASE_NOTES.md`](../RELEASE_NOTES.md) if your change is user-visible, and add tests if possible.

  - Dafny's integration tests are in [`Test`](../Test).  PRs that fix issues reported on GitHub should include a test in [`Test/git-issues/`](../Test/git-issues/).

    Each `.dfy` file in `Test/` a test, with a  [`lit`](https://llvm.org/docs/CommandGuide/lit.html) header describing how to run it and a `.expect` file indicating the expected output.  See [`Test/README.md`](../Test/README.md) for more info on running Dafny' integration tests.

  - Dafny's unit tests are in various `*.Test` directories in [`Source`](../Source).

  Our CI is configured to run all tests when you create a PR.  To run tests locally, use `dotnet test Source/Dafny.sln` (but note that running the tests for our compiler backends requires installing lots of additional software).

## Code of Conduct

See [`CODE_OF_CONDUCT.md`](./CODE_OF_CONDUCT.md).
