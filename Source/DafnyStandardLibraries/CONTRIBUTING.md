# Guidelines for Contributing to the Dafny Standard Libraries

If you're looking to make a big impact on the Dafny community,
you've come to the right place.
Reusable, general-purpose utilities are extremely valuable for any programming language,
but especially so for Dafny,
where we can save users the hard work of proving these utilities correct as well.

This document augments the [general guidelines on contributing to Dafny](../../CONTRIBUTING.md).
The general structure and automation of the surrounding Dafny implementation
takes care of a lot of the requirements on standard libraries automatically,
but there are a few additional points to be aware of.

## Standard library standards

This project tries to be an exemplar of Dafny development practices,
both to ensure a high level of quality of the libraries themselves,
and for other Dafny projects to imitate.
It tries to minimize how dependent it is on the mechanisms for ensuring the quality
of Dafny itself, since these techniques overlap but have different requirements.
It does not make use of LIT-style integration tests, for example,
but tries to make use of generally-available Dafny features and tooling instead.

### Examples and tests

Basic examples and/or tests are mandatory, for several reasons:

* Helping to explain the functionality of the library;
* Helping to ensure the specifications are actually useable,
  guarding against things like pre-conditions that are difficult or impossible to satisfy; and
* Ensuring the implementation actually works on all Dafny backends.

The build process uses `dafny test` against each stable Dafny backend, 
so use `{:test}` and `expect` rather than `print` to check results.
For some libraries having examples and tests that only use lemmas
to check things are provable are reasonable,
and it's fine if `dafny test` only ends up checking that verification succeeds,
but avoid non-ghost code that cannot be compiled.

The support for measuring runtime test coverage of Dafny code
is not complete enough to be applied easily to this project,
but will be added as soon as possible.
In the meantime, please ensure your testing coverage
is at least greater than 0%!

### Documentation

Make sure there is a top-level `*.md` file for the library,
even just as a simple landing page,
linked from the root [README.md](README.md) for this project.
Having documentation in either separate Markdown files or Dafny docstrings
is just fine. Do not add docstrings that simply repeat the information
in the signature of a declaration just for the sake of having a docstring.

The build process for this project uses a [`check-examples`](scripts/check-examples) script
to automatically test that code snippets are valid.
Make sure to add the necessary directives such as `<!-- %check-verify -->`!
Note that this copy of `check-examples` is different from the one in the top-level Scripts directory,
which generates LIT-style Dafny integration tests instead.

### Style and formatting

As much as possible, follow the [Dafny Style Guide](https://dafny.org/dafny/StyleGuide/Style-Guide).
The build process applies `dafny format` to all source.

### Packaging

For now all standard libraries are built together into a single `DafnyStandardLibraries.doo` file,
which is included as an embedded resource in `DafnyPipeline.dll`.
That will likely need to change as more libraries are imported,
in particular https://github.com/dafny-lang/libraries/tree/master/src/NonlinearArithmetic
which needs to build with `--disable-nonlinear-arithmetic`.
It will be fairly straightforward to build multiple `.doo` files that are all added
with the `--standard-libraries` option, but the build process will need to be tweaked to support that.

### External code

Several standard libraries will need to depend on `{:extern}`-ally implemented functionality.
The plan is to include such code in each backend's runtime,
but adding this to the build process is currently blocked on https://github.com/dafny-lang/dafny/issues/511.

### On brittleness

There are two sides to brittleness relevant to this project:

**Brittleness of the standard libraries**: This project uses the current 
[best known defense against brittleness](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-verification):
enforcing a tight upper-bound on the resources needed to verify each batch of assertions.
For simplicitly, this project just sets a direct `--resource-limit`,
rather than relying on the second-pass approach of the `dafny-reportgenerator`.
This limit is set aggressively low in the hopes that we can maintain it
even as new libraries are added, which means some existing code
will need to be refactored somewhat to be added here.

The downside of this approach is that it can be challenging to know when code is actually correct
but cannot be verified efficiently enough.
Feel free to temporarily raise this limit when developing libraries,
but we should be very resistant to raising the limit in the checked in copy.

**Brittleness of code using the standard libraries**: This one is tougher.
There is tension between two different use cases:

* New users of Dafny get a much better experience with libraries that make heavier use of Dafny's automation:
  not making most definitions opaque, including useful instrinsic specifications, and so on.
  This lets folks just starting with Dafny experience the joy of a proven-correct example
  much quicker, and providing basic utilities like `Option<T>` and `Seq.Filter` that Just Work
  are a big part of this pleasant and encouraging experience.
* Mature Dafny projects need to worry about their own brittleness,
  and would prefer all definitions are opaque and all specifications extrinsic instead.

For now, these libraries are more focused on the first use case,
but should plan for a smooth migration process to support the second better in the future.

Note the examples also specify a resource limit,
which is important to help reduce how much brittleness these libraries
inflict on consumers.

## Importing from dafny-lang/libraries

There are a couple of things to watch out for when importing libraries from the
[dafny-lang/libraries]() repository:

* Several libraries have two copies in `dafny-lang/libraries`: one under `src`,
  and one under `src/dafny`. The latter is a copy refactored to nest all modules under a top-level
  `Dafny` module to reduce the risk of naming conflicts. This is a great idea,
  but it turns out that using "Dafny" conflicts with some Dafny runtime symbols,
  so these libraries use `DafnyStdLib` instead. You will probably find you have to adjust
  documentation examples accordingly.

  When the latter copy exists, prefer to use it along with its the Markdown documentation,
  but check that there aren't significant differences between the two versions.
* `dafny-lang/libraries` relies on LIT for testing, but this project uses mostly `dafny test`.
  It should be possible to refactor existing example or test files to the latter approach:
  see [WrappersExamples.dfy](examples/WrappersExamples.dfy) compared to
  https://github.com/dafny-lang/libraries/blob/master/examples/WrappersExamples.dfy for example.
