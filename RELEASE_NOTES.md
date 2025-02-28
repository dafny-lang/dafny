# Upcoming

See [docs/dev/news/](docs/dev/news/).

# 4.10.0

## New features

- Support for code actions in the language server to:
  - Insert failing implicit assertions in a "by" clause by preference.
  - Insert forall statement for any forall expressions that could not be proved
  - Insert calc statement for any equality that cannot be proved.
  (https://github.com/dafny-lang/dafny/pull/6044)

- Besides `--filter-position :<line>`, also support `--filter-position :<start>-<end>`, `--filter-position :<start>-` and `--filter-position :-<end>` (https://github.com/dafny-lang/dafny/pull/6077)

- The options --iterations from the command `measure-complexity`, has been renamed to `--mutations`. The option `--progress VerificationJob` has been renamed to `--progress Batch`. (https://github.com/dafny-lang/dafny/pull/6078)

## Bug fixes

- By clauses for assign-such-that statements (:|), are now never ignored. (https://github.com/dafny-lang/dafny/pull/6024)

- The code action for assertion no longer suggests asserting the same assertion. (https://github.com/dafny-lang/dafny/pull/6025)

- Fix a bug that caused a crash when translating by blocks (https://github.com/dafny-lang/dafny/pull/6050)

# 4.9.1

## New features

- Introduce the attributes {:isolate} and {:isolate "paths} that simplify the verification of an assertion by introducing additional verification jobs. {:isolate} can be applied to `assert`, `return` and `continue` statements. When using `{:isolate_assertions}` or `--isolate-assertions`, each return statement now creates a separate verification job for each ensures clause. Previously all ensures clauses where verified in a single job, for all return statements. (https://github.com/dafny-lang/dafny/pull/5832)

- Fill in matching patterns for the quantifiers introduced by automatic induction to represent the induction hypothesis. Suppress the generation of the induction hypothesis if no such matching patterns are found. Enhance tooltips accordingly. This feature is added to stabilize verification, but by sometimes not generating induction hypotheses, some automatic proofs may no longer go through. For backward compatibility, use an explicit `{:induction ...}` where `...` is the list of variables to use for the induction-hypothesis quantifier. Additionally, use a  `{:nowarn}` attribute to suppress any warning about lack of matching patterns.

  Improve the selection of induction variables.

  Allow codatatype equality in matching patterns and as a focal predicate for extreme predicates.

  More specifically:

  * If a lemma bears `{:induction x, y, z}`, where `x, y, z` is a subset of the lemma's parameters (in the same order
     that the lemma gives them), then an induction hypothesis (IH) is generated. The IH quantifies over the
     given variables.

     For an instance-member lemma, the variables may include the implicit `this` parameter.

     For an extreme lemma, the IH generated is the for corresponding prefix lemma, and the given variables may
     include the implicit parameter `_k`.

     If good matching patterns are found for the quantifier, then these are indicated in tooltips.
     If no patterns are found, then a warning is generated; except, if the lemma bears `{:nowarn}`, then only
     an informational message is given.

  * If a lemma bears `{:induction}` or `{:induction true}`, then a list of induction variables is determined heuristically.

     If the list is empty, then a warning message is generated and no IH is generated. If the list is nonempty,
     an IH is generated and the list of variables is indicated in a tooltip.

     If good matching patterns are found for the quantifier, then these are indicated in tooltips.
     If no patterns are found, then a warning is generated; except, if the lemma bears {:nowarn}, then only
     an informational message is given.

  * If a lemma bears `{:induction false}`, then no IH is generated.

  * If a lemma bears an `:induction` attribute other than those listed above, then an error is generated.

  * If a lemma bears no `:induction` attribute, and the `--manual-lemma-induction` flag is present, then no IH is generated.

  * Otherwise, a list of induction variables is determined heuristically.

     If this list is empty, then no IH is generated and no warning/info is given.

     If the list is nonempty, then the machinery looks for matching patterns for the IH quantifier. If none are
     found, then no IH is generated.  An informational message is generated, saying which candidate variables were
     used and saying that no matching patterns were found.

     If patterns are found, then an IH is generated, the list of variables and the patterns are indicated in tooltips,
     and the patterns are used with the IH quantifier.

     The pattern search can be overriden by providing patterns explicitly using the `{:inductionTrigger}` attribute.
     This attribute has the same syntax as the `{:trigger}` attribute.  Using an empty list of triggers restores
     Dafny's legacy behavior (no triggers for lemma induction hypotheses).
  (https://github.com/dafny-lang/dafny/pull/5835)

- Accept `decreases to` and `nonincreases to` expressions with 0 LHSs and/or 0 RHSs, and allow parentheses to be omitted when there is 1 LHS and 1 RHS. (https://github.com/dafny-lang/dafny/pull/5891)

- Allow forall statements in statement expressions (https://github.com/dafny-lang/dafny/pull/5894)

- When using `--isolate-assertions` or `{:isolate_assertions}`, a separate assertion batch will be generated per pair of return statement and ensures clause. (https://github.com/dafny-lang/dafny/pull/5917)

## Bug fixes

- `{:only}` on members only affects verification on the current file. (https://github.com/dafny-lang/dafny/pull/5730)

- Fixed a bug that caused "hide *" and "reveal *" not to work when used in statement expressions, 
  after a variable assignment occurred in the same expression.
  (https://github.com/dafny-lang/dafny/pull/5781)

- Fix malformed Boogie in function override checks (https://github.com/dafny-lang/dafny/pull/5875)

- Fix soundness issue where the verifier had assumed properties of `this` already during the first phase of a constructor (https://github.com/dafny-lang/dafny/pull/5876)

- Don't assume type information before binding variables (for let expressions and named function results) (https://github.com/dafny-lang/dafny/pull/5877)

- Enable using reveal statement expression inside witness expressions (https://github.com/dafny-lang/dafny/pull/5882)

- Fix formatting of var by statements (https://github.com/dafny-lang/dafny/pull/5927)

- Fix bugs that occur when using `{:extern}` to export members (https://github.com/dafny-lang/dafny/pull/5939)

- Fixed a bug that would cause the symbol verification tasks to be done multiple times when using module refinement (https://github.com/dafny-lang/dafny/pull/5967)

- Map range requires equality for enclosing type to support equality (https://github.com/dafny-lang/dafny/pull/5972)

- Improved code navigation for datatype update expressions (https://github.com/dafny-lang/dafny/pull/5986)

# 4.9.0

## New features

- Added opaque blocks to the language. Opaque blocks enable improving verification performance. See the documentation for more details. (https://github.com/dafny-lang/dafny/pull/5761)

- By blocks ("... by { ... }") are now available for assert statements, call statements, and the three types of assignments (:=, :-, :|). Also, by blocks should now be more intuitive since they enable proving any assertions on the left-hand side of the 'by', not just the 'outermost' one. For example, previously `assert 3 / x == 1 by { assume x == 3; }` could still give a possible division by zero error, but now it won't. (https://github.com/dafny-lang/dafny/pull/5779)

- Use --suggest-proof-refactoring to be alerted of function definitions, which have no contribution to a method's proof, and facts, which are only used once in a proof. (https://github.com/dafny-lang/dafny/pull/5812)

- Support for [top-level @-attributes](https://dafny.org/latest/DafnyRef/DafnyRef#sec-at-attributes) (https://github.com/dafny-lang/dafny/pull/5825)

## Bug fixes

- Enable abstract imports to work well with match expression that occur in specifications (https://github.com/dafny-lang/dafny/pull/5808)

- Fix a bug that prevented using reveal statement expressions in the body of a constant. (https://github.com/dafny-lang/dafny/pull/5823)

- Improve performance of `dafny verify` for large applications, by removing memory leaks (https://github.com/dafny-lang/dafny/pull/5827)

- Green gutter icons cover constants without RHS (https://github.com/dafny-lang/dafny/pull/5841)

# 4.8.1

## New features

- feat: allow type parameters of `newtype` declarations
  feat: support optional `witness` clause of constraint-less `newtype` declarations
  feat: show tool tips for auto-completed type parameters
  feat: show tool tips for inferred `(==)` characteristics
  fix: Don't let `newtype` well-formedness checking affect witness checking (fixes ##5520)
  fix: Check the emptiness status of constraint-less `newtype` declarations (fixes #5521)
  (https://github.com/dafny-lang/dafny/pull/5495)

- New feature: model extractor

  ### CLI option

  The `dafny verify` command now has an option `--extract:<file>`, where (just like for the various print options) `<file>` is allowed to be `-` to denote standard output.

  ### Extract mechanism

  Upon successful verification, the new extract mechanism visits the AST of the given program. For any module marked with `{:extract}`, the extract-worthy material from the module is output. The output declarations will be in the same order as they appear textually in the module (in particular, the fact that module-level Dafny declarations are collected in an internal class `_default` has no bearing on the output order).

  Three kinds of declarations are extract-worthy:

  * A type declaration `A<X, Y, Z>` that bears an attribute `{:extract_name B}` is extracted into a Boogie type declaration `type B _ _ _;`.

      The definition of the type is ignored. (The intended usage for an extracted type is that the Dafny program give a definition for the type, which goes to show the existence of such a type.)

  * A function declaration `F(x: X, y: Y): Z` that bears an attribute `{:extract_name G}` is extracted into a Boogie function declaration `function G(x: X, y: Y): Z;`.

      The body of the Dafny function is ignored. (The intended usage for an extracted function is that the Dafny program give a definition for the function, which goes to show the existence of such a function.)

  * A lemma declaration `L(x: X, y: Y) requires P ensures Q` that bears an attribute `{:extract_pattern ...}` or an attribute `{:extract_used_by ...}` is extracted into a Boogie `axiom`. The axiom has the basic form `axiom (forall x: X, y: Y :: P ==> Q);`.

      If the lemma has an attribute `{:extract_used_by F}`, then the axiom will be emitted into the `uses` clause of the Boogie function generated for Dafny function `F`.

      If the lemma has no in-parameters, the axiom is just `P ==> Q`.

      If the lemma has in-parameters, then any attribute `{:extract_pattern E, F, G}` adds a matching pattern `{ E, F, G }` to the emitted quantifier. Also, any attribute `{:extract_attribute "name", E, F, G}` adds an attribute `{:name E, F, G}` to the quantifier.

  ### Expressions

  The pre- and postconditions of extracted lemmas turn into analogous Boogie expressions, and the types of function/lemma parameters and bound variables are extracted into analogous Boogie types. The intended usage of the extract mechanism is that these expressions and types do indeed have analogous Boogie types.

  At this time, only a limited set of expressions and types are supported, but more can be added in the future.

  Any `forall` and `exists` quantifiers in expressions are allowed to use `:extract_pattern` and `:extract_attribute` attributes, as described above for lemmas.

  Some extracted expressions are simplified. For example, `true && !!P` is simplified to `P`.

  ### Soundness

  The Dafny program that is used as input for the extraction is treated like any other Dafny program. The intended usage of the extraction mechanism is to prove parts of the axiomatization in `DafnyPrelude.bpl` to be logically consistent. Whether or not the extracted Boogie declarations meet this goal depends on the given Dafny program. For example, if the given Dafny program formalizes sequences in terms of maps and formalizes maps in terms of sequences, then the extraction probably does not provide guarantees of consistency.
  (https://github.com/dafny-lang/dafny/pull/5621)

- Dafny-to-Rust: `{:test}` methods generate `#[test]` wrappers in Rust that can be invoked using `cargo test`.
  Similarly, `{:rust_cfg_test}` on modules generates a `#[cfg(test)]` in the resulting rust module.
  (https://github.com/dafny-lang/dafny/pull/5676)

## Bug fixes

- Allow hiding instance member using a static reference

- Enable using "hide *" in the context of a recursive function

- Support for double constant initialization in Dafny-to-Rust (https://github.com/dafny-lang/dafny/pull/5642)

- Support for enumerating datatypes in the Rust backend (https://github.com/dafny-lang/dafny/pull/5643)

- Tail-Recursion for the Dafny-to-Rust compiler (https://github.com/dafny-lang/dafny/pull/5647)

- The new resolver (accessible using `--type-system-refresh`) can now handle revealing instance functions using a static receiver, as it is the case for the current resolver (https://github.com/dafny-lang/dafny/pull/5760)

# 4.8.0

## New features

- Introduce `hide` statements that enable hiding the body of a function at a particular proof location, which allows simplifying the verification of that proof in case the body of the function is not needed for the proof. `Hide` statements make the opaque keyword on functions obsolete. (https://github.com/dafny-lang/dafny/pull/5562)

- Let the command `measure-complexity` output which verification tasks performed the worst in terms of resource count. Output looks like:
  ...
  Verification task on line 8 in file measure-complexity.dfy consumed 9984 resources
  Verification task on line 7 in file measure-complexity.dfy consumed 9065 resources
  ...
  (https://github.com/dafny-lang/dafny/pull/5631)

- Enable the option `--enforce-determinism` for the commands `resolve` and `verify` (https://github.com/dafny-lang/dafny/pull/5632)

- Method calls get an optional by-proof that hides the precondtion and its proof (https://github.com/dafny-lang/dafny/pull/5662)

## Bug fixes

- Clarify error location of inlined `is` predicates. (https://github.com/dafny-lang/dafny/pull/5587)

- Optimize the compilation of single-LHS assignment statements to allow the RHS to be a deeply nested expression. This solves a problem in compiling to Java, since `javac` does not deal gracefully with nested lambda expressions. (https://github.com/dafny-lang/dafny/pull/5589)

- Crash when compiling an empty source file while including testing code (https://github.com/dafny-lang/dafny/pull/5638)

- Let the options --print-mode=NoGhostOrIncludes and --print-mode=NoIncludes work (https://github.com/dafny-lang/dafny/pull/5645)

- Verification in the IDE now works correctly when declaring nested module in a different file than their parent. (https://github.com/dafny-lang/dafny/pull/5650)

- Fix NRE that would occur when using --legacy-data-constructors (https://github.com/dafny-lang/dafny/pull/5655)

# 4.7.0

## New features

- Add the option --find-project <path> that given a Dafny file traverses up the file tree until it finds a Dafny project that includes that path. This is useful when developing a particular file and doing CLI invocations as part of your development workflow.

- Improved error reporting when verification times out or runs out of resources, so that when using `--isolate-assertions`, the error message points to the problematic assertion. (https://github.com/dafny-lang/dafny/pull/5281)

- Support newtypes based on map and imap (https://github.com/dafny-lang/dafny/pull/5175)

- To enable smoothly working with multiple projects inside a single repository, Dafny now allows using a Dafny project file as an argument to `--library`. When using `dafny verify`, Dafny ensures that any dependencies specified through a project are verified as well, unless using the flag `--dont-verify-dependencies`. (https://github.com/dafny-lang/dafny/pull/5297)

- Experimental Dafny-to-Rust compiler development
  - Supports emitting code even if malformed with option `--emit-uncompilable-code`.
  - Supports for immutable collections and operators
  (https://github.com/dafny-lang/dafny/pull/5081)

- Allow for plugins to add custom request handlers to the language server. (https://github.com/dafny-lang/dafny/pull/5161)

- Deprecated the unicode-char option (https://github.com/dafny-lang/dafny/pull/5302)

- Warn when passing a Dafny source file to `--library` (https://github.com/dafny-lang/dafny/pull/5313)

- Add support for "translation records", which record the options used when translating library code.
  * `--translation-record` - Provides a `.dtr` file from a previous translation of library code. Can be specified multiple times.
  * `--translation-record-output` - Customizes where to write the translation record for the current translation. Defaults to the output directory.
  Providing translation records is necessary to handle options such as `--outer-module` that affect how code is translated.
  (https://github.com/dafny-lang/dafny/pull/5346)

- The new `decreases to` expression makes it possible to write an explicit assertion equivalent to the internal check Dafny does to prove that a loop or recursive call terminates. (https://github.com/dafny-lang/dafny/pull/5367)

- The new `assigned` expression makes it possible to explicitly assert that a variable, constant, out-parameter, or object field is definitely assigned. (https://github.com/dafny-lang/dafny/pull/5501)

- Greatly reduced the size of generated code for the backends: C#, Python, GoLang and JavaScript.

- Introduce additional warnings that previously only appeared when running the `dafny audit` command. Two warnings are as follows:
  - Emit a warning when exporting a declaration that has requires clauses or subset type inputs
  - Emit a warning when importing a declaration that has ensures clauses or subset type outputs
Those two can be silenced with the flag `--allow-external-contracts`. A third new warning occurs when using bodyless functions marked with `{:extern}`, and can be silenced using the option `--allow-external-function`.

- Enable project files to specify another project file as a base, which copies all configuration from that base file. More information can be found in the reference manual. 

## Bug fixes

- Fix a common memory leak that occurred when doing verification in the IDE that could easily consume gigabytes of memory. 

- Fix bugs that could cause the IDE to become unresponsive

- Improve the performance of the Dafny IDE by fixing bugs in its caching code

- No longer reuse SMT solver processes between different document version when using the IDE, making the IDE verification behavior more inline to that of the CLI

- Fix bugs that caused Dafny IDE internal errors (https://github.com/dafny-lang/dafny/issues/5355, https://github.com/dafny-lang/dafny/pull/5543, https://github.com/dafny-lang/dafny/pull/5548)

- Fix bugs in the Dafny IDEs code navigation and renaming features when working with definition that are not referred to.

- Fix a code navigation bug that could occur when navigating to and from module imports
- 
- Fix a code navigation bug that could occur when navigating to and from explicit types of variables
  (https://github.com/dafny-lang/dafny/pull/5419)

- Let the IDE no longer show diagnostics for projects for which all files have been closed (https://github.com/dafny-lang/dafny/pull/5437)

- Fix bug that could lead to an unresponsive IDE when working with project files (https://github.com/dafny-lang/dafny/pull/5444)

- Fix bugs in Dafny library files that could cause them not to work with certain option values, such as --function-syntax=3 

- Fix a bug that prevented building Dafny libraries for Dafny projects that could verify without errors.

- Reserved module identifiers correctly escaped in GoLang (https://github.com/dafny-lang/dafny/pull/4181)

- Fix a soundness issue that could be triggered by calling ensures fresh in the post-condition of a constructor (https://github.com/dafny-lang/dafny/pull/4700)

- Ability to cast a datatype to its trait when overriding functions (https://github.com/dafny-lang/dafny/pull/4823)

- Fix crash that could occur when using a constructor in a match pattern where a tuple was expected (https://github.com/dafny-lang/dafny/pull/4860)

- No longer emit an incorrect internal error while waiting for verification message (https://github.com/dafny-lang/dafny/pull/5209)

- More helpful error messages when read fields not mentioned in reads clauses (https://github.com/dafny-lang/dafny/pull/5262)

- Check datatype constructors for bad type-parameter instantiations (https://github.com/dafny-lang/dafny/pull/5278)

- Avoid name clashes with Go built-in modules (https://github.com/dafny-lang/dafny/pull/5283)

- Invalid Python code for nested set and map comprehensions (https://github.com/dafny-lang/dafny/pull/5287)

- Stop incorrectly emitting the error message "Dafny encountered an internal error while waiting for this symbol to verify" (https://github.com/dafny-lang/dafny/pull/5295)

- Rename the `dafny generate-tests` option `--coverage-report` to `--expected-coverage-report` (https://github.com/dafny-lang/dafny/pull/5301)

- Stop giving an incorrect warning about a missing {:axiom} clause on an opaque constant. (https://github.com/dafny-lang/dafny/pull/5306)

- No new resolver crash when datatype update expressions are partially resolved (https://github.com/dafny-lang/dafny/pull/5331)

- Optional pre-type won't cause a crash anymore (https://github.com/dafny-lang/dafny/pull/5369)

- Unguarded enumeration of bound variables in set and map comprehensions (https://github.com/dafny-lang/dafny/pull/5402)

- Reference the correct `this` after removing the tail call of a function or method (https://github.com/dafny-lang/dafny/pull/5474)

- Apply name mangling to datatype names in Python more often (https://github.com/dafny-lang/dafny/pull/5476)

- Only guard `this` when eliminating tail calls, if possible (https://github.com/dafny-lang/dafny/pull/5524)

- Compiled disjunctive nested pattern matching no longer crashing (https://github.com/dafny-lang/dafny/pull/5572)

# 4.6.0

## New features

- Add a check to `dafny run` that notifies the user when a value that was parsed as a user program argument, and which occurs before a `--` token, starts with `--`, since this indicates they probably mistyped a Dafny option name. (https://github.com/dafny-lang/dafny/pull/5097)

- Add an option --progress that can be used to track the progress of verification. (https://github.com/dafny-lang/dafny/pull/5150)

- Add the attribute `{:isolate_assertions}`, which does the same as `{:vcs_split_on_every_assert}`. Deprecated `{:vcs_split_on_every_assert}` (https://github.com/dafny-lang/dafny/pull/5247)

## Bug fixes

- (soundness issue) Twostate predicate now check if their not new arguments are allocated in the previous heap (https://github.com/dafny-lang/dafny/pull/4844)

- Add uniform checking of type characteristics in refinement modules (https://github.com/dafny-lang/dafny/pull/5146)

- Fixed links associated with the standard libraries. (https://github.com/dafny-lang/dafny/pull/5176)

- fix: Disable the "erase datatype wrappers" optimization if the datatype implements any traits.
  feat: Allow the "erase datatype wrappers" optimization if the only fields in the datatype are ghost fields.
  (https://github.com/dafny-lang/dafny/pull/5234)

- Fix the default string value emitted for JavaScript (https://github.com/dafny-lang/dafny/pull/5239)

# 4.5.0

## New features

- Add the option `--include-test-runner` to `dafny translate`, to enable getting the same result as `dafny test` when doing manual compilation. (https://github.com/dafny-lang/dafny/pull/3818)

- - Fix: verification in the IDE no longer fails for iterators
  - Fix: the IDE now provides feedback when verification fails to run, for example due to a bad solver path
  - Fix: let the IDE correctly use the solver-path option when it's specified in a project file
  - Feat: improve the order of verification diagnostics emitted by the Dafny CLI, so that they now always follow the line order of the program.
  (https://github.com/dafny-lang/dafny/pull/4798)

- - Add an option `--filter-position` to the `dafny verify` command. The option filters what gets verified based on a source location. The location is specified as a file path suffix, optionally followed by a colon and a line number. For example, `dafny verify dfyconfig.toml --filter-position=source1.dfy:5` will only verify things that range over line 5 in the file `source1.dfy`. In combination with ``--isolate-assertions`, individual assertions can be verified by filtering on the line that contains them. When processing a single file, the filename can be skipped, for example: `dafny verify MyFile.dfy --filter-position=:23`
  - Add an option `--filter-symbol` to the `dafny verify` command, that only verifies symbols whose fully qualified name contains the given argument. For example, `dafny verify dfyconfig.toml --filter-symbol=MyModule` will verify everything inside `MyModule`.
  - The option `--boogie-filter` has been removed in favor of --filter-symbol
  (https://github.com/dafny-lang/dafny/pull/4816)

- Add a `json` format to those supported by `--log-format` and `/verificationLogger`, for producing thorough, machine readable logs of verification results. (https://github.com/dafny-lang/dafny/pull/4951)

- - Flip the behavior of `--warn-deprecation` and change the name to `--allow-deprecation`, so the default is now false, which is standard for boolean options.
  - When using `--allow-deprecation`, deprecated code is shown using tooltips in the IDE, and on the CLI when using `--show-tooltips`.
  - Replace the option `--warn-as-error` with the option `--allow-warnings`. The new option, when false, the default value, causes Dafny to stop generating executable output and return a failure exit code, when warnings occur in the program. Contrary to the previous `--warn-as-error` option, warnings are always reported as warnings.
    - During development, users must use `dafny run --allow-warnings` if they want to run their Dafny code when it contains warnings.
    - If users have builds that were passing with warnings, they have to add `--allow-warnings` to allow them to still pass. 
    - If users upgrade to a new Dafny version, and are not using `--allow-warnings`, and do not want to migrate off of deprecated features, they will have to use `--allow-deprecation`.
  - When using the legacy CLI, the option /warningsAsErrors now has the behavior of --allow-warnings=false
  - A doo file that was created using `--allow-warnings` causes a warning if used by a consumer that does not use it.
  (https://github.com/dafny-lang/dafny/pull/4971)

- The new `{:contradiction}` attribute can be placed on an `assert` statement to indicate that it forms part of an intentional proof by contradiction and therefore shouldn't be warned about when `--warn-contradictory-assumptions` is turned on. (https://github.com/dafny-lang/dafny/pull/5001)

- Function and method parameters and return types, and datatype constructor arguments, can now have attributes. By default, there are no attributes that Dafny recognizes in these positions, but custom back-ends can use this feature to get extra information from the source files. (https://github.com/dafny-lang/dafny/pull/5032)

- Under the CLI option `--general-newtypes`, the base type of a `newtype` declaration can now be (`int` or `real`, as before, or) `bool`, `char`, or a bitvector type.

  `as` and `is` expressions now support more types than before. In addition, run-time type tests are supported for `is` expressions, provided type parameters are injective (as was already required) and provided the constraints of any subset type or newtype is compilable. Note, although both `as` and `is` allow many more useful cases than before, using `--general-newtypes` will also forbid some unusual cases that were previously allowed. Any such case that is now forbidden can still be done by doing the `as`/`is` via `int`.
  (https://github.com/dafny-lang/dafny/pull/5061)

- Allow newtype declarations to be based on set/iset/multiset/seq. (https://github.com/dafny-lang/dafny/pull/5133)

## Bug fixes

- Fixed crash caused by cycle in type declaration (https://github.com/dafny-lang/dafny/pull/4471)

- Fix resolution of unary minus in new resolver (https://github.com/dafny-lang/dafny/pull/4737)

- The command line and the language server now use the same counterexample-related Z3 options. (https://github.com/dafny-lang/dafny/pull/4792)

- Dafny no longer crashes when required parameters occur after optional ones. (https://github.com/dafny-lang/dafny/pull/4809)

- Use defensive coding to prevent a crash in the IDE that could occur in the context of code actions. (https://github.com/dafny-lang/dafny/pull/4818)

- Fix null-pointer problem in new resolver (https://github.com/dafny-lang/dafny/pull/4875)

- Fixed a crash that could occur when a case body of a match that was inside a loop, had a continue or break statement. (https://github.com/dafny-lang/dafny/pull/4894)

- Compile run-time constraint checks for newtypes in comprehensions (https://github.com/dafny-lang/dafny/pull/4919)

- Fix null dereference in constant-folding invalid string-indexing expressions (https://github.com/dafny-lang/dafny/pull/4921)

- Check for correct usage of type characteristics in specifications and other places where they were missing.

  This fix will cause build breaks for programs with missing type characteristics (like `(!new)` and `(0)`). Any such error message is accompanied with a hint about what type characterics need to be added where.
  (https://github.com/dafny-lang/dafny/pull/4928)

- Initialize additional fields in the AST (https://github.com/dafny-lang/dafny/pull/4930)

- Fix crash when a function/method with a specification is overridden in an abstract type. (https://github.com/dafny-lang/dafny/pull/4954)

- Fix crash for lookup of non-existing member in new resolver (https://github.com/dafny-lang/dafny/pull/4955)

- Fix: check that subset-type variable's type is determined (resolver refresh).
  Fix crash in verifier when there was a previous error in determining subset-type/newtype base type.
  Fix crash in verifier when a subset type has no explicit `witness` clause and has a non-reference trait as its base type.
  (https://github.com/dafny-lang/dafny/pull/4956)

- The `{:rlimit N}` attribute, which multiplied `N` by 1000 before sending it to Z3, is deprecated in favor of the `{:resource_limit N}` attribute, which can accept string arguments with exponential notation for brevity.  The `--resource-limit` and `/rlimit` flags also now omit the multiplication, and the former allows exponential notation. (https://github.com/dafny-lang/dafny/pull/4975)

- Allow a datatype to depend on traits without being told "datatype has no instances" (https://github.com/dafny-lang/dafny/pull/4997)

- Don't consider `:= *` to be a definite assignment for non-ghost variables of a `(00)` type (https://github.com/dafny-lang/dafny/pull/5024)

- Detect the same ghost usage in initializing assignments as in other expressions. The effect of this fix is to allow more iset/imap comprehensions to be compiled.

  Also, report errors if the LHS of `:=` in compiled `map`/`imap` comprehensions contains ghosts.
  (https://github.com/dafny-lang/dafny/pull/5041)

- Escape names of nested modules in C# and Java (https://github.com/dafny-lang/dafny/pull/5049)

- A parent trait that is a reference type can now be named via `import opened`.

  Implicit conversions between a datatype and its parent traits no longer crashes the verifier.

  (Dis)equality expressions of a (co)datatype and its parent traits no longer crashes the verifier.
  (https://github.com/dafny-lang/dafny/pull/5058)

- Fixed support for newtypes as sequence comprehension lengths in Java (https://github.com/dafny-lang/dafny/pull/5065)

- Don't emit an error message for a `function-by-method` with unused type parameters. (https://github.com/dafny-lang/dafny/pull/5068)

- The syntax of a predicate definition must always include parentheses. (https://github.com/dafny-lang/dafny/pull/5069)

- Termination override check for certain non-reference trait implementations (https://github.com/dafny-lang/dafny/pull/5087)

- Malformed Python code for some functions involving lambdas (https://github.com/dafny-lang/dafny/pull/5093)

- Let verifier understand opaque function overrides, supporting both when the overridden function is opaque and non-opaque. Revealing such a function for one overriding type has the effect of revealing it for all overriding types.

  Also, forbid the case where a function is opaque in a parent trait and the function override is not opaque. (Previously, this had caused a crash.)
  (https://github.com/dafny-lang/dafny/pull/5111)

# 4.4.0

## New features

- Reads clauses on method declarations are now supported when the `--reads-clauses-on-methods` option is provided. 
  The `{:concurrent}` attribute now verifies that the `reads` and `modifies` clauses are empty instead of generating an auditor warning.
  (https://github.com/dafny-lang/dafny/pull/4440)

- Added two new options, `--warn-contradictory-assumptions` and `--warn-redundant-assumptions`, to detect potential problems with specifications that indicate that successful verification may be misleading. These options are currently hidden because they may occasionally produce false positives in cases where proofs are so trivial that the solver never does work on them. (https://github.com/dafny-lang/dafny/pull/4542)

- Verification of the `{:concurrent}` attribute on methods now allows non-empty `reads` and `modifies` clauses with the `{:assume_concurrent}` attribute. (https://github.com/dafny-lang/dafny/pull/4563)

- Implemented support for workspace/symbol request to allow IDE navigation by symbol. (https://github.com/dafny-lang/dafny/pull/4619)

- The new `--verification-coverage-report` flag to `dafny verify` creates an HTML report highlighting which portions of the program were and were not necessary for verification. The format is the same as for `dafny generate-tests --coverage-report` and files from the two commands can be merged. (https://github.com/dafny-lang/dafny/pull/4625)

- Built-in types such as the `nat` subset type, tuples, arrows, and arrays are now pre-compiled into each backend's runtime library,
  instead of emitted on every call to `dafny translate`, to avoid potential duplicate definitions when translating components separately.
  (https://github.com/dafny-lang/dafny/pull/4658)

- The new `--only-label` option to `merge-coverage-reports` includes only one category of highlighting in the output. For example, merging coverage reports from test generation and verification using the option `--only-label NotCovered` will highlight only the regions not covered by either testing or verification. (https://github.com/dafny-lang/dafny/pull/4673)

- The Dafny distribution now includes standard libraries, available with the `--standard-libraries` option.
  See https://github.com/dafny-lang/dafny/blob/master/Source/DafnyStandardLibraries/README.md for details.
  (https://github.com/dafny-lang/dafny/pull/4678)

- Introduce replaceable modules, which can be used to help define Dafny applications that translate to multiple target languages. (https://github.com/dafny-lang/dafny/pull/4681)

- The new `--coverage-report` flag to `dafny run` and `dafny test` creates an HTML report highlighting which portions of the program were executed at runtime. (https://github.com/dafny-lang/dafny/pull/4755)

- Enable turning nonlinear arithmetic on or off on a per-module basis, using the attribute `{:disable-nonlinear-arithmetic}`, 
  which optionally takes the value false to enable nonlinear arithmetic.
  (https://github.com/dafny-lang/dafny/pull/4773)

- Let the IDE provide code navigation in situations where the program parses but has resolution errors. Note that this only works for modules whose dependency tree does not have errors, or modules who contain errors themselves, but not for modules whose dependencies contain errors. (https://github.com/dafny-lang/dafny/pull/4855)

## Bug fixes

- Ensures that computing the set of values or items of map can only be done if the type of the range supports equality. (https://github.com/dafny-lang/dafny/pull/1373)

- Subset type decl's witness correctly taken into account (https://github.com/dafny-lang/dafny/pull/3792)

- Added a comprehensive test for test generation and fixed a bug that prevented test generation to process function-by-method declarations (https://github.com/dafny-lang/dafny/pull/4406)

- Optimized memory consumption of test generation by reusing the Boogie AST of the target Dafny program. (https://github.com/dafny-lang/dafny/pull/4530)

- Fix a bug that prevented certain types of lemma to be verified in the IDE (https://github.com/dafny-lang/dafny/pull/4607)

- Dot completion now works on values the type of which is a type synonym. (https://github.com/dafny-lang/dafny/pull/4635)

- Fix a case where the document symbol API would return incorrect data when working on a file with parse errors (https://github.com/dafny-lang/dafny/pull/4675)

- Emit less nested target code in match-case expressions (nice for readability, and necessary for Java) (https://github.com/dafny-lang/dafny/pull/4683)

- Ghost diagnostics are now correctly updated when they become empty (https://github.com/dafny-lang/dafny/pull/4693)

- Enable verification options that are configured in a Dafny project file, to be picked up by the Dafny language server (https://github.com/dafny-lang/dafny/pull/4703)

- Prevent double-counting of covered/uncovered lines in test coverage reports (https://github.com/dafny-lang/dafny/pull/4710)

- fix: correction of type inference for default expressions (https://github.com/dafny-lang/dafny/pull/4724)

- The new type checker now also supports static reveals for instance functions (https://github.com/dafny-lang/dafny/pull/4733)

- Resolve :- expressions with void outcomes in new resolver (https://github.com/dafny-lang/dafny/pull/4734)

- Crash in the resolver on type parameters of opaque functions in refined modules (https://github.com/dafny-lang/dafny/pull/4768)

- Fix error messages being printed after their context snippets (https://github.com/dafny-lang/dafny/pull/4787)

- Override checks no longer crashing when substituting type parameters and equality (https://github.com/dafny-lang/dafny/pull/4812)

- Removed one cause of need for restarting the IDE. (https://github.com/dafny-lang/dafny/pull/4833)

- The Python compiler emits reserved names for datatypes (https://github.com/dafny-lang/dafny/pull/4843)

# 4.3.0

## New features

- Add support for the Find References LSP request
  - Returned references may be incomplete when not using project mode
  (https://github.com/dafny-lang/dafny/pull/2320)

- Improve scalability of inlining for test generation and generate coverage information with respect to the original Dafny source (https://github.com/dafny-lang/dafny/pull/4255)

- Support generating of tests targeting path-coverage of the entire program and tests targeting call-graph-sensitive block coverage (referred to as Branch coverage) (https://github.com/dafny-lang/dafny/pull/4326)

- Add support for Rename LSP request
  - Support requires enabling project mode and defining a Dafny project file
  (https://github.com/dafny-lang/dafny/pull/4365)

- Make verification in the IDE more responsive by starting verification after translating the required module to Boogie, instead of first translating all modules that could be verified. (https://github.com/dafny-lang/dafny/pull/4378)

- The Dafny IDE now has improved behavior when working with a Dafny file that's part of a Dafny project. A Dafny file is part of a project if a `dfyconfig.toml` can be found somewhere in the file's path hierarchy, such as in the same folder or in the parent folder. A `dfyconfig.toml` can specify which Dafny options to use for that project, and can specify which Dafny files are part of the project. By default, the project will include all .dfy files reachable from the folder in which the `dfyconfig.toml` resides. Project related features of the IDE are:
  - Whenever one file in the project is opened, diagnostics for all files in the Dafny project are shown. When including a file with errors that's part of the same project, the message "the included file contains errors" is no longer shown. Instead, the included file's errors are shown directly.
  - If any file in the project is changed, diagnostics for all files in the project are updated. Without a project, changing an included file will not update diagnostics for the including file until the including file is also changed.
  - The find references feature (also added in this release), works better in files that are part of a project, since only then can it find references that are inside files that include the current file.
  - The assisted rename feature (also added in this release), only works for files that are part of a project.
  - When using a project file, it is no longer necessary to use include directives. In the previous version of Dafny, it was already the case that the Dafny CLI, when passed a Dafny project file, does not require include directives to process the Dafny program. The same now holds for the Dafny IDE when working with Dafny files for which a project file can be found.
  - If any file in the project is resolved, all files in the project are resolved. Opening a file in a project that's already resolved means the opened file is resolved instantly.
  - The IDE's memory consumption stays the same regardless of how many files in a project are opened. Without a project, the IDE increases it's memory usage for each open file.

  Try out the IDE's project support now by creating an empty `dfyconfig.toml` file in the root of your project repository.
  (https://github.com/dafny-lang/dafny/pull/4435)

- Prior to generating tests, Dafny now checks the targeted program for any features that test generation does not support or any misuse of test generation specific attributes.
  Any such issues are reported to the user.
  (https://github.com/dafny-lang/dafny/pull/4444)

- Added documentation of the generate-tests command to the reference manual (https://github.com/dafny-lang/dafny/pull/4445)

- When two modules in the same scope have the same name, Dafny now reports an error that contains the location of both modules. (https://github.com/dafny-lang/dafny/pull/4499)

- - The Dafny IDE will now report errors that occur in project files.
  - The Dafny IDE will now shown a hint diagnostic at the top of Dafny project files, that says which files are referenced by the project.
  (https://github.com/dafny-lang/dafny/pull/4539)

## Bug fixes

- Triggers warnings correclty converted into errors with --warn-as-errors (https://github.com/dafny-lang/dafny/pull/3358)

- Allow JavaScript keywords as names of Dafny modules (https://github.com/dafny-lang/dafny/pull/4243)

- Support odd characters in pathnames for Go (https://github.com/dafny-lang/dafny/pull/4257)

- Allow Dafny filenames compiled to Java to start with a digit (https://github.com/dafny-lang/dafny/pull/4258)

- Parser now supports files with a lot of consecutive single-line comments (https://github.com/dafny-lang/dafny/pull/4261)

- Gutter icons more robust (https://github.com/dafny-lang/dafny/pull/4287)

- Unresolved abstract imports no longer crash the resolver (https://github.com/dafny-lang/dafny/pull/4298)

- Make capitalization of target Go code consistent (https://github.com/dafny-lang/dafny/pull/4310)

- Refining an abstract module with a class with an opaque function no longer crashes (https://github.com/dafny-lang/dafny/pull/4315)

- Dafny can now produce coverage reports indicating which parts of the program are expected to be covered by automatically generated tests. 
  The same functionality can be used to report other forms of coverage.
  (https://github.com/dafny-lang/dafny/pull/4325)

- Fix issue that would prevent the IDE from correctly handling default export sets (https://github.com/dafny-lang/dafny/pull/4328)

- Allow function-syntax and other options with a custom default to be overridden in `dfyconfig.toml` (https://github.com/dafny-lang/dafny/pull/4357)

- There were two differences between verification in the IDE and the CLI, one small and one tiny, which would only become apparent for proofs that Z3 had trouble verifying. The small difference has been resolved, while the tiny one still persists, so the IDE and CLI should behave almost equivalently now, including resource counts, on most code. (https://github.com/dafny-lang/dafny/pull/4374)

- Old command line interface for test generation is no longer supported, all calls should use dafny generate-tests (https://github.com/dafny-lang/dafny/pull/4385)

- Fixed a bug leading to stack overflow during counterexample extraction on some programs. (https://github.com/dafny-lang/dafny/pull/4392)

- Ability to use .Key as a constant name in datatypes and classes (https://github.com/dafny-lang/dafny/pull/4394)

- Existential assertions are now printed correctly (https://github.com/dafny-lang/dafny/pull/4401)

- When a symbol such as a method is not given a name, the error given by Dafny now shows where this problem occurs. (https://github.com/dafny-lang/dafny/pull/4411)

- Fix flickering and incorrect results in the verification status bar, and improve responsiveness of verification diagnostics (https://github.com/dafny-lang/dafny/pull/4413)

- Significantly improve IDE responsiveness for large projects, preventing it from appearing unresponsive or incorrect. Previously, for projects of a certain size, the IDE would not be able to keep up with incoming changes made by the user, possibly causing it to never catch up and appearing frozen or showing outdated results. (https://github.com/dafny-lang/dafny/pull/4419)

- Declarations with {:only} ensure that other declarations aren't displayed as verified in the gutter icons (https://github.com/dafny-lang/dafny/pull/4432)

- Fix issues that could cause the IDE status bar to show incorrect information (https://github.com/dafny-lang/dafny/pull/4454)

- When verification times out, only show a red underline on the name of the verifiable for which verification timed out, instead of under its whole definition. (https://github.com/dafny-lang/dafny/pull/4477)

- Prevent the IDE from becoming completely unresponsive after certain kinds of parse errors would occur. (https://github.com/dafny-lang/dafny/pull/4495)

- Support all types of options in the Dafny project file (dfyconfig.toml) (https://github.com/dafny-lang/dafny/pull/4506)

- Fix an issue that would cause some types of errors and other diagnostics not to appear in the IDE, if they appeared in files other than the active one. (https://github.com/dafny-lang/dafny/pull/4513)

- Fix an IDE issue that would lead to exceptions when using module export declarations and making edits in imported modules that were re-exported (https://github.com/dafny-lang/dafny/pull/4556)

- Fix a leak in the IDE that would cause it to become less responsive over time. (https://github.com/dafny-lang/dafny/pull/4570)

# 4.2.0

## New features

- The --show-snippets options is implemented for errors printed to the console (https://github.com/dafny-lang/dafny/pull/3304)

- * {:error} now accepts success messages
  * Better hover messages when using the IDE
  * Harmonized language to use more "could not prove" rather than "might not hold"
  (https://github.com/dafny-lang/dafny/pull/3687)

- Unicode representations of mathematical symbols (such as logical implies, and, and or) are no longer recognized by the parser. (https://github.com/dafny-lang/dafny/pull/3755)

- Allow the Dafny IDE to publish 'Parsing' and 'Preparing Verification' messages to let the user better understand what they're waiting for. (https://github.com/dafny-lang/dafny/pull/4031)

- Removed obsolete options /mimicVerificationOf, /allowGlobals (https://github.com/dafny-lang/dafny/pull/4062)

- Allow the `{:only}` attribute to be used on members in addition to `assert` statements (https://github.com/dafny-lang/dafny/pull/4074)

- The obsolete and unsound option /allocated is removed; the behavior of dafny is locked to the case of /allocated:4. (https://github.com/dafny-lang/dafny/pull/4076)

- When using the Dafny CLI, error messages of the form "the included file <filename> contains error(s)" are no longer reported, since the actual errors for these included files are shown as well. When using the Dafny server, errors like these are still shown, since the Dafny server only shows errors for currently opened files. In addition, such errors are now also shown for files that are indirectly included by an opened file. (https://github.com/dafny-lang/dafny/pull/4083)

- When using the Dafny IDE, parsing is now cached in order to improve performance when making changes in multi-file projects. (https://github.com/dafny-lang/dafny/pull/4085)

- Errors issued in command-line mode now show source code context by default; this behavior can be disabled using the option --show-snippets:false. (https://github.com/dafny-lang/dafny/pull/4087)

- Reduced resolution time by up to 50%. Measurements on large codebases show a 35% average reduction in resolution time.

- After generating Python code we run the byte-code compiler to surface possible issues earlier, if it's not subsequently run. (https://github.com/dafny-lang/dafny/pull/4155)

- Improve the responsiveness of the Dafny language server when making changes while it is in the 'Resolving...' state. (https://github.com/dafny-lang/dafny/pull/4175)

- It is now possible to reveal an instance function of a class by a static reveal, without the need of an object of that class. (https://github.com/dafny-lang/dafny/pull/4176)

- Support for the `--bprint` option for language server arguments (https://github.com/dafny-lang/dafny/pull/4206)

- Improve printing of real numbers to use decimal notation more often (https://github.com/dafny-lang/dafny/pull/4235)

- When translated to other languages, Dafny module names no longer have the suffix `_Compile` appended to them. This may cause issues with existing code from non-Dafny languages in your codebase, if that code was previously referencing modules with `_Compile` in the name. You can migrate either by removing the `_Compile` part of references in your codebase, or by using the backwards compatibility option `--compile-suffix` when using `translate`, `build`, or `run`. (https://github.com/dafny-lang/dafny/pull/4265)

- Counterexample parsing now supports both the 'Arguments' and 'Predicates' polymorphism encoding in Boogie. (https://github.com/dafny-lang/dafny/pull/4299)

## Bug fixes

- Removed wrong "related position" precision when dealing with regrouped quantifiers (https://github.com/dafny-lang/dafny/pull/2211)

- Fixed crash on an empty filename (https://github.com/dafny-lang/dafny/pull/3549)

- Fixes crash if solver-path is not found (https://github.com/dafny-lang/dafny/pull/3572)

- Avoid infinite recursion when trying to construct a potentially self-referential object during test generation (https://github.com/dafny-lang/dafny/pull/3727)

- Better error message when incorrect number of out parameters (https://github.com/dafny-lang/dafny/pull/3835)

- Compilation of continue labels no longer crashing in Go (https://github.com/dafny-lang/dafny/pull/3978)

- The terminology 'opaque type' is changed to 'abstract type (for uninterpreted type declarations), to avoid ambiguity with used of the 'opaque' keyword and revealing declarations (https://github.com/dafny-lang/dafny/pull/3990)

- Ensures override checks have access to fuel constant equivalences (https://github.com/dafny-lang/dafny/pull/3995)

- No more crash when using constant in pattern (https://github.com/dafny-lang/dafny/pull/4000)

- Remove multiset cardinality cap in Python (https://github.com/dafny-lang/dafny/pull/4014)

- Wrong statement order in generated code for certain for-loops (https://github.com/dafny-lang/dafny/pull/4015)

- Making assertion explicit work for nested statements (https://github.com/dafny-lang/dafny/pull/4016)

- Use type antecedent in Type/Allocation axioms for const fields
  Don't generate injectivity axioms for export-provided types
  (https://github.com/dafny-lang/dafny/pull/4020)

- Added a new CLI option --warn-deprecation, which is on by default
  Extraneous semicolons are now warned about by default; the warning can be disabled using --warn-deprecation:false
  (https://github.com/dafny-lang/dafny/pull/4041)

- Regression in the subset check of the function override check (https://github.com/dafny-lang/dafny/pull/4056)

- Fix function to function-by-method transformation pass in test generation that could previously lead to parsing errors (https://github.com/dafny-lang/dafny/pull/4067)

- Modules verified in the correct order to prevent Boogie Crash (https://github.com/dafny-lang/dafny/pull/4139)

- In VSCode, resource units are now always displayed with 3 digit precision.
  Moreover, they can now display values greater than MAX_INT without displaying a negative result.
  (https://github.com/dafny-lang/dafny/pull/4143)

- Remove redundant code in the test generation project (https://github.com/dafny-lang/dafny/pull/4146)

- Generate type axioms in the absence of explicit constraints for `newtype`s (https://github.com/dafny-lang/dafny/pull/4190)

- Support for opaque function handles (https://github.com/dafny-lang/dafny/pull/4202)

- Traits with opaque functions can now be extended without errors (https://github.com/dafny-lang/dafny/pull/4205)

- Disabled --show-snippets CLI option, which is otherwise on by default, during test generation
  Test generation modifies Boogie AST resulting from Dafny, and is, therefore, incompatible with --show-snippets
  (https://github.com/dafny-lang/dafny/pull/4216)

- Select proper division for real-based newtypes (https://github.com/dafny-lang/dafny/pull/4234)

- Formatting in the IDE consistent again with the CLI (https://github.com/dafny-lang/dafny/pull/4269)

- Fixes invalid declaration errors when verifying directly from Dafny using /typeEncoding:m. (https://github.com/dafny-lang/dafny/pull/4275)

- Make gutter icons more robust to document changes (https://github.com/dafny-lang/dafny/pull/4308)

# 4.1.0

## New features

- Added support for `.toml` based Dafny project files. For now the project file only allows specifying which Dafny files to include and exclude, and what options to use.
  The CLI commands that take Dafny files as input, such as build, run, translate, will now also accept Dafny project files.
  When using an IDE based on `dafny server`, such as the Dafny VSCode extension, the IDE will look for a Dafny project file by traversing up the file tree from the currently opened file, until it finds it `dfyconfig.toml`. The project file will override options specified in the IDE.
  (https://github.com/dafny-lang/dafny/pull/2907)

- Recognize the `{:only}` attribute on `assert` statements to temporarily transform other assertions into assumptions (https://github.com/dafny-lang/dafny/pull/3095)

- Exposes the --output and --spill-translation options for the dafny test command (https://github.com/dafny-lang/dafny/pull/3612)

- The `dafny audit` command now reports instances of the `{:concurrent}` attribute, intended to flag code that is intended, but can't be proven, to be safe for use in a concurrent setting. (https://github.com/dafny-lang/dafny/pull/3660)

- Added option --no-verify for language server (https://github.com/dafny-lang/dafny/pull/3732)

- Documenting Dafny Entities
  * Added `.GetDocstring(DafnyOptions)` to every AST node
  * Plugin support for custom Docstring formatter, 
  * Activatable plugin to support a subset of Javadoc through `--javadoclike-docstring-plugin`
  * Support for displaying docstring in VSCode
  (https://github.com/dafny-lang/dafny/pull/3756)

- Documentation of the syntax for docstrings added to the reference manual (https://github.com/dafny-lang/dafny/pull/3773)

- Labelled assertions and requires in functions (https://github.com/dafny-lang/dafny/pull/3804)

- API support for obtaining the Dafny expression that is being checked by each assertion (https://github.com/dafny-lang/dafny/pull/3888)

- Added a "Dafny Library" backend, which produces self-contained, pre-verified `.doo` files ideal for distributing shared libraries.
  `.doo` files are produced with commands of the form `dafny build -t:lib ...`.
  (https://github.com/dafny-lang/dafny/pull/3913)

- Semantic interpretation of dots in names for `{:extern}` modules when compiling to Python (https://github.com/dafny-lang/dafny/pull/3919)

- Code actions in editor to explicit failing assertions.
  In VSCode, place the cursor on a failing assertion that support being made explicit and either
  - Position the caret on a failing assertion, press CTRL+; and then ENTER
  - Hover over the failing division by zero, click "quick fix", press ENTER
  Both scenarios will explicit the failing assertion.
  If you don't see a quick fix, it means that the assertion cannot be automatically made explicit for now.

  Here is a initial list of assertions that can now be made explicit:
  - Division by zero
  - "out of bound" on sequences index, sequence slices, or array index
  - "Not in domain" on maps
  - "Could not prove unicity" of `var x :| ...` statement  
  - "Could not prove existence" of `var x :| ...` statement
  (https://github.com/dafny-lang/dafny/pull/3940)

## Bug fixes

- dafny test accepts a --methods-to-test option whose value is a regular expression selecting which tests to include in the test run (https://github.com/dafny-lang/dafny/pull/3221)

- The deprecated attributes :dllimport, :handle, and :heapQuantifier are no longer recognized. (https://github.com/dafny-lang/dafny/pull/3398)

- While using `dafny translate --target=java`, the `--include-runtime` option works as intended, while before it had no affect. (https://github.com/dafny-lang/dafny/pull/3611)

- Tested support for paths with spaces in them (https://github.com/dafny-lang/dafny/pull/3683)

- Crash related to the override check for generic functions (https://github.com/dafny-lang/dafny/pull/3692)

- Opaque functions guaranteed to be opaque until revealed (https://github.com/dafny-lang/dafny/pull/3719)

- Support for Corretto tests (https://github.com/dafny-lang/dafny/pull/3731)

- Right shift on native byte has the same consistent semantics even in Java (https://github.com/dafny-lang/dafny/pull/3734)

- Main and {:test} methods may now be in the same program (https://github.com/dafny-lang/dafny/pull/3744)

- The formatter now produces the same output whether invoked on the command-line or from VSCode (https://github.com/dafny-lang/dafny/pull/3790)

- The --solver-log option is now hidden from help unless --help-internal is used. (https://github.com/dafny-lang/dafny/pull/3798)

- Highlight "inconclusive" as errors in the gutter icons (https://github.com/dafny-lang/dafny/pull/3821)

- Docstring for functions with ensures (https://github.com/dafny-lang/dafny/pull/3840)

- Prevent a compiler crash that could occur when a datatype constructor was defined that has multiple parameters with the same name. (https://github.com/dafny-lang/dafny/pull/3860)

- Improved rules for nameonly parameters and parameter default-value expressions (https://github.com/dafny-lang/dafny/pull/3864)

- Fixes several compilation issues, mostly related to subset types defined by one of its type parameter (https://github.com/dafny-lang/dafny/pull/3893)

- Explicitly define inequality of `multiset`s in Python for better backwards compatibility (https://github.com/dafny-lang/dafny/pull/3904)

- Format for comprehension expressions (https://github.com/dafny-lang/dafny/pull/3912)

- Formatting for parameter default values (https://github.com/dafny-lang/dafny/pull/3944)

- Formatting issue in forall statement range (https://github.com/dafny-lang/dafny/pull/3960)

- Select alternative default calc operator only if it doesn't clash with given step operators (https://github.com/dafny-lang/dafny/pull/3963)

# 4.0.0

## Breaking changes

- Remove deprecated countVerificationErrors option (https://github.com/dafny-lang/dafny/pull/3165)

- The default version of Z3 Dafny uses for verification is now 4.12.1. (https://github.com/dafny-lang/dafny/pull/3400)

- The default values of several options has changed in Dafny 4.0. See `--help` for details.
     - `--function-syntax` changed from `3` to `4`
     - `--quantifier-syntax` changed from `3` to `4`
     - `--unicode-char` changed from `false` to `true`
  (https://github.com/dafny-lang/dafny/pull/3623)

- The default value of the `/allocated` option is now `4`, and the option itself is deprecated. (https://github.com/dafny-lang/dafny/pull/3637)

- Compilation to Go no longer attempts to use the Dafny `string` type and the Go `string` type interchangably when calling external methods (which was buggy and unsound). (https://github.com/dafny-lang/dafny/pull/3647)

# 3.13.1

## New features

- Expose non-relaxed definite assignment (`/definiteAssignment:4`) in legacy CLI (https://github.com/dafny-lang/dafny/pull/3641)

## Bug fixes

- Fix translation of Dafny FunctionHandles to Boogie (https://github.com/dafny-lang/dafny/pull/2266)

- To ensure that a `class` correctly implements a `trait`, we perform an override check. This check was previously faulty across `module`s, but works unconditionally now. (https://github.com/dafny-lang/dafny/pull/3479)

- Fixes to definite assignment and determinism options:
     - `--enforce-determinism` now forbids constructor-less classes
     - With non-relaxed definite assignment, allow auto-init fields to be uninitialized
  (https://github.com/dafny-lang/dafny/pull/3641)

# 3.12.0

## New features

- Dafny code formatter with IDE support (https://github.com/dafny-lang/dafny/pull/2399)
     - Makes it possible to "format" one or many Dafny files on the command-line, which for now means only changing the indentation of lines.
     - Instructions and more details are available in the [Dafny Reference Manual](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-dafny-format)

- Implements error detail information and quick fixes:
     - An error catalog with error message explanations is at https://dafny.org/latest/HowToFAQ/Errors
     - In VSCode, when hovering over an error, the hover information shows additional explanation and
       an error id, which is also a link to the error explanation page
     - Where a Quick Fix is available, the Quick Fix link is active
  (https://github.com/dafny-lang/dafny/pull/3299)

- * `opaque` is now a modifier, though still allowed, but deprecated as an identifier; it replaces the `{:opaque}` attribute (https://github.com/dafny-lang/dafny/pull/3462)

- * The value of the --library option is allowed to be a comma-separated list of files or folders (https://github.com/dafny-lang/dafny/pull/3540)

## Bug fixes

- Exclude verifier's type information for “new object” allocations (https://github.com/dafny-lang/dafny/pull/3450)

- The Dafny scanner no longer treats lines beginning with # (even those in strings) as pragmas. (https://github.com/dafny-lang/dafny/pull/3452)

- * The attribute `:heapQuantifier` is deprecated and will be removed in the future. (https://github.com/dafny-lang/dafny/pull/3456)

- Fixed race conditions in the language server that made gutter icons behave abnormally (https://github.com/dafny-lang/dafny/pull/3502)

- No more crash when hovering assertions that reference code written in other smaller files (https://github.com/dafny-lang/dafny/pull/3585)

# 3.11.0

## New features

- Go to definition now works reliably across all Dafny language constructs and across files. (https://github.com/dafny-lang/dafny/pull/2734)

- Improve performance of Go code by using native byte/char arrays (https://github.com/dafny-lang/dafny/pull/2818)

- Introduce the experimental `measure-complexity` command, whose output can be fed to the Dafny report generator. In a future update, we expect to merge the functionality of the report generator into this command. (https://github.com/dafny-lang/dafny/pull/3061)

- Integrate the Dafny [auditor plugin](https://github.com/dafny-lang/compiler-bootstrap/tree/main/src/Tools/Auditor) as a built-in `dafny audit` command. (https://github.com/dafny-lang/dafny/pull/3175)

- Add the `--solver-path` option to allow customizing the SMT solver used when using the new Dafny CLI user interface. (https://github.com/dafny-lang/dafny/pull/3184)

- Add the experimental `--test-assumptions` option to all execution commands: run, build, translate and test.
  When turned on, inserts runtime tests at locations where (implicit) assumptions occur, such as when calling or being called by external code and when using assume statements.
  Functionality is still being expanded. Currently only checks contracts on every call to a function or method marked with the {:extern} attribute.
  (https://github.com/dafny-lang/dafny/pull/3185)

- For the command `translate`, renamed the option `--target` into `language` and turned it into a mandatory argument. (https://github.com/dafny-lang/dafny/pull/3239)

- Havoc assignments now count as assignments for definite-assignment checks. (https://github.com/dafny-lang/dafny/pull/3311)

- Unless `--enforce-determinism` is used, no errors are given for arrays that are allocated without being initialized.
  (https://github.com/dafny-lang/dafny/pull/3311)

- Enable passing a percentage value to the --cores option, to use a percentage of the total number of logical cores on the machine for verification. (https://github.com/dafny-lang/dafny/pull/3357)

- `dafny build` for Java now creates a library or executable jar file.
  - If there is a Main method, the jar is an executable jar. So a simple A.dfy can be built as `dafny build -t:java A.dfy`
    and then run as `java -jar A.jar`
  - If there is no Main entry point, all the generated class files are assembled into a library jar file that can be used on a
    classpath as a java library.
  - In both cases, the DafnyRuntime library is included in the generated jar.
  - In old and new CLIs, the default location and name of the jar file is the name of the first dfy file, with the extension changed
  - In old and new CLIs, the path and name of the output jar file can be given by the --output option, with .jar added if necessary
  - As before, the compilation artifacts (.java and .class files) are placed in a directory whose name is the same as the jar file
    but without the .jar extension and with '-java' appended
  - With the new CLI, the generated .java artifacts are deleted unless --spill-translation=true and the .class files are deleted in any case;
    both kinds of files are retained with the legacy CLI for backwards compatibility.
  - If any other jar files are needed to compile the dafny/java program, they must be on the CLASSPATH;
    the same CLASSPATH used to compile the program is needed to run the program

  Having a library or executable jar simplifies the user's task in figuring out how to use the built artifacts.
  (https://github.com/dafny-lang/dafny/pull/3355)

## Bug fixes

- Nonexistent files passed on the CLI now result in a graceful exit (https://github.com/dafny-lang/dafny/pull/2719)

- Check loop invariants on entry, even when such are the only proof obligations in a method. (https://github.com/dafny-lang/dafny/pull/3244)

- The :options attribute now accepts new style options `--function-syntax` and `--quantifier-syntax` (https://github.com/dafny-lang/dafny/pull/3252)

- Improved error messages for `dafny translate` (https://github.com/dafny-lang/dafny/pull/3274)

- The :test attribute is now compatible with `dafny run` and `dafny build` (https://github.com/dafny-lang/dafny/pull/3275)

- Settings `--cores=0` will cause Dafny to use half of the available cores. (https://github.com/dafny-lang/dafny/pull/3276)

- Removed an infeasible assertion in the Dafny Runtime for Java (https://github.com/dafny-lang/dafny/pull/3280)

- Language server displays more relevant information on hovering assertions (https://github.com/dafny-lang/dafny/pull/3281)

- Any `(==)` inferred for a type parameter of an iterator is now also inferred for the corresponding non-null iterator type. (https://github.com/dafny-lang/dafny/pull/3284)

- The otherwise ambiguous program fragment `export least predicate` is parsed such that `least` (or `greatest`) is the export identifier (https://github.com/dafny-lang/dafny/pull/3291)

- The parser no longer generates bad tokens when invoked through `/library` (https://github.com/dafny-lang/dafny/pull/3301)

- Match expressions no longer incorrectly convert between newtypes and their basetype (https://github.com/dafny-lang/dafny/pull/3333)

- Warn that 'new' cannot be used in expressions, instead of throwing a parse error (https://github.com/dafny-lang/dafny/pull/3366)

- The attributes `:dllimport` and `:handle` are now deprecated. They were undocumented, untested, and not maintained. (https://github.com/dafny-lang/dafny/pull/3399)

- Fixed an axiom related to sequence comprehension extraction (https://github.com/dafny-lang/dafny/pull/3411)

# 3.10.0

## New features

- Emit warnings about possibly missing parentheses, based on operator precedence and unusual identation (https://github.com/dafny-lang/dafny/pull/2783)

- The DafnyRuntime NuGet package is now compatible with the .NET Standard 2.0 and .NET Framework 4.5.2 frameworks. (https://github.com/dafny-lang/dafny/pull/2795)

- Counterexamples involving sequences present elements in ascending order by index. (https://github.com/dafny-lang/dafny/pull/2975)

- The definition of the `char` type will change in Dafny version 4, to represent any Unicode scalar value instead of any UTF-16 code unit.
  The new command-line option `--unicode-char` allows early adoption of this mode.
  See section [7.5](http://dafny.org/dafny/DafnyRef/DafnyRef#sec-characters) of the Reference Manual for more details.
  (https://github.com/dafny-lang/dafny/pull/3016)

- `dafny run` now consistently requests UTF-8 output from compiled code.
  Use `chcp 65501` if you see garbled output on Windows.
  (https://github.com/dafny-lang/dafny/pull/3049)

- feat: support for traits as type arguments by fully allowing variance on datatypes in Java (https://github.com/dafny-lang/dafny/pull/3072)

## Bug fixes

- Function by method with the same name as a method won't crash resolver (https://github.com/dafny-lang/dafny/pull/2019)

- Better reporting if 'this' used in a subset type - and no crash (https://github.com/dafny-lang/dafny/pull/2068)

- Support for aliases in module resolution without crashing on imports (https://github.com/dafny-lang/dafny/pull/2108)

- Added missing check to prevent crash during resolution (https://github.com/dafny-lang/dafny/pull/2111)

- No more resolver crash on pattern match with incompatible types (https://github.com/dafny-lang/dafny/pull/2139)

- Refinements get errors at the correct place in LSP (https://github.com/dafny-lang/dafny/pull/2402)

- Resolution errors in the left-hand sign of an assign-such-that statement do not crash Dafny anymore (https://github.com/dafny-lang/dafny/pull/2496)

- old() cannot be inferred as a trigger alone (https://github.com/dafny-lang/dafny/pull/2593)

- Labels are no longer compiled in the case of variable declarations (https://github.com/dafny-lang/dafny/pull/2608)

- No more mention of reveal lemmas when implementing opaque functions in traits (https://github.com/dafny-lang/dafny/pull/2612)

- Verification of abstract modules not duplicated when imported (https://github.com/dafny-lang/dafny/pull/2703)

- Dafny now compiles functions that mix tail- and non-tail-recursive calls without crashing (https://github.com/dafny-lang/dafny/pull/2726)

- substitution of binding guards does not crash if splits present (https://github.com/dafny-lang/dafny/pull/2748)

- No more crash when constraining type synonyms (https://github.com/dafny-lang/dafny/pull/2829)

- Returning a tuple when it should be two variables does not crash Dafny anymore (https://github.com/dafny-lang/dafny/pull/2878)

- Default generic values no longer cause compilation error (https://github.com/dafny-lang/dafny/pull/2885)

- Now publishing Dafny Binary for MacOS Arm64 architecture (https://github.com/dafny-lang/dafny/pull/2889)

- Added a missing case in the Translator (pattern matching for variable declarations) (https://github.com/dafny-lang/dafny/pull/2920)

- The Python and Go backends now encode non-ASCII characters in string literals correctly (https://github.com/dafny-lang/dafny/pull/2926)

- Added a missing case of TypeSynonymDecl in the resolver that caused a crash (https://github.com/dafny-lang/dafny/pull/2927)

- Fix malformed Boogie generated for extreme predicates (https://github.com/dafny-lang/dafny/pull/2984)

- Counter-examples with non-integer sequence indices do not crash Dafny anymore. (https://github.com/dafny-lang/dafny/pull/3048)

- Use correct type for map update expression (https://github.com/dafny-lang/dafny/pull/3059)

- Language server no longer crashing in special case (https://github.com/dafny-lang/dafny/pull/3062)

- Resolved an instance in which the Dafny language server could enter a broken state. (https://github.com/dafny-lang/dafny/pull/3065)

- Do not refer to an implicit assignment in error messages on return statements (https://github.com/dafny-lang/dafny/pull/3125)

- Multiple exact same failing assertions do not crash the Boogie counter-example engine anymore (https://github.com/dafny-lang/dafny/pull/3136)

- Duplicate declarations caused by resolver do not crash the language server anymore (https://github.com/dafny-lang/dafny/pull/3155)

# 3.9.1

## New features

- The language server now supports all versions of z3 ≥ 4.8.5.  Dafny is still distributed with z3 4.8.5 and uses that version by default. (https://github.com/dafny-lang/dafny/pull/2820)

## Bug fixes

- Correct error highlighting on function called with default arguments (https://github.com/dafny-lang/dafny/pull/2826)

- Crash in the LSP in some code that does not parse (https://github.com/dafny-lang/dafny/pull/2833)

- A function used as a value in a non-ghost context must not have ghost parameters, and arrow types cannot have ghost parameters. (https://github.com/dafny-lang/dafny/pull/2847)

- Compiled lambdas now close only on non-ghost variables (https://github.com/dafny-lang/dafny/pull/2854)

- Previously, for a file printing the number of arguments, `dafny printing.dfy -compileTarget:js --args 1 2 3` would print 4: one for the executable, one for each argument.
  But `dafny -compile:2 -compileTarget:js printing.dfy; node ./printing.js` would print 5: One for `node`, one for `./printing.js`, and one for each argument.
  This fix ensures that `node ./printing.js` is considered as a single argument, and the first argument, to be consistent with every other language.
  (https://github.com/dafny-lang/dafny/pull/2876)

- Handle sequence-to-string equality correctly in the JavaScript runtime (https://github.com/dafny-lang/dafny/pull/2877)

- don't crash on type synonyms and subset types of array types in LHSs of simultaneous assignments (https://github.com/dafny-lang/dafny/pull/2884)

- Removed an bogus optimization on the Language Server (https://github.com/dafny-lang/dafny/pull/2890)

- The Dafny-to-Java compiler will now fully-qualify type casts in pattern destructors, avoiding "reference to TYPE is ambiguous" errors from javac. (https://github.com/dafny-lang/dafny/pull/2904)

- Variable declarations and formals in match cases do not trigger errors anymore. (https://github.com/dafny-lang/dafny/pull/2910)

# 3.9.0

- feat: Introduce a new Dafny CLI UI that complies with the POSIX standard and uses verbs to distinguish between use-cases. Run the Dafny CLI without arguments to view help for this new UI. (https://github.com/dafny-lang/dafny/pull/2823)
- feat: Support for testing certain contracts at runtime with a new `/testContracts` flag (https://github.com/dafny-lang/dafny/pull/2712)
- feat: Support for parsing Basic Multilingual Plane characters from UTF-8 in code and comments (https://github.com/dafny-lang/dafny/pull/2717)
- feat: Command-line arguments are now available from `Main` in Dafny programs, using `Main(args: seq<string>)` (https://github.com/dafny-lang/dafny/pull/2594)
- feat: Generate warning when 'old' has no effect (https://github.com/dafny-lang/dafny/pull/2610)
- fix: Missing related position in failing precondition (https://github.com/dafny-lang/dafny/pull/2658)
- fix: No more IDE crashing on the elephant operator (https://github.com/dafny-lang/dafny/pull/2668)
- fix: Use the right comparison operators for bitvectors in Javascript (https://github.com/dafny-lang/dafny/pull/2716)
- fix: Retain non-method-body block statements when cloning abstract signatures (https://github.com/dafny-lang/dafny/pull/2731)
- fix: Correctly substitute variables introduced by a binding guard (https://github.com/dafny-lang/dafny/pull/2745)
- fix: The CLI no longer attempts to load each DLL file passed to it. (https://github.com/dafny-lang/dafny/pull/2568)
- fix: Improved hints and error messages regarding variance/cardinality preservation (https://github.com/dafny-lang/dafny/pull/2774)
- feat: New behavior for `import opened M` where `M` contains a top-level declaration `M`, see PR for a full description (https://github.com/dafny-lang/dafny/pull/2355)
- fix: The DafnyServer package is now published to NuGet as well, which fixes the previously-broken version of the DafnyLanguageServer package. (https://github.com/dafny-lang/dafny/pull/2787)
- fix: Support for spaces in the path to Z3 (https://github.com/dafny-lang/dafny/pull/2812)
- deprecate: Statement-level refinement syntax (e.g. `assert ...`) is deprecated (https://github.com/dafny-lang/dafny/pull/2756)
- deprecate: The form of the modify statement with a block statement is deprecated
- docs: The user documentation at https://dafny.org has a new landing page

# 3.8.1

- feat: Support for the `{:opaque}` attibute on `const` (https://github.com/dafny-lang/dafny/pull/2545)
- feat: Support for plugin-based code actions on the IDE (https://github.com/dafny-lang/dafny/pull/2021)
- fix: Fixed a crash when parsing `newtype` in the parser (https://github.com/dafny-lang/dafny/pull/2649)
- fix: Added missing error reporting position on string prefix check (https://github.com/dafny-lang/dafny/pull/2652)
- fix: Prevent LSP server from exiting when a crash occurs (https://github.com/dafny-lang/dafny/pull/2664)
- fix: Fix bug where LSP server would not show diagnostics that referred to included files (https://github.com/dafny-lang/dafny/pull/2664)
- fix: Check all compiled expressions to be compilable (https://github.com/dafny-lang/dafny/pull/2641)
- fix: Better messages on hovering failing postconditions in IDE (https://github.com/dafny-lang/dafny/pull/2654)
- fix: Better error reporting on counter-examples if an option is not provided (https://github.com/dafny-lang/dafny/pull/2650)
- feat: Introduced ghost constructors in datatypes. One use of these is when working with uninitialized storage, see https://github.com/dafny-lang/rfcs/pull/11. (https://github.com/dafny-lang/dafny/pull/2666)


# 3.8.0

- fix: Use the right bitvector comparison in decrease checks
  (https://github.com/dafny-lang/dafny/pull/2512)
- fix: Don't use native division and modulo operators for non-native int-based newtypes in Java and C#.
  (https://github.com/dafny-lang/dafny/pull/2416)
- feat: Dafny now supports disjunctive (“or”) patterns in match statements and expressions.  Cases are separated by `|` characters.  Disjunctive patterns may not appear within other patterns and may not bind variables.
  (https://github.com/dafny-lang/dafny/pull/2448)
- feat: The Dafny Language Server used by the VSCode IDE extension is now available as a NuGet package called `DafnyLanguageServer` (https://github.com/dafny-lang/dafny/pull/2600)
- fix: Counterexamples - fix an integer parsing bug and correctly extract datatype and field names (https://github.com/dafny-lang/dafny/pull/2461)
- feat: New option `-diagnosticsFormat:json` to print Dafny error messages as JSON objects (one per line).
  (https://github.com/dafny-lang/dafny/pull/2363)
- fix: No more exceptions when hovering over variables without type, and types of local variabled kept under match statements (https://github.com/dafny-lang/dafny/pull/2437)
- fix: Check extreme predicates and constants in all types, not just classes
  (https://github.com/dafny-lang/dafny/pull/2515)
- fix: Correctly substitute type variables in override checks
  (https://github.com/dafny-lang/dafny/pull/2522)
- feat: `predicate P(x: int): (y: bool) ...` is now valid syntax (https://github.com/dafny-lang/dafny/pull/2454)
- fix: Improve the performance of proofs involving bit vector shifts (https://github.com/dafny-lang/dafny/pull/2520)
- fix: Perform well-definedness checks for ensures clauses of forall statements (https://github.com/dafny-lang/dafny/pull/2606)
- fix: Resolution and verification of StmtExpr now pay attention to if the StmtExpr is inside an 'old' (https://github.com/dafny-lang/dafny/pull/2607)

# 3.7.3

- feat: *Less code navigation when verifying code*: In the IDE, failing postconditions and preconditions error messages now immediately display the sub-conditions that Dafny could not prove. Both on hover and in the Problems window. (https://github.com/dafny-lang/dafny/pull/2434)
- feat: Whitespaces and comments are kept in relevant parts of the AST (https://github.com/dafny-lang/dafny/pull/1801)
- fix: NuGet packages no longer depend on specific patch releases of the .NET frameworks.


# 3.7.2

- fix: Hovering over variables and methods inside cases of nested match statements works again. (https://github.com/dafny-lang/dafny/pull/2334)
- fix: Fix bug in translation of two-state predicates with heap labels. (https://github.com/dafny-lang/dafny/pull/2300)
- fix: Check that arguments of 'unchanged' satisfy enclosing reads clause. (https://github.com/dafny-lang/dafny/pull/2302)
- feat: Whitespaces and comments are kept in relevant parts of the AST (https://github.com/dafny-lang/dafny/pull/1801)
- fix: Underconstrained closures don't crash Dafny anymore. (https://github.com/dafny-lang/dafny/pull/2382)
- fix: Caching in the language server does not prevent gutter icons from being updated correctly. (https://github.com/dafny-lang/dafny/pull/2312)
- fix: Last edited file verified first & corrected display of verification status. (https://github.com/dafny-lang/dafny/pull/2352)
- fix: Correctly infer type of numeric arguments, where the type is a subset type of a newtype. (https://github.com/dafny-lang/dafny/pull/2314)
- fix: Fix concurrency bug that sometimes led to an exception during the production of verification logs. (https://github.com/dafny-lang/dafny/pull/2398)


# 3.7.1

- fix: The Dafny runtime library for C# is now compatible with .NET Standard 2.1, as it was before 3.7.0. Its version has been updated to 1.2.0 to reflect this. (https://github.com/dafny-lang/dafny/pull/2277)
- fix: Methods produced by the test generation code can now be compiled directly to C# XUnit tests (https://github.com/dafny-lang/dafny/pull/2269)


# 3.7.0

- feat: The Dafny CLI, Dafny as a library, and the C# runtime are now available on NuGet. You can install the CLI with `dotnet tool install --global Dafny`. The library is available as `DafnyPipeline` and the runtime is available as `DafnyRuntime`. (https://github.com/dafny-lang/dafny/pull/2051)
- feat: New syntax for quantified variables, allowing per-variable domains (`x <- C`) and ranges (`x | P(x), y | Q(x, y)`). See [the quantifier domain section](https://dafny.org/latest/DafnyRef/DafnyRef#sec-quantifier-domains) of the Reference Manual. (https://github.com/dafny-lang/dafny/pull/2195)
- feat: The IDE will show verification errors for a method immediately after that method has been verified, instead of after all methods are verified. (https://github.com/dafny-lang/dafny/pull/2142)
- feat: Added "Resolving..." message for IDE extensions (https://github.com/dafny-lang/dafny/pull/2234)
- feat: Live verification diagnostics for the language server (https://github.com/dafny-lang/dafny/pull/1942)
- fix: Correctly specify the type of the receiver parameter when translating tail-recursive member functions to C# (https://github.com/dafny-lang/dafny/pull/2205)
- fix: Added support for type parameters in automatically generated tests (https://github.com/dafny-lang/dafny/pull/2227)
- fix: No more display of previous obsolete verification diagnostics if newer are available (https://github.com/dafny-lang/dafny/pull/2142)
- fix: Prevent the language server from crashing and not responding on resolution or ghost diagnostics errors (https://github.com/dafny-lang/dafny/pull/2080)
- fix: Various improvements to language server robustness (https://github.com/dafny-lang/dafny/pull/2254)


# 3.6.0

- feat: The `synthesize` attribute on methods with no body allows synthesizing objects based on method postconditions at compile time (currently only available for C#). See Section [22.2.20](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-synthesize-attr) of the Reference Manual. (https://github.com/dafny-lang/dafny/pull/1809)
- feat: The `/verificationLogger:text` option now prints all verification results in a human-readable form, including a description of each assertion in the program.
- feat: The `/randomSeedIterations:<n>` option (from Boogie) now tries to prove each verification condition `n` times with a different random seed each time, to help efficiently and conveniently measure the stability of verification. (https://github.com/boogie-org/boogie/pull/567)
- feat: The new `/runAllTests` can be used to execute all methods with the `{:test}` attribute, without depending on a testing framework in the target language.
- feat: Recognize `!in` operator when looking for compilable comprehensions (https://github.com/dafny-lang/dafny/pull/1939)
- feat: The Dafny language server now returns expressions ranges instead of token ranges to better report errors (https://github.com/dafny-lang/dafny/pull/1985)
- fix: Miscompilation due to incorrect parenthesization in C# output for casts. (https://github.com/dafny-lang/dafny/pull/1908)
- fix: Populate TestResult.ResourceCount in `/verificationLogger:csv` output correctly when verification condition splitting occurs (e.g. when using `/vcsSplitOnEveryAssert`).
- fix: DafnyOptions.Compiler was null, preventing instantiation of ModuleExportDecl (https://github.com/dafny-lang/dafny/pull/1933)
- fix: /showSnippets crashes Dafny's legacy server (https://github.com/dafny-lang/dafny/pull/1970)
- fix: Don't check for name collisions in modules that are not compiled (https://github.com/dafny-lang/dafny/pull/1998)
- fix: Allow datatype update expressions for constructors with nameonly parameters (https://github.com/dafny-lang/dafny/pull/1949)
- fix: Fix malformed Java code generated for comprehensions that use maps (https://github.com/dafny-lang/dafny/pull/1939)
- fix: Comprehensions with nested subset types fully supported, subtype is correctly checked (https://github.com/dafny-lang/dafny/pull/1997)
- fix: Fix induction hypothesis generated for lemmas with a receiver parameter (https://github.com/dafny-lang/dafny/pull/2002)
- fix: Make verifier understand `(!new)` (https://github.com/dafny-lang/dafny/pull/1935)
- feat: Some command-line options can now be applied to individual modules, using the `{:options}` attribute. (https://github.com/dafny-lang/dafny/pull/2073)
- fix: Missing subset type check in datatype updates (https://github.com/dafny-lang/dafny/pull/2059)
- fix: Fix initialization of non-auto-init in-parameters in C#/JavaScript/Go compilers (https://github.com/dafny-lang/dafny/pull/1935)
- fix: Resolution of static functions-by-method (https://github.com/dafny-lang/dafny/pull/2023)
- fix: Export sets did not work with inner modules (https://github.com/dafny-lang/dafny/pull/2025)
- fix: Prevent refinements from changing datatype and newtype definitions (https://github.com/dafny-lang/dafny/pull/2038)
- feat: The new `older` modifier on arguments to predicates indicates that a predicate ensures the allocatedness of some of its arguments. This allows more functions to show that their quantifiers do not depend on the allocation state. For more information, see the reference manual section on `older`. (https://github.com/dafny-lang/dafny/pull/1936)
- fix: Fix `(!new)` checks (https://github.com/dafny-lang/dafny/issues/1419)
- fix: multiset keyword no longer crashes the parser (https://github.com/dafny-lang/dafny/pull/2079)


# 3.5.0

- feat: `continue` statements. Like Dafny's `break` statements, these come in two forms: one that uses a label to name the continue target and one that specifies the continue target by nesting level. See section [19.2](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-break-continue) of the Reference Manual. (https://github.com/dafny-lang/dafny/pull/1839)
- feat: The keyword syntax for functions will change in Dafny version 4. The new command-line option `/functionSyntax` (see `/help`) allows early adoption of the new syntax. (https://github.com/dafny-lang/dafny/pull/1832)
- feat: Attribute `{:print}` declares that a method may have print effects. Print effects are enforced only with `/trackPrintEffects:1`.
- fix: No warning "File contains no code" if a file only contains a submodule (https://github.com/dafny-lang/dafny/pull/1840)
- fix: Stuck in verifying in VSCode - support for verification cancellation (https://github.com/dafny-lang/dafny/pull/1771)
- fix: export-reveals of function-by-method now allows the function body to be ghost (https://github.com/dafny-lang/dafny/pull/1855)
- fix: Regain C# 7.3 compatibility of the compiled code. (https://github.com/dafny-lang/dafny/pull/1877)
- fix: The error "assertion violation" is replaced by the better wording "assertion might not hold". This indicates better that the verifier is unable to prove the assertion. (https://github.com/dafny-lang/dafny/pull/1862)
- fix: Plug two memory leaks in Dafny's verification server (#1858, #1863)
- fix: Generate missing termination measures for subset types on sequences (#1875)
- fix: Resolve expressions in attributes in all specifications of functions and iterators. (https://github.com/dafny-lang/dafny/pull/1900)


# 3.4.2

- fix: No output when compiling to JavaScript on Windows (https://github.com/dafny-lang/dafny/pull/1824)
- fix: CanCall assumptions for loop invariants (https://github.com/dafny-lang/dafny/pull/1813)
- fix: Behavior of the C# runtime in a concurrent setting (https://github.com/dafny-lang/dafny/pull/1780)


# 3.4.1

- feat: Plugin support in the resolution pipeline (https://github.com/dafny-lang/dafny/pull/1739)
- fix: NullPointerException in the AST (https://github.com/dafny-lang/dafny/pull/1805)
- fix: Change datatype deconstruction in match statements for C# (https://github.com/dafny-lang/dafny/issues/1815)


# 3.4

- For certain classes of changes to a Dafny program, prevent unexpected changes in verification behavior.
- Add command line options to assist in debugging verification performance.
- Critical fixes to the IDE and greatly improved responsiveness of non-verification IDE features.
- The C# back-end supports traits as type parameters on datatypes.

### Verification
- feat: Prevent changes in the verification behavior of a proof, when any of these types of changes are made to Dafny user code:
  - Changes to declarations not referenced by the method being verified
  - Changes to the name of any declaration
  - Changes to the order of top-level declarations
- feat: Assist in debugging the verification performance of a proof by adding the `/vcsSplitOnEveryAssert` CLI option and `{:vcs_split_on_every_assert}` attribute (see https://github.com/boogie-org/boogie/issues/465), and report the outcome and duration of splits when they occur in `/verificationLogger:trx` content.
- feat: Add a `/verificationLogger:csv` CLI option that emits the same status and timing information as `/verificationLogger:trx`, but in an easier-to-parse format, along with Z3 resource counts for more repeatable tracking of verification difficulty.

- fix: Resolve unsoundness issue (https://github.com/dafny-lang/dafny/issues/1619).
- fix: Don't silently succeed if the solver crashes (https://github.com/boogie-org/boogie/pull/488).

### IDE
- feat: Verification status reporting shows which proof is being verified, which can help debug slow to verify proofs.
- feat: Publish parsing and resolution diagnostics before verification has completed. Verification diagnostics from previous runs are migrated.
- feat: Enable 'go to definition', 'hover' and 'signature help' features before verification has completed.
- feat: Improve the hover feature to work for a wider scope of Dafny constructs, including function and method parameters, forall, exists and let expressions, and set and map comprehensions.
- feat: Add an experimental verification caching feature, which enables automatically determining which proofs need to verify again after making changes.
- feat: Display related resolution errors using nested diagnostics instead of independent diagnostics.

- fix: Clean up process resources if IDE closed or restarted.
- fix: Do not let the Dafny compilation status bar get in a stuck state.

### UX
- feat: Improve error reporting when providing incorrectly typed arguments in a function call.
- feat: Improve error reporting when using type tests.

### C#
- feat: Support variant type parameters on datatype definitions, which enables using traits as type arguments (https://github.com/dafny-lang/dafny/issues/1499).
- feat: Support for downcasting both custom datatypes and functions (https://github.com/dafny-lang/dafny/pull/1645, https://github.com/dafny-lang/dafny/pull/1755).

- fix: Resolve various instances where Dafny would produce invalid C# code (https://github.com/dafny-lang/dafny/issues/1607, https://github.com/dafny-lang/dafny/issues/1761, and https://github.com/dafny-lang/dafny/issues/1762).

### Various improvements
- fix: `DafnyLanguageServer.dll` and `Dafny.dll` depended on two different versions of Newtonsoft.Json, which could cause crashes in development environments.
- fix: (error reporting) Types with the same name but from different modules are now disambiguated in error messages.
- fix: (error reporting) Messages about arguments / parameters type mismatch are clearer and include the parameter name if available.
- fix: (robustness) Exceptions during parsing, if any, won't crash the language server anymore.
- fix: The elephant operator (`:-`) has a clearer error message and no longer reject generic methods on its right-hand side.

## Breaking changes

- The verifier in Dafny 3.4 is now more efficient for many programs, and making changes to Dafny programs is less likely to cause verification to take longer or timeout. However, it is still possible for some correct programs to take longer to verify than on Dafny 3.3, or for verification to fail. For users with such programs who are not yet ready to modify them to pass the 3.4 verifier, we offer the command line option `/mimicVerificationOf:3.3` to keep the Dafny 3.4 verification behavior consistent with 3.3.

- In Dafny 3.3, comprehensions quantified over subset types did not validate the constraint of the subset type, which could result in crashes at run-time. In 3.4, subset types are disabled in set comprehensions in compiled contexts, unless the subset constraint is itself compilable.

  Before, the following code would pass Dafny and be compiled without error, but would crash at run-time:
  ```Dafny
  type RefinedData = x: Data | ghostFunction(x)
  method Main() {
    var s: set<Data> = ...
    var t = set x: RefinedData | x in s;
    forall x in t {
      if !ghostFunction(x) {
        var crash := 1/0;
      }
    }
  }
  ```
  In Dafny 3.4, the same code triggers a resolution error of the form:
  ```
  Error: RefinedData is a subset type and its constraint is not compilable, hence it cannot yet be used as the type of a bound variable in set comprehension. The next error will explain why the constraint is not compilable.
  Error: ghost constants are allowed only in specification contexts
  ```

- Changes in type inference may cause some programs to need manual type annotations. For example, in the nested pattern in the following program
  ```Dafny
  datatype X<+T> = X(x: T)
  datatype Y<T> = Y(y: T)

  function method M(): (r: X<Y<nat>>) {
      var d: X<Y<int>> := X(Y(3));
      match d
      case X(Y(i)) => X(Y(i))
  }
  ```
  the type of the Y constructor needs the type to be given explicitly `X(Y<nat>.Y(i)`. As a variation of that program
  ```Dafny
  datatype X<+T> = X(x: T)
  datatype Y<T> = Y(y: T)

  trait Tr {}
  class Cl extends Tr {
      constructor () {}
  }

  method M() returns (r: X<Y<Cl>>) {
      var cl := new Cl();
      var d: X<Y<Tr>> := X(Y(cl));
      match d
      case X(Y(tr)) => r := X(Y(tr));
  }
  ```
  the program can be specified with an explicit cast `X(Y(tr as Cl))`.
