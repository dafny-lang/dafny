# Upcoming

See [docs/dev/news/](docs/dev/news/).

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
