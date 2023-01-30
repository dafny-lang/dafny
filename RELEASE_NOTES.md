# Upcoming

See [docs/dev/news/](docs/dev/news/).

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
- fix: Last edited verified first & corrected display of verification status. (https://github.com/dafny-lang/dafny/pull/2352)
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
