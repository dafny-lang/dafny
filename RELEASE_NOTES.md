# 3.4 

The top four improvements in Dafny 3.4 are:
- For certain classes of changes, prevent unexpected changes in verification behavior when changing a Dafny program 
- Add command line options to assist in debugging verification performance.
- Critical fixes to the IDE and greatly improved responsiveness of non-verification IDE features. 
- The C# back-end supports traits as type parameters on datatypes.

### Verification
- fix: Resolve the following unsoundness issue: https://github.com/dafny-lang/dafny/issues/1619

- feat: Prevent changes in the verification behavior of a proof, when any of these types of changes are made to Dafny user code:
  - Changes logically unrelated to the proof being verified.
  - Changes to the name of any declaration
  - Changes to the order of top-level declarations
- feat: Assist in debugging the verification performance of a proof by adding the '/vcsSplitOnEveryAssert' CLI option and '{:vcs_split_on_every_assert}' attribute, and report the outcome and duration of splits when they occur in /verificationLogger:trx content.

### IDE 
- fix: Clean up process resources if IDE closed or restarted
- fix: Do not let the Dafny compilation status bar get in a stuck state

- feat: Verification status reporting shows which proof is being verified, which can help debug slow to verify proofs.
- feat: Publish parsing and resolution diagnostics before verification has completed. Verification diagnostics from previous runs are migrated.
- feat: Enable 'go to definition', 'hover' and 'signature help' features before verification has completed
- feat: Improve the hover feature to work for a wider scope of Dafny constructs, including function and method parameters, forall, exists and let expressions, and set and map comprehensions.
- feat: Add an experimental verification caching feature, which enables automatically determining which proofs need to verify again after making changes.

### UX
- feat: Improve error reporting when providing wrongly typed arguments in a function call
- feat: Improve error reporting when using type tests

### C#
- fix: resolve an instance where Dafny would produce invalid C# code: https://github.com/dafny-lang/dafny/issues/1607
- feat: support traits as type parameters on datatypes: https://github.com/dafny-lang/dafny/issues/1499

## Breaking changes

- Proofs such as methods and lemma's whose verification behavior, either the result or the verification time, depend on arbitrary behavior in Dafny's solver, may show different verification behavior in Dafny 3.4. For customers who are not ready to change those proofs to make their verification more reliable, we offer the command line option `/mimicVerificationOf:3.3` to  keep the Dafny 3.4 verification behavior consistent with 3.3.

- In Dafny 3.3, comprehensions quantified over subset types did not validate the constraint of the subset type, which could result in crashes at run-time. In 3.4, subset types are disabled in set comprehensions in compiled contexts, unless the subset constraint is itself compilable.

Before, the following code would pass Dafny and be compiled without error, but would crash at run-time:
```
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
Error: RefinedData is a subset type and its constraint is not compilable, hence it cannot yet be used as the type of a bound variable in set comprehension. The next error will explain why the constraint is not compilable.
Error: ghost constants are allowed only in specification contexts