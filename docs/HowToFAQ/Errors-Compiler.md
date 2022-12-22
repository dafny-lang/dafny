<!-- DafnyCore/Compilers/SinglePassCompiler.cs -->

## {0} Process exited with exit code {1}


## Error: Unable to start {psi.FileName}{additionalInfo}

## Compilation error: _msg_

## '_feature_' is not an element of the {TargetId} compiler's UnsupportedFeatures set

## Opaque type ('{0}') with extern attribute requires a compile hint.  Expected {{:extern compile_type_hint}} 

## Opaque type ('{0}') cannot be compiled; perhaps make it a type synonym or use :extern.

## since yield parameters are initialized arbitrarily, iterators are forbidden by the --enforce-determinism option

## Iterator {0} has no body

## The method \"{0}\" is not permitted as a main method ({1}).

## Could not find the method named by the -Main option: {0}

## More than one method is marked \"{{:main}}\". First declaration appeared at {0}.

## This method marked \"{{:main}}\" is not permitted as a main method ({0}).

## More than one method is declared as \"{0}\". First declaration appeared at {1}.

## This method "Main" is not permitted as a main method ({0}).

## Error: Function _name_ has no body

```dafny <!-- %check-translate -->
function f(): int
```

The given function has no body, which is OK for verification, but not OK for compilation --- the compiler does not know what content to give it.

## Error: Function _name_ must be compiled to use the {:test} attribute

```dafny <!-- %check-translate -->
function {:test} f(): int { 42 }
```

Only compiled functions and methods may be tested using the `dafny test` command, which tests everything marked with `{:test}`.
However this function is a ghost function, and consequently cannot be tested during execution.
If you want the function to be compiled,
declare the function as a `function` instead of `ghost function` in Dafny 4 
or as `function method` instead of `function` in Dafny 3.

## Method _name_ is annotated with :synthesize but is not static, has a body, or does not return anything

## Method _name_ has no body

-- 2 occurrences

## {0} '{1}' is marked as :handle, so all the traits it extends must be be marked as :handle as well: {2}

## {0} '{1}' is marked as :handle, so all its non-static members must be ghost: {2}

## an assume statement without an {{:axiom}} attribute cannot be compiled

## a forall statement without a body cannot be compiled

## a loop without a body cannot be compiled

## nondeterministic assignment forbidden by the --enforce-determinism option

## nondeterministic assignment forbidden by the --enforce-determinism option

## assign-such-that statement forbidden by the --enforce-determinism option

## this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'

## nondeterministic if statement forbidden by the --enforce-determinism option

## binding if statement forbidden by the --enforce-determinism option

## case-based if statement forbidden by the --enforce-determinism option

## nondeterministic loop forbidden by the --enforce-determinism option

## case-based loop forbidden by the --enforce-determinism option

## nondeterministic assignment forbidden by the --enforce-determinism option

-- this is the thrid occurrence

## compiler currently does not support assignments to more-than-6-dimensional arrays in forall statements

## modify statement without a body forbidden by the --enforce-determinism option

## assign-such-that search produced no value (line {0})

## this let-such-that expression is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'

## Comparison of a handle can only be with another handle

<!-- DafnyCore/Compileres/Synthesizer-Csharp.cs -->

## '{feature}' is not an element of the {TargetId} compiler's UnsupportedFeatures set

## Stubbing fields is not recommended (field {0} of object {1} inside method {2})