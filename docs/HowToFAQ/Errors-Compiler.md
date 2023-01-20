<!-- %default %useHeadings -->

<!-- DafnyCore/Compilers/SinglePassCompiler.cs -->

## **Error: _process_ Process exited with exit code _code_**

The dafny compiler prepares a representation of the Dafny program in the desired target programming
language and then invokes the target language's compiler on those files as a subsidiary process.
This error message indicates that the sub-process terminated with an error of some sort.
This should not ordinarily happen. Some possible causes are
- lack of resources that caused the underlying compiler to fail
- lack of or corrupted installation of the underlying compiler
- a bug in dafny whereby the source code it prepares for the compiler is faulty

There may be additional error messages from the underlying compiler that can help debug this situation.
You can also attempt to run the target programming language compiler manually in your system 
to make sure it is functional.

## **Error: Unable to start _target_**

The dafny compiler prepares a representation of the Dafny program in the desired target programming
language and then invokes the target language's compiler on those files as a subsidiary process.
This error message indicates that this sub-process would not start;
it gives some additional information about what the invoking process was told about the failure to start.

Typically this error happens when the installation of the underlying compiler is not present or is incomplete,
such as the proper files not having the correct permissions.


## **Error: Error: '_feature_' is not an element of the _target_ compiler's UnsupportedFeatures set**

This messages indicates two problems:
- the given feature is not supported in the compiler for the target language but is present in the program,
so the program will need to be revised to avoid this feature;
- the feature is not listed in the in-tool list of unsupported features.
The latter is a (minor) bug in the in-tool documentation. Please report this error message and the part of the
program provoking it to the Dafny team's [issue tracker](https://github.com/davidcok/dafny/issues).

## **Error: Opaque type ('_type_') with extern attribute requires a compile hint.  Expected {:extern compile_type_hint}**

<!-- TODO -->
_Documentation of extern and compile hints is in progress._

## **Error: Opaque type (_name_) cannot be compiled; perhaps make it a type synonym or use :extern.**
<!-- %check-run -->
```dafny
type T
```

[Opaque types](../DafnyRef/DafnyRef#sec-opaque-types) are declared like `type T`.
They can be useful in programs where the particular characteristics of the type
do not matter, such as in manipulating generic collections.
Such programs can be verified, but in order to be compiled to something executable, 
the type must be given an actual definition. 
If the definition really does not matter, just give it a definition like 
`type T = bool` or `type T = `int`.

Note that some properties of a type an be indicated using a [type charcteristic](../DafnyRef/DafnyRef#sec-type-characteristics).
For example, [`type T(00)` indicates that the type `T` is non-empty](../DafnyRef/DafnyRef#sec-nonempty-types).

## **Error: since yield parameters are initialized arbitrarily, iterators are forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
In an iterator, the yield parameters are initialized with arbitary values and can be read before 
they are set with actual values, so there is a bit of nondeterminism.
Consequently, iterators in general are not permitted along with `--enforce-determinism`.

## **Error: iterator _name_ has no body**

<!-- %check-run -->
```dafny
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
```

Programs containing iterators without bodies can be verified.
However, a body-less iterator is an unchecked assumption (even if it is ghost).
Consequently, like body-less functions and loops, dafny will not
compile a program containing an iterator without a body.
Furthermore, if the iterator is non-ghost, it cannot be executed if it does not have a body.

## **Error: The method '_name_' is not permitted as a main method (_reason_).**

<!-- %check-legacy %options -compile:2 -Main:mmm -->
```dafny
method mmm(i: int) {}
```

To create an executable program, the compiler needs to know which is the method 
to call to start the program, typically known as the 'main' method or main entry point. 
`dafny` chooses such a method based on a few rules (cf. [details in the Dafny User Guide](#sec-user-guide-main)).

But there are restrictions on which methods may be used as a main entry point.
Most importantly
- the method must take no input arguments or just one argument of type `seq<string>`
- it must not be ghost
- the method may be a class method, but then typically it is `static`

Most commonly and for clarity, the intended main method is marked with the attribute `{:main}`.

## **Error: Could not find the method named by the -Main option: _name_**

<!-- %check-legacy %options /compile:2 -Main:m -->
```dafny
class A { static method mm() {} }
```

In the legacy command-line syntax, the main method may be specified on the command-line.
When doing so, the name given must be a fully-qualified name.
For instance. a method `m` in a (top-level) module `M` is named `M.m` 
or in a class `C` in a module `M` is named `M.C.m`.
This error message indicates that dafny does not recognize the name given as the name of a method.

## **Error: More than one method is marked {:main}. First declaration appeared at _location_.**

<!-- %check-run -->
```dafny
method {:main} M(s: seq<string>) {}
method {:main} P() {}
```

When searching all the files in the program (including `include`d ones), dafny found more than one method marked
with `{:main}`. The error location is that of one of the methods and the error refers to another.
The tool does not know which one to use. 
The solution is to remove the `{:main}` attribute from all but one.

Note that entry points that are intended as unit tests can be marked with `{:test}` instead.

## **Error: This method marked {:main} is not permitted as a main method (_name_).**

<!-- %check-run -->
```dafny
method {:main} M(i: int) {}
```

Only some methods may be used as entry points and the one indicated may not.
The principal restrictions are these ([more details in the Dafny User Guide](#sec-user-guide-main)):
- the method must take no input arguments or just one argument of type `seq<string>`
- it must not be ghost
- the method may be a class method, but then typically it is `static`

## **Error: More than one method is declared as 'Main'. First declaration appeared at _location_.**

<!-- %check-run -->
```dafny
method Main(s: seq<string>) {}
class A {
  static method Main() {}
}
```

In the absence of any `{:main}` attributes, dafny chooses a method named `Main` as the main entry point.
When searching all the files in the program (including `include`d ones), dafny found more than one method named `Main`.
The error location is that of one of the methods and the error text refers to another.
The solution is to mark one of them as `{:main}`.

Note that entry points that are intended as unit tests can be marked with `{:test}` instead.

## **Error: This method 'Main' is not permitted as a main method (_reason_).**

<!-- %check-run -->
```dafny
method Main(i: int) {}
```

If dafny finds no methods marked `{:main}`, it then looks for a method named `Main`
to use as the starting point for the program.
This error occurs if the `Main` method that is found
does not qualify as a main entry point because it violates one or more of the [rules](#sec-user-guide-main),
as given by the reason in the error message.

## **Error: Function _name_ has no body**

<!-- %check-run -->
```dafny
function f(): int
```

The given function has no body, which is OK for verification, but not OK for compilation 
--- the compiler does not know what content to give it.
Even ghost functions must have bodies because body-less ghost functions are a form of unchecked assumptions.

## **Error: Function _name_ must be compiled to use the {:test} attribute**

<!-- %check-run -->
```dafny
function {:test} f(): int { 42 }
```

Only compiled functions and methods may be tested using the `dafny test` command, 
which tests everything marked with `{:test}`.
However this function is a ghost function, and consequently cannot be tested during execution.
If you want the function to be compiled,
declare the function as a `function` instead of `ghost function` in Dafny 4 
or as `function method` instead of `function` in Dafny 3.

## **Error: Method _name_ is annotated with :synthesize but is not static, has a body, or does not return anything**

<!-- TODO: Need example? -->

The `{:synthesize}` attribute is an experimental attribute used to create 
a mock object for methods that do not have bodies.
It is currently only available for compiling to C# and in conjunction with the Moq library.
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.

## **Error: Method _name_ has no body**

<!-- %check-run -->
```dafny
method m()
```

To be part of a compiled program, each method must have a body.
Ghost methods are the equivalent of unchecked assumptions
so they too must have bodies.

## **Error: _kind_ '_name_' is marked as :handle, so all the traits it extends must be marked as :handle as well: _trait_**

<!-- TODO -->
_The documentation of the {:handle} attribute is in progress._

## **Error: _kind '_name_' is marked as :handle, so all its non-static members must be ghost: _trait_**

<!-- TODO -->
_The documentation of the {:handle} attribute is in progress._


## **Error: an assume statement without an {:axiom} attribute cannot be compiled**

<!-- %check-run -->
```dafny
method m(x: int) {
  assume x > 0;
}
```

A method may be parsed and verified even if an [assume statement](../DafnyRef/DafnyRef#sec-assume-statement) is present. 
However, the assume statement is an explicit, unchecked assumption.
Dafny does not allow programs with unchecked assumptions, that is, incompletely verified programs, to be compiled.
The `{:axiom}` attribute can be used to tell Dafny that the assumption is to be considered an
externally verified _axiom_, with the program author taking responsibility for its validity.

If the assumption marked with `{:axiom}` is not actually valid, then the validity of the entire program is in question.

## **Error: a forall statement without a body cannot be compiled**

<!-- %check-run -->
```dafny
method m(a: array<int>) {
  forall x: int | x > 0 
  var y := 3;
}
```

A method may be parsed and verified even if a [forall statement](../DafnyRef/DafnyRef#sec-forall-statement) is missing a body. 
However, the body must be supplied before the program can be compiled,
even if the method is `ghost`. Body-less foralls in ghost methods are 
similar to unchecked assumptions.

## **Error: a loop without a body cannot be compiled**

<!-- %check-run -->
```dafny
ghost method m(i: int) {
  var x: int := i;
  while x > 0 
  x := 3;
}
```

A method may be parsed and verified even if a loop is missing a body. 
Note that a missing body is different than an empty body, which is just `{ }`.
However, the body must be supplied before the program can be compiled,
even if the method is `ghost`. 
Body-less loops in ghost methods are similar to unchecked assumptions.

## **Error: nondeterministic assignment forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m() {
  var x: int;
  x := *;
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'assign any legal value' (`... := *`) statement is not permitted with `--enforce-determinism`.

There are a few different forms of this kind of assignment:
- `x := *;`
- `x, y, z := 3, *, 42;`
- `forall i | 0 <= i < a.Length { a[i] := *; }`

## **Error: assign-such-that statement forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m() {
  var x: int;
  x :| x < 5;
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'assign any value that satisfies the predicate' (`:|`) statement is not permitted with `--enforce-determinism`,
even if there is only one such possible value.
(The tool does not try to determine whether there is just one value and
whether there is a reasonable way to compute it.)


## **Error: this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '_name_'**

<!-- TODO -->
_The documentation of this problem is in progress._

## **Error: nondeterministic if statement forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m() {
var y: int;
  if * { y:= 0; } else { y:= 1; }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'non-deterministic if' (`if *`) statement is not permitted with `--enforce-determinism`.

## **Error: binding if statement forbidden by the --enforce-determinism option**

<!-- TODO: a binding guard is a ghost statement so how could this situation ever happen? -->

<!-- %no-check %options --enforce-determinism -->
```dafny
method m(k: int) {
  var i := k;
  var y: int;
  if i :| i < 5 {  } else { y := 1; }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The [`if` with a binding guard](../DafnyRef/DafnyRef#sec-binding-guards) (`if ... :| `) checks that the 
given predicate is satisfiable by some value. If not, then the 'else' branch is executed;
but if so, the 'then' branch is executed with an arbitrary value that satisifies the predicate.
Because of this arbitrary selection, the if-with-binding-guard is not permitted with `--enforce-determinism`,
even if there is exactly one value that satisfies the predicate.
(The tool does not try to determine whether there is just one value and
whether there is a reasonable way to compute it.)

## **Error: case-based if statement forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m(k: int) {
  var i := k;
  if
  {
    case i >= 0 => i := i - 1;
    case i <= 0 => i := i + 1;
  }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The case-based if statement allows the case guards to be evaluated in an arbitrary order and
an arbitrary one of those found to be true is chosen to be executed.
Hence the case-based if is not permitted with `--enforce-determinism`.

To enforce a deterministic order to the evaluation, use a chain of if-then-else statements.


## **Error: nondeterministic loop forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m(b: bool) decreases * {
  while * 
    decreases *
  { }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'non-deterministic while' (`while *`) statement is not permitted with `--enforce-determinism`.

## **Error: case-based loop forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
method m(k: int) {
  var i := k;
  while 
    decreases if i < 0 then -i else i
  {
    case i > 0 => i := i - 1;
    case i < 0 => i := i + 1;
  }
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The case-based while statement allows the case guards to be evaluated in an arbitrary order and
an arbitrary one of those found to be true is chosen to be executed.
Hence the case-based loop is not permitted with `--enforce-determinism`.

To enforce a deterministic order to the evaluation, use a chain of if-then-else statements
or series of `if` statements in which the then-branch ends in a continue statement.

## **Error: compiler currently does not support assignments to more-than-6-dimensional arrays in forall statements**

<!-- TODO -->
_The documentation of this problem is in progress._

## **Error: modify statement without a body forbidden by the --enforce-determinism option**

<!-- %check-run %options --enforce-determinism -->
```dafny
class A { var j: int }

method m(k: int, o: A) 
  modifies o
{
  var i := k;
  modify o;
}
```

The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.

The [`modify` statement](../DafnyRef/DafnyRef#sec-modify-statement) allows the program to modify 
the state of the given objects in an arbitrary way
(though each field still has a legal value of its declared type).
Hence such a statement is not permitted with `--enforce-determinism`.

Note that a `modify` statement with a body is deprecated.


## **Error: this let-such-that expression is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '_name_'**

<!-- TODO -->
_The documentation of this problem is in progress._

## **Error: Comparison of a handle can only be with another handle**

<!-- TODO -->
_The documentation of the {:handle} attribute is in progress._

<!-- DafnyCore/Compilers/Synthesizer-Csharp.cs -->

## **Error: Post-conditions on function _function_ might be unsatisfied when synthesizing code for method _name_"

<!-- TODO: Example? Say more? Better documentation? -->

This message relates to mocking methods in C# with the Moq framework. 
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.

## **Error: Stubbing fields is not recommended (field _name_ of object _object_ inside method _method_)**

<!-- TODO: Example? Say more? Better documentation? -->

This message relates to mocking methods in C# with the Moq framework. 
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.

<!-- DafnyCore/Compilers/Compiler-Csharp.cs -->

# Errors specific to the C# compiler

## **Error: Expected arguments are {:dllimport dllName} or {:dllimport dllName, entryPoint} where dllName and entryPoint are strings: _argument_**

<!-- %check-run -->
```dafny
class A { 
  var Q: string
  method {:dllimport Q} mm()
}
```

A `{:dllimport}` attribute states that the method is implemented in the given dll.
Accordingly the attribute has an argument that names the dll and, possibly, the entry point within the dll.
Both of these arguments must be string literals.

## **Error: A _kind_ declared with :dllimport is not allowed a body: _name_**

<!-- %check-run -->
```dafny
class A { 
  method {:dllimport "Q.dll"} mm() {}
}
```

The `{:dllimport}` attribute indicates that the given method is implemented in the stated dll.
As such, the method should not have a body. The method should, though, have specifications,
as these specifications will be used to reason about the calls of the method elsewhere in the
Dafny program.

## **Error: A _kind_ declared with :dllimport must be static: _name_**

<!-- %check-run -->
```dafny
class A { 
  method {:dllimport "Q.dll"} mm()
}
```

Only static methods may be associated with dlls.

<!-- DafnyCore/Compilers/Compiler-go.cs -->
# Errors specific to the Go compiler

## **Error: Unsupported field _name_ in extern trait**

<!-- TODO -->
_Documentation of the Go compiler errors is in progress._

## **Error: Cannot convert from _type_ to _target-type_**

<!-- TODO - may not be feasible -->
_Documentation of the Go compiler errors is in progress._
