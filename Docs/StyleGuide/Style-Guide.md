This style guide provides coding conventions for the Dafny code.

*This documentation is still in progress. Please feel free to add any more suggestions if any.*

## Naming Convention
Any **variables** are named with `camelCase`.
```dafny
var minValue := 1;
var cipherMessage := "Hello World";
```

Any **lemmas**, **predicates**, **functions**, **methods**, **classes**, and **modules** are named with `PascalCase`.
```dafny
method FindIndex(arr: seq<int>, k: int)
    ...
```

Any static or global **constants** are named with `UPPERCASE_WITH_UNDERSCORES`.
```dafny
static const MONTHS_IN_A_YEAR := 12;
```

### Method Prefix
Avoid redundant names when variables or methods are in a class/module.
```dafny
class Integer {

    // The following method converts the given integer
    // to a string.
    //
    // this method name can be simplified to ToString()
    // so that the method call is Integer.ToString(i)
    // instead of Integer.IntegerToString(i).

    // YES
    method ToString(i: int) returns (s: string)
        ...

    // NO
    method IntegerToString(i: int) returns (s: string)
        ...
}
```

## Code Layout

### Braces
Dafny by default opens a new brace in the same line.
```dafny
module M() {
    ...
    method Met() {
        ...
    }
}
```
In case the method (or function, lemma, etc) signature is too long to fit in one line, or in case the signature has at
least one specification clause, the new brace goes to the new line.

```dafny
module M() {
    ...
    method Met(i: int) returns (j: int)
        requires i % 2 == 0
        ensures j > 10
    {
        ...
    }
}
```

This applies to every scope: `module`, `class`, `predicate`, `if`, `while`, and more.

### Imports
Import the modules with `opened` to avoid typing a full module name each time a method is invoked.
```dafny
import opened StandardLibrary
...
```

When there are more than two modules with the same method name, specify the name of the module during method invocation.

```dafny
import opened MyModule
import opened YourModule
...
method MyMethod() {
    MyModule.foo();
    YourModule.foo();
}
```

In case typing the full module name is cumbersome, import it with a shorthanded name.

```dafny
import M = MyModuleWithACumbersomeName
import Y = YourModuleWithACumbersomeName
...
method MyMethod() {
    M.foo();
    Y.foo();
}
```

Common imports, such as `StandardLibrary` and `Native`, should be grouped together, followed by custom module imports
with a blank line in-between.

```dafny
import opened StandardLibrary
import opened Native

import opened Donut
import Coffee
```

## Indentation and Line Breaks

### Tabs or Spaces?
Spaces are preferred over tabs. Tabs should only be used to remain consistent with the existing code with tabs.

Use 4 spaces for each indentation.

### Maximum Character Limit
Although there is no strict requirement, it is generally recommended to have maximum of 120 characters in each line.

### Functions, Methods, Predicates, and Lemmas
Every Dafny method has the following signature.
```dafny
method {:<attributes>} MethodName(param1: Type, param2: Type) returns (ret: Type)
    decreases param1
    requires P()
    modifies param2
    ensures Q()
```

When possible, put MethodName and `returns` statement in the same line, as the keyword `returns` is distinct from other
method specification clauses, such as `modifies`, `requires`, `ensures`, and `decreases`, which can be mixed in any
order (although not recommended for readability), while `returns` should always be right after the parameter
definitions. Each method specification clause should be in a separate line.

In case the Method signature is too long, we can break it down.
```dafny
method {:<attributes>} MethodName(param1: Type, param2: Type,
        param3: Type, param4: Type, param5: Type)
    returns (ret1: Type, ret2: Type, ret3: Type, ret4: Type,
        ret5: Type)
    decreases param1
    requires P1()
    requires P2()
    requires P3()
    modifies param2
    modifies param3
    ensures Q1()
    ensures Q2()
```

Multiple `requires` or `ensures` can be combined into one:
```dafny
requires
    P1() &&
    P2() &&
    P3()
```
The same rules apply to `function`, `predicate`, and `lemma` definitions.

## Things to Avoid

### Parenthesis

In a lot of cases, Dafny does not require parentheses around expressions. Here are some examples.

* If-Else-While Statements
```dafny
// YES
var i := 1;
while i < 10 {
    ...
    if 1 < i {
        ...
    }
    ...
}

// NO
var i := 1;
while (i < 10) {
    ...
    if (1 < i) {
        ...
    }
    ...
}
```

* Simple Boolean/Arithmetic Expressions
```dafny
// YES
method Collatz(num: nat)
    decreases *
{
    var n := num;
    while 1 < n
        decreases *
    { 
        n := if n % 2 == 0 then n / 2 else n * 3 + 1;
    }
}

// NO
method Collatz(num: nat)
    decreases *
{
    var n := num;
    while (1 < n) // unnecessary parentheses
        decreases *
    { 
        n := if ((n % 2) == 0) then (n / 2) else ((n * 3) + 1); // unnecessary parentheses
    }
}
```
### Whitespaces

Avoid unnecessary whitespaces inside expressions.

#### Type Declaration
Type declaration should have a form of `variableName: variableType`.
```dafny
// YES
var i: int := 1;
class {:extern} Util {
    var {:extern} Exception: System.String
}

// NO
var i : int := 1; // unnecessary whitespaces
class {:extern} Util {
    var {:extern} Exception : System.String // unnecessary whitespaces
}
```

#### Function, Method, Predicate, and Lemma Declaration
The `function`, `method`, `predicate`, and `lemma` definitions should have a form of
`FunctionName(parameterName: parameterType, ...)`.

```dafny
// YES
function method Foo<int>(i: int): int

// NO
function method Foo<int> (i : int) : int // unnecessary whitespaces
```

Avoid too little or too many whitespaces that reduce the overall readability.

```dafny
// YES
lemma MyLemma<A, B>(x: seq<seq<A>>, y: B) {
    ...
}

// NO
lemma MyLemma <A,B> ( x : seq<seq<A>> , y :B){
    ...
}
```

## Recommendations
This section describes a few recommendations that can help make code more readable and easy to follow, although not
strictly enforced.

### Externs
Try to name them the same in Dafny and C# whenever possible, so that in Dafny we only have to write `{:extern}`, not
`{:extern "<name>"}`.

### Things to Consider
Ask these questions before designing / implementing a program in Dafny.
* Is this variable name / function name `X` a good name?
* Does it make sense that this method `M` is in module `X`? Shouldn't it be in module `Y` instead?
* Does the definition `X` belong to the file `Y.dfy`?
* Is `X.dfy` a good filename?