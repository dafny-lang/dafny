This style guide provides coding conventions for the Dafny code.

*This documentation is still in progress. Please feel free to add any more suggestions if any.*

## Naming Convention
Any **variables** are named with `camelCase`.
```dafny
var minValue := 1;
var cipherMessage := "Hello World";
```

Any **lemmas**, **predicates**, **functions**, **methods**, **classes**, **modules**, **datatypes**, and **newtypes**
are named with `PascalCase`.
```dafny
method FindIndex(arr: seq<int>, k: int)
    ...
```

Any static or global **constants** are named with `UPPERCASE_WITH_UNDERSCORES`.
```dafny
static const MONTHS_IN_A_YEAR := 12
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
Opening braces go on the same line by default.
```dafny
module M {
    ...
    method Met() {
        ...
    }
}
```
In case the method (or function, lemma, etc) signature is too long to fit in one line, or in case the signature has at
least one specification clause, the opening brace goes on a new line.

```dafny
module M {
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

By default, import modules without opening them.
```dafny
import Coffee
...
```

However, if some members of a module are used very frequently, import it using `opened`:
```dafny
import opened Donut
...
```
When a file uses two modules, and both of them define a method of the same name, do not import them `opened`.
```dafny
import MyModule
import YourModule
...
method MyMethod() {
    MyModule.foo();
    YourModule.foo();
}
```

In this case, if you want to shorten their name, import them with a shorthand name.
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

Although not required, it's recommended to keep the order of `import`s and `include`s alphabetically, except when it
makes more sense to group them logically.

## Indentation and Line Breaks

### Tabs or Spaces?
Spaces are preferred over tabs. Tabs should only be used to remain consistent with the existing code with tabs.

Use 2 spaces for each indentation.

### Maximum Character Limit
Although there is no strict requirement, it is generally recommended to have a maximum of 120 characters per line.

### Newlines
Use newlines between sequential **functions**, **methods**, **predicates**, and **lemmas** to increase readability.

End each file with a newline.

### Functions, Methods, Predicates, and Lemmas
Every Dafny method has the following signature.
```dafny
method {:<attributes>} MethodName(param1: Type, param2: Type) returns (ret: Type)
    requires P()
    modifies param2
    ensures Q()
    decreases param1
```

When possible, put `MethodName` and the `returns` statement on the same line, as the keyword `returns` is distinct from
other method specification clauses, such as `requires`, `modifies`, `ensures`, and `decreases`, which should appear in
this order. Each method specification clause should be on a separate line, indented.

In case the Method signature is too long, we can break it down.
```dafny
method {:<attributes>} MethodName(param1: Type, param2: Type,
        param3: Type, param4: Type, param5: Type)
    returns (ret1: Type, ret2: Type, ret3: Type, ret4: Type,
        ret5: Type)
    requires P1()
    requires P2()
    requires P3()
    modifies param2
    modifies param3
    ensures Q1()
    ensures Q2()
    decreases param1
```

Multiple `requires` or `ensures` can be combined into one:
```dafny
requires
    && P1()
    && P2()
    && P3()
```
The same rules apply to `function`, `predicate`, and `lemma` definitions.

## Things to Avoid

### Parentheses

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

* Statements That Take Expression Arguments
```dafny
// YES
assert x < 100;
print x;

// NO
assert(x < 100);
print(x);
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
### Whitespace

Avoid unnecessary whitespace inside expressions.

#### Type Declaration
A type declaration should have a form of `variableName: variableType`.
```dafny
// YES
const one: int := 1
class {:extern} Util {
    var {:extern} Exception: System.String
}

// NO
const one : int := 1 // unnecessary whitespace
class {:extern} Util {
    var {:extern} Exception : System.String // unnecessary whitespace
}
```

Note, if the type can be inferred by Dafny, leave it out, unless you think it provides
useful documentation in the program. So, constant `one` above is better declared as
```dafny
const one := 1
```

#### Function, Method, Predicate, and Lemma Declaration
The `function`, `method`, `predicate`, and `lemma` definitions should have a form of
`FunctionName(parameterName: parameterType, ...)`.

```dafny
// YES
function method Foo<int>(i: int): int

// NO
function method Foo<int> (i : int) : int // unnecessary whitespace
```

Avoid too little or too many whitespace that reduce the overall readability.

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
Try to name them the same in Dafny and the target language (e.g. C#, Java, etc) whenever possible, so that in Dafny we
only have to write `{:extern}`, not `{:extern "<name>"}`.

### Things to Consider
Ask these questions before designing / implementing a program in Dafny.
* Is this variable name / function name `X` a good name?
* Does it make sense that this method `M` is in module `X`? Shouldn't it be in module `Y` instead?
* Does the definition `X` belong to the file `Y.dfy`?
* Is `X.dfy` a good filename?
