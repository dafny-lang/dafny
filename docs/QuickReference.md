<p></p>
<link rel="stylesheet" href="assets/main.css">

# Dafny Quick Reference

This page illustrates many of the most common language features in Dafny.  In order to get you started more quickly, the descriptions here are simplified&#8211;this page is not the language reference.  For example, this page does not go into modules, iterators, or refinement, which you won&#8217;t need until you write larger or more advanced programs in Dafny.

## Programs

At the top level, a Dafny program (stored as a file with extension .dfy) is a set of declarations.
The declarations introduce _types_, _methods_, and _functions_, where the order of introduction is irrelevant.
These user-defined types include _classes_ and _inductive datatypes_.
The classes themselves also contain a set of declarations, introducing _fields_, methods, and functions.
If the program contains a parameter-less method called Main, then execution of the compiled program starts there, but it is not necessary to have a main method to do verification.

Comments start with // and go to the end of the line, or start with /* and end with */ and can be nested.

## Fields

In a class, a field x of some type T is declared as: `var x: T`

Unlike for local variables and bound variables, the type is required and will not be inferred.
The field can be declared to be a ghost (that is, used for specification and not execution) field by preceding the declaration with the keyword `ghost`.
Dafny's types include `bool` for booleans, `int` for mathematical (that is, unbounded) integers, `string` for strings, user-defined classes and inductive datatypes, `set<T>` for a finite mathematical (immutable) set of `T` values (where `T` is a type), and `seq<T>` for a mathematical (immutable) sequence of `T` values.
In addition, there are array types (which are like predefined "class" types) of one and more dimensions, written `array<T>`, `array2<T>`, `array3<T>`, etc.
The type `object` is a supertype of all class types, that is, an object denotes any reference, including `null`.
Another useful type is `nat`, which denotes a subrange of `int`, namely the non-negative integers.

## Methods

A method declaration (either at the top level or inside a class) has the form:
<pre>
method M(a: A, b: B, c: C) returns (x: X, y: Y, z: Y)
  requires Pre
  modifies Frame
  ensures Post
  decreases TerminationMetric
{
  Body
}
</pre>
where a, b, c are the method's in-parameters,
x, y, z are the method's out-parameters,
Pre is a boolean expression denoting the method's precondition,
Frame denotes a set of objects whose fields may be updated by the method,
Post is a boolean expression denoting the method's postcondition,
TerminationMetric is the method's variant function,
and Body is a statement that implements the method.
Frame can be a list of expressions, each of which is a set of objects or a single object, the latter standing for the singleton set consisting of that one object.
The method's frame is the union of these sets, plus the set of objects allocated by the method body.
For example, if c and d are parameters of a class type C, then each line of
<pre>
  modifies {c, d}
  modifies {c} + {d}
  modifies c, {d}
  modifies c, d
</pre>
means the same thing.

If omitted, the pre- and postconditions default to true and the frame defaults to the empty set.
The variant function is a list of expressions, denoting the lexicographic tuple consisting of the given expressions followed implicitly by “top” elements.
If omitted, Dafny will guess a variant function for the method, usually the lexicographic tuple that starts with the list of the method's in-parameters.
The Dafny IDE will show the guess in a tooltip.

A method can be declared as ghost (specification-only) by preceding the declaration with the keyword `ghost`.
By default, a method in a class has an implicit receiver parameter, `this`.
This parameter can be removed by preceding the method declaration with the keyword `static`.
A static method `M` in a class `C` can be invoked by `C.M(...)`.

In a class, a method can be declared to be a constructor method by replacing the keyword `method` with the keyword `constructor`.
A constructor can only be called at the time an object is allocated (see object-creation examples below), and for a class that contains one or more constructors, object creation must be done in conjunction with a call to a constructor.
Ordinarily, a method has a name, of course, but a class is allowed to have one constructor without a name&#8211;an _anonymous constructor_&#8211;like this:
<pre>
  constructor (n: int)
    modifies this
  {
    Body
  }
</pre>

Sometimes, methods are used as lemmas.
This can be made clearer in the program text by declaring the method with `lemma` instead of `method`.

Here is an example method that takes 3 integers as in-parameters and returns these in 3 out-parameters in sorted order:
```
method Sort(a: int, b: int, c: int) returns (x: int, y: int, z: int)
  ensures x <= y <= z && multiset{a, b, c} == multiset{x, y, z}
{
  x, y, z := a, b, c;
  if z < y {
    y, z := z, y;
  }
  if y < x {
    x, y := y, x;
  }
  if z < y {
    y, z := z, y;
  }
}
```

## Functions

A function declaration (either at the top level or inside a class) has the form:
```
function F(a: A, b: B, c: C): T
  requires Pre
  reads Frame
  ensures Post
  decreases TerminationMetric
{
  Body
}
```

where a, b, c are the method's parameters, T is the type of the function's result,
Pre is a boolean expression denoting the function's precondition,
Frame denotes a set of objects whose fields the function body may depend on,
Post is a boolean expression denoting the function's postcondition,
TerminationMetric is the function's variant function,
and Body is an expression that defines the function.

The precondition allows a function to be partial, that is, the precondition says when the function is defined (and Dafny will verify that every use of the function meets the precondition).
The postcondition is usually not needed, since the body of the function gives the full definition.
However, the postcondition can be a convenient place to declare properties of the function that may require an inductive proof to establish.
For example:
```
function Factorial(n: int): int
  requires 0 <= n
  ensures 1 <= Factorial(n)
{
  if n == 0 then 1 else Factorial(n-1) * n
}
```
says that the result of `Factorial` is always positive, which Dafny verifies inductively from the function body.
To refer to the function's result in the postcondition, use the name of the function itself, as shown in the example.

By default, a function is ghost, and cannot be called from executable (non-ghost) code. To make it non-ghost, replace the keyword `function` with the keyword phrase `function method`.
A function that returns a boolean can be declared with the keyword `predicate` and then eliding the colon and return type.

If a function or method is declared as a member of a type (like a `class`), then it has an implicit receiver parameter, `this`.
This parameter can be removed by preceding the declaration with the keyword `static`. A static function `F` in a class `C` can be invoked by `C.F(...)`.
This is a convenient way to declare a number of helper functions in a separate class.

## Classes

A class is defined as follows:
```
class C {
  // member declarations go here
}
```

where the members of the class (fields, methods, and functions) are defined (as described above) inside the curly braces.
## Datatypes

An inductive datatype is a type whose values are created using a fixed set of constructors.
A datatype `Tree` with constructors `Leaf` and `Node` is declared as follows:
```
datatype Tree = Leaf | Node(Tree, int, Tree)
```
The first constructor is optionally preceded by a vertical bar.

The constructors are separated by vertical bars.
Parameter-less constructors need not use parentheses, as is shown here for `Leaf`.

For each constructor `Ct`, the datatype implicitly declares a boolean member `Ct?`, which returns true for those values that have been constructed using Ct.
For example, after the code snippet:
<pre>var t0 := Leaf; var t1 := Node(t0, 5, t0);</pre>

the expression `t1.Node?` evaluates to `true` and `t0.Node?` evaluates to `false`.
Two datatype values are equal if they have been created using the same constructor and the same parameters to that constructor.
Therefore, for parameter-less constructors like `Leaf`, `t.Leaf?` gives the same result as `t == Leaf`.

A constructor can optionally declare a destructor for any of its parameters, which is done by introducing a name for the parameter.
For example, if `Tree` were declared as:
<pre>datatype Tree = Leaf | Node(left: Tree, data: int, right: Tree)</pre>

then `t1.data == 5` and `t1.left == t0` hold after the code snippet above.

## Generics

Dafny supports type parameters.
That is, any type, method, and function can have type parameters.
These are declared in angle brackets after the name of what is being declared. For example:
```
class MyMultiset<T> {
  /*...*/
}

datatype Tree<T> = Leaf | Node(Tree<T>, T, Tree<T>)

method Find<T>(key: T, collection: Tree<T>) {
  /*...*/
}

function IfThenElse<T>(b: bool, x: T, y: T): T {
  /*...*/
}
```

## Statements

Here are examples of the most common statements in Dafny.
```
  var LocalVariables := ExprList;

  Lvalues := ExprList;

  assert BoolExpr;

  print ExprList;

  if BoolExpr0 {
    Stmts0
  } else if BoolExpr1 {
    Stmts1
  } else {
    Stmts2
  }

  while BoolExpr
    invariant Inv
    modifies Frame
    decreases Rank
  {
    Stmts
  }

  match Expr {
    case Empty => Stmts0
    case Node(l, d, r) => Stmts1
  }

  break;

  return;
```

The `var` statement introduces local variables (which are not allowed to shadow other variables declared inside the same set of most tightly enclosing curly braces).
Each variable can optionally be followed by `: T` for any type `T`, which explicitly gives the preceding variable the type `T` (rather than being inferred).
The ExprList with initial values is optional.
To declare the variables as ghost variables, precede the declaration with the keyword `ghost`.

The assignment statement assigns each right-hand side in ExprList to the corresponding left-hand side in Lvalues.
These assignments are performed in parallel (more to the point, all necessary reads occur before the writes), so the left-hand sides must denote distinct L-values.
Each right-hand side can be an expression or an object creation of one of the following forms:
```
  new T
  new T.Init(ExprList)
  new T(ExprList)
  new T[SizeExpr]
  new T[SizeExpr0, SizeExpr1]
```

The first form allocates an object of type `T`.
The second form additionally invokes an initialization method or constructor on the newly allocated object.
The third form shows how the syntax differs from the second form when the constructor called is anonymous.
The other forms show examples of array allocations, in particular a one- and a two-dimensional array of `T` values, respectively.

The entire right-hand side of an assignment can also be a method call, in which case the left-hand sides are the actual out-parameters (omitting the `:=` if there are no out-parameters).

The `assert` statement claims that the given expression evaluates to true (which is checked by the verifier).

The `print` statement outputs to standard output the values of the given print expressions.
Characters in strings can be escaped; for example, of interest for the print statement is that `\n` denotes a newline character inside a string.

The `if` statement is the usual one.
The example shows stringing together alternatives using `else if`.
The `else` branch is optional, as usual.

The `while` statement is the usual loop, where the `invariant` declaration gives a loop invariant,
the `modifies` clause restricts the modification frame of the loop,
and the `decreases` clause introduces a variant function for the loop.
By default, the loop invariant is true, the modification frame is the same as in the enclosing context (usually the `modifies` clause of the enclosing method), and the variant function is guessed from the loop guard.

The `match` statement evaluates the source Expr, an expression whose type is an inductive datatype, and then executes the case corresponding to which constructor was used to create the source datatype value, binding the constructor parameters to the given names.
If they are not needed to mark the end of the match statement, then the curly braces that surround the cases can be elided.

The `break` statement can be used to exit loops, and the `return` statement can be used to exit a method.

## Expressions

The expressions in Dafny are quite similar to those in Java-like languages. Here are some noteworthy differences.

In addition to the short-circuiting boolean operators `&&` (and) and `||` (or), Dafny has a short-circuiting implication operator `==>` and an if-and-only-if operator `<==>`.
As suggested by their widths, `<==>` has lower binding power than `==>`, which in turn has lower binding power than `&&` and `||`.

Dafny comparison expressions can be chaining, which means that comparisons "in the same direction" can be strung together. For example,
`0 <= i < j <= a.Length == N`

has the same meaning as:
`0 <= i && i < j && j <= a.Length && a.Length == N`

Note that boolean equality can be expressed using both `==` and `<==>`. There are two differences between these.
First, `==` has a higher binding power than `<==>`. Second, `==` is _chaining_ while `<==>` is _associative_.
That is, `a == b == c` is the same as `a == b && b == c`, whereas `a <==> b <==> c` is the same as `a <==> (b <==> c)`, which is also the same as `(a <==> b) <==> c`.

Operations on integers are the usual ones, except that `/` (integer division) and `%` (integer modulo) follow the Euclidean definition, which means that `%` always results in a non-negative number.
(Hence, when the first argument to `/` or `%` is negative, the result is different than what you get in C, Java, or C#, see <a href="http://en.wikipedia.org/wiki/Modulo_operation" target="_self">http://en.wikipedia.org/wiki/Modulo_operation</a>.)


Dafny expressions include universal and existential quantifiers, which have the form:
`forall x :: Expr` and `exists x :: Expr`, where `x` is a bound variable (which can be declared with an explicit type, as in `x: T`) and `Expr` is a boolean expression.

Operations on sets include `+` (union), `*` (intersection), and `-` (set difference), the set comparison operators `<` (proper subset), `<=` (subset), their duals `>` and `>=`, and `!!` (disjointness).
The expression `x in S` says that `x` is a member of set `S`, and `x !in S` is a convenient way of writing `!(x in S)`.

To make a set from some elements, enclose them in curly braces.
For example, `{x,y}` is the set consisting of `x` and `y` (which is a singleton set if `x == y`), `{x}` is the singleton set containing `x`, and `{}` is the empty set.


Operations on sequences include `+` (concatenation) and the comparison operators `<` (proper prefix) and `<=` (prefix).
Membership can be checked like for sets: `x in S` and `x !in S`.
The length of a sequence S is denoted `|S|`, and the elements of such a sequence have indices from 0 to less than `|S|`.
The expression `S[j]` denotes the element at index `j` of sequence `S`.
The expression `S[m..n]`, where `0 <= m <= n <= |S|`, returns a sequence whose elements are the `n-m` elements of `S` starting at index `m` (that is, from `S[m]`, `S[m+1]`, ... up to but not including `S[n]`).
The expression `S[m..]`; (often called "drop m") is the same as `S[m..|S|]`;, that is, it returns the sequence whose elements are all but the first `m` elements of `S`.
The expression `S[..n]`; (often called "take n") is the same as `S[0..n]`, that is, it returns the sequence that consists of the first n elements of S.

If `j` is a valid index into sequence `S`, then the expression `S[j := x]`; is the sequence that is like `S` except that it has `x` at index `j`.

Finally, to make a sequence from some elements, enclose them in square brackets.
For example, `[x,y]` is the sequence consisting of the two elements `x` and `y` such that `[x,y][0] == x` and `[x,y][1] == y`, `[x]` is the singleton sequence whose only element is `x`, and `[]` is the empty sequence.


The if-then-else expression has the form: `if BoolExpr then Expr0 else Expr1`

where Expr0 and Expr1 are any expressions of the same type.
Unlike the if statement, the if-then-else expression uses the `then` keyword, and must include an explicit `else` branch.


The `match` expression is analogous to the match statement and has the form:
```
match Expr { case Empty => Expr0 case Node(l, d, r) => Expr1 }
```

The curly braces can be used to mark the end of the match expression, but most commonly this is not needed and the curly braces can then be elided.
