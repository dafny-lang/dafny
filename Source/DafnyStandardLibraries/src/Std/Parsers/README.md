# Verified Parser Combinators

Parser combinators in Dafny, inspired from the model of [Meijer&Hutton 1996](https://cspages.ucalgary.ca/~robin/class/521/class-handout.pdf#page=282).

This library offers two styles of functional parser combinators.

- The first parsers style is a synonym for `seq<char> -> ParseResult<Result>` that supports monadic styles, is straightforward to use, but results in lots of closing parentheses.

- The second parsers style is a datatype wrapper around the first style, which enable to define functions as infix or suffix operations, which makes parsers sometimes easier to read and helps decreasing nesting.

## Library usage

The tutorial in [`Tutorial.dfy`](../../../examples/Parsers/Tutorial.dfy) shows how to import the library, call the two styles of parser API, apply the parser to a string, and also use `PrintFailure` to pretty print the failure along with the line and column where it occurred.

To view a full example of how to use the parser combinator library,
especially how to define a recursive parser that is guaranteed to terminate,
please refer to the file [`PolynomialParser.dfy`](../../../examples/Parsers/PolynomialParser.dfy).

As a quick walkthrough, here is a test to parse a Tic-tac-toe grid using parser combinators.

<!-- %check-run-output -->
```dafny
module M {
  import opened Std.Parsers.StringParsers

  /** Tic tac toe using string parsers */
  method Main() {
    var cell := OrSeq([
      String("O"), String("X"), String(" ")
    ]);
    var v := String("|");
    var row := Concat(cell, ConcatKeepRight(v, Concat(cell, ConcatKeepRight(v, cell))));
    var sep := String("\n-+-+-\n");
    var grid := 
      Concat(row, ConcatKeepRight(sep, Concat(row, ConcatKeepRight(sep, row))));
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    var r := Apply(grid, input);
    expect r.IsFailure();
    print FailureToString(input, r);
  }
}
```

it displays the following:

<!-- %check-expect -->
```expect
Error:
5: P| |O
   ^
expected 'O', or
expected 'X', or
expected ' '
```

Here is the equivalent using parser builders, abbreviated version:

<!-- %check-verify -->
```dafny
module M {
  import opened Std.Parsers.StringBuilders

  /** Tic tac toe using string parser builders */
  method Main() {
    var cell := O([ S("O"), S("X"), S(" ") ]);
    var v := S("|");
    var row := cell.I_e(v).I_I(cell).I_e(v).I_I(cell);   // I stands for included, e for excluded
    var sep := S("\n-+-+-\n");
    var grid := row.I_e(sep).I_I(row).I_e(sep).I_I(row);
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    var r := grid.Apply(input);
    expect r.IsFailure();
    print FailureToString(input, r);
  }
}
```

If you prefer, you can still write a parser using the verbose names of the builders. Some think it is distracting to have long names when all that matters is
the described parser, but some others believe it's easier to understand. You choose:

<!-- %check-verify -->
```dafny
module M {
  import opened Std.Parsers.StringBuilders

  /** Tic tac toe using string parser builders */
  method Main() {
    var cell := Or([ String("O"), String("X"), String(" ") ]);
    var v := String("|");
    var row := cell.ConcatKeepRight(v).Concat(cell).ConcatKeepLeft(v).Concat(cell);
    var sep := String("\n-+-+-\n");
    var grid := row.I_e(sep).I_I(row).I_e(sep).I_I(row);
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
    var r := grid.Apply(input);
    expect r.IsFailure();
    print FailureToString(input, r);
  }
}
```



The output is the same as before.

## What is verified?

Despite combinators enabling to define mutually recursive parsers (`RecursiveMap`, `Recursive`), Dafny will always check termination. When using recursive combinators, termination is checked at run-time so it does not prevent quick prototyping and iterations, and error messages about non-termination are always precise (either the ordering, or the progression).

This library offers a predicate on parsers of the first style `Valid()`, which
indicates that such parsers will never raise a fatal result, and will always return a
string that is suffix of the string they are given as input. Many combinators have
a proof that, if their inputs are Valid(), then their result is Valid().
Checking validity statically could help design parsers that do even less checks at run-time, but it has not been developed in this library.

## Relationship to JSON parsers

The JSON parser of the standard library is very specialized and the type of the parsers combinators it is using is actually a subset type.
Subset types are known to be a source of proof brittleness,
so this library design is not using subset types.
That said, it is possible to create an adapter around a JSON parser to make it a parser of this library.

# Caveats

- The `Rec()` parser combinator (`Recursive()` if not using builders) will consume stack and, in programming languages that have a finite amount of stack, programs can get out of memory. Prefer `Rep` and `RepSeq` as much as possible as they are tail-recursive by default. There is also another version `RecNoStack()` that does exactly what `Rec()` does but requires the parser combinator to be provided by continuations. SEee the example [`SmtParser.dfy`](../../../examples/Parsers/SmtParser.dfy) on how to use `RecNoStack()`.

# Implementation notes

The module hierarchy is as follow:

<!-- %no-check -->
```dafny
abstract module Std.Parsers.Core {
  type C
}
module Std.Parsers.StringCore refines Std.Parsers.Core {
  type C: Char
}

abstract module Std.Parsers.Builders {
  import P: Std.Parsers.Core
}
module Std.Parsers.String.Builders refines  {
  import P = StringParsers
}
```


## FAQ: 

### What properties can we use it to prove?

* You get for free that parsers terminate, at worst with a run-time parser failure result "no progress and got back to the same function".
* You can actually prove the absence of certain kinds of errors. There are several lemmas that propagate this property through parsers combinators. Proving this on the recursive cases is also possible but not obvious.
* You can prove the equivalence between various combinations of parser combinators (e.g. Bind/Succeed == Map)
* You can use these parser combinators as a specification for optimized methods that perform the same task but perhaps with a different representation, e.g. array and position instead of sequences of characters.

### What are fatal errors?

`ParseResult.Failure` has a `.level` field which is almost always `FailureLevel.Recoverable`. It is however `FailureLevel.Fatal` in the two following cases:
- A parser returned more input than it had at the beginning
- A `RecMap` construct used a parser that was not defined.

Fatal errors are not to be recovered from and automatically bubble up the parser combinator stack. For example, for the parser combinator `a.?()`, if `a` fails with a recoverable failure, normally it returns a `None`, but in the presence of a fatal error it will return the same fatal error.

Like other kinds of parse result failures, it's also possible to prove the absence of fatal errors.

### How does it backtrack?

There are several ways parsers can backtrack in the current design.

* A parser not consuming any input when returning a recoverable error can be ignored for combinators with alternatives like `Or`, `Maybe`, `If` or `ZeroOrMore` (respectively `O([...])`, `.?()`, `.If()` and `.Rep()` if using builders)
* It's possible to transform a parser to not commit any input when it fails (except fatal errors) via the combinator `?(...)` (`.??()` if using builders). This means the failure will have the same input as previously given, nothing is consumed, making it possible for surrounding combinators to explore alternatives.
* The combinators `BindResult`, a generalization of the `Bind` combinator when considering parsers as monads, lets the user decides whether to continue on the left parser's remaining input or start from the beginning.

### My parser is not parsing my input string but should. How to figure out what's wrong?

See [DEBUGGING.md](DEBUGGING.md) for a step-by-step walkthrough on how to debug your parsers effectively.

### What are the verbose names for the parser builders? Why are there abbreviated and verbose versions?


This table shows the abbreviated and verbose equivalents of parser combinators in the `Std.Parsers.ParserBuilders` module.

| Abbreviated Syntax | Verbose Equivalent |
|-------------------|-------------------|
| `a.?()`           | `a.Option()`      |
| `a.??()`          | `a.FailureResetsInput()` |
| `a.e_I(b)`        | `a.ConcatKeepRight(b)` |
| `a.I_e(b)`        | `a.ConcatKeepLeft(b)` |
| `a.I_I(b)`        | `a.Concat(b)` |
| `a.M(f)`          | `a.Map(f)` |
| `a.M2(unfolder, f)` | `a.Map2(unfolder, f)` |
| `a.M3(unfolder, f)` | `a.Map3(unfolder, f)` |
| `MId(r)`          | `MapIdentity(r)` |
| `a.Rep()`         | `a.Repeat()` |
| `a.RepFold(init, combine)` | `a.RepeatFold(init, combine)` |
| `a.RepSep(separator)` | `a.RepeatSeparator(separator)` |
| `a.RepMerge(merger)` | `a.RepeatMerge(merger)` |
| `a.RepSepMerge(separator, merger)` | `a.RepeatSeparatorMerge(separator, merger)` |
| `a.Rep1()`        | `a.RepeatAtLeastOnce()` |
| `O([a, b, ...])` | `Or([a, b, ...])` |
| `EOS`             | `EndOfString` |
| `Rec(underlying)` | `Recursive(underlying)` |
| `RecNoStack(underlying)` | `RecursiveNoStack(underlying)` |

Additionally, the emodule `Std.Parsers.Stringbuilders` inherits from these definitions and has two more abbreviated parser definitions:

| Abbreviated Syntax | Verbose Equivalent |
|-------------------|-------------------|
| `S("constant")`   | `String("constant")` |
| `WS`              | `Whitespace` |

The abbreviated syntax is designed to reduce visual noise in complex parser definitions, making the parser logic more readable by visually separating the parser logic (constants, strings, and custom parser calls) from the underlying combinator machinery. It's a matter of taste.