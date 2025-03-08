# Verified Parser Combinators

Parser combinators in Dafny, inspired from the model (Meijer&Hutton 1996).

This library offers two styles of functional parser combinators.

- The first parsers style is a synonym for `seq<character> -> ParseResult<Result>` that supports monadic styles, is straightforward to use, but results in lots of closing parentheses.

- The second parsers style is a datatype wrapper around the first style, which enable to define functions as infix or suffixes, which makes parsers sometimes easier to read and helps decreasing nesting.

## Library usage

The tutorial in [`Tutorial.dfy`](../../../examples/Parsers/Tutorial.dfy) shows how to import the library call the two parsers style API, apply the parser to a string, and also use the PrintFailure to pretty print the failure along with the line/col where it occurred.

To view a full example of how to use the parser combinator library,
especially how to define a recursive parser that is guaranteed to terminate,
please refer to the files [`PolynomialParser.dfy`](../../../examples/Parsers/PolynomialParser.dfy) and [`PolynomialParserBuilder.dfy`](../../../examples/Parsers/PolynomialParserBuilder.dfy), which both parse polynomial expressions.

As a quick walkthrough, here is a test to parse a Tic-tac-toe grid using parser combinators.

```
method {:test} TestTicTacToe() {
  var x := OrSeq([
    String("O"), String("X"), String(" ")
  ]);
  var v := String("|");
  var row := Concat(x, ConcatR(v, Concat(x, ConcatR(v, x))));
  var sep := String("\n-+-+-\n");
  var grid := 
    Concat(row, ConcatR(sep, Concat(row, ConcatR(sep, row))));
  var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
  var r := grid(input);
  expect r.IsFailure();
  PrintFailure(input, r);
}
```

it displays the following:

```
Error:
5: P| |O
   ^
expected 'O', or
expected 'X', or
expected ' '
```

Here is the equivalent using parser builders:

```
method {:test} TestTicTacToe() {
  var x := O([ S("O"), S("X"), S(" ") ]);
  var v := S("|");
  var row := x.I_e(v).I_I(x).I_e(v).I_I(x);   // I stands for included, e for excluded
  var sep := S("\n-+-+-\n");
  var grid := row.I_e(sep).I_I(row).I_e(sep).I_I(row);
  var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
  var r := grid(input);
  expect r.IsFailure();
  PrintFailure(input, r);
}
```

## What is verified?

Despite combinators enabling to define mutually recursive parsers (`RecursiveMap`, `Recursive`), Dafny will always check termination. When using recursive combinators, termination is checked at run-time so it does not prevent quick prototyping and iterations, and error messages about non-termination are always precise (either the ordering, or the progression).

This library offers a predicate on parsers of the first style `Valid()`, which
indicates that such parsers will never raise a fatal result, and will always return a
string that is suffix of the string they are given as input. Many combinators have
a proof that, if their inputs are Valid(), then their result is Valid().
Checking validity statically could help design parsers that do even less checks at run-time, but it has not been developed in this library.

This library also offers a dual type to parser, named Displayer, which is `(Result, seq<character>) -> seq<character>`. It only defines the dual of the Concat parser combinator and proves the roundtrip to be the identity. Because Dafny does not offer
compilable predicate to check that a datatype constructor is included in another one,
writing combinators for this kind of parser dual is difficult.

## Relationship to JSON parsers

The JSON parser is very specialized and the type of the parsers combinators it is using is actually a subset type.
Subset types are known to be a source of proof brittleness,
so this library design is not using subset types.
That said, it is possible to create an adapter around a JSON parser to make it a parser of this library.

# Caveats

- Recursive parsers will consume stack and, in programming languages that have a finite amount of stack, programs can get out of memory. Prefer `Rep` and `RepSeq` as much as possible as they are tail-recursive.

# Implementation notes

The module hierarchy is as follow:

```
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

* You get for free that parsers terminate, at worst with a run-time "fatal" parser result "no progress and got back to the same function"
* You can actually prove the absence of fatal errors. There are several lemmas that propagate this property through parsers combinators. Proving this on the recursive cases is also possible but not obvious.
* You can prove the equivalence between various combinations of parser combinators (e.g. Bind/Succed == Map)
* You can use these parser combinators as a specification for optimized methods that perform the same task but perhaps with a different representation, e.g. array and position instead of sequences of characters.

### How does it backtrack? Like Parsec (fails if tokens are consumed)?

There are several ways parsers can backtrack in the current design.

* A parser not consuming any input when returning a recoverable error can be ignored for combinators with alternatives like `Or`, `Maybe`, `If` or `ZeroOrMore` (respectively `O([...])`, `.?()`, `.If()` and `.Rep()` if using builders)
* It's possible to transform a parser to not consume any input when it fails (except fatal errors) via the combinator `?(...)` (`.??()` if using builders). This means the failure will have the same input as previously given, making it possible for surrounding combinators to explore alternatives.
* The combinators `BindResult`, a generalization of the `Bind` combinator when considering parsers as monads, lets the user decides whether to continue on the left parser's remaining input or start from the beginning.

### My parser is not parsing my input string but should. How to figure out what's wrong?

Developing parsers can be pretty challenging sometimes. Fortunately, this library provides tools to debug parsers.

Let's say you develop the following parser to parse a list of space-separated numbers on the command line:

```
import opened Std.Parsers.StringBuilders

const pDoc :=
  WS.e_I(Nat)   // Space then nat
  .Rep()        // Zero or more times
  .I_e(WS)      // Then space
  .End()        // Then end

method Main() {
  var input := " 1 2 3 4 ";
  var result := pDoc.apply(input);
  match result {
    case Success(value, remaining) =>
      print value, "\n";
    case Failure(error, sub_data) =>
      var failureMessage :=
        FailureToString(input, result);
      print failureMessage;
  }
}
```

Note that `.Rep()` is a parser combinator that repeats the parser to its left until it fails (its loop body), at which point it should emit the sequence of parsed elements.
You see the unexpected result:
```
Error:
1:  1 2 3 4
            ^
expected a digit
```

It's expecting a digit where it should have just accepted the end of the string. To figure out what went wrong,
let's first define two debug functions like below - they can't be defined in the library because they have print effects. You could change the type of the output of string if you were to customize them.
```
function di(
  name: string, input: string): string {
  input
} by method {
  print DebugSummaryInput(name, input);
  return input;
}

function de<K>(
  name: string,
  di_result: string,
  result: P.ParseResult<K>): () {
  ()
} by method {
  PrintDebugSummaryOutput(name, di_result, result);
  return ();
}
```

Now you can use the `.Debug("some name", di, de)` suffix on any parser builder to debug its input and parse result. Let's use it on our example just before parsing the end
```
const pDoc := 
  WS.e_I(Nat)
  .Rep()
  .I_e(WS)
  .Debug("End", di, de)
  .End
```

Running this parser on `" 1 2 3 4 "` displays the following trace.

```
> End: 9 " "
< End: 9 " "
| R: 0 "EOS"
| Was committed
| Error:
| 1:  1 2 3 4
|             ^
| expected a digit
|
```

This trace indicates that the parser to the left of `.Debug` started to parse when there were 9 characters left (the entire string) and the first character was a space.
When it finished (displaying the same length of 9 and first space character)
it says that the remaining to parse has length 0 and "starts" with the end of string.
The "was committed" message simply indicates that the parser considers anything between 0 and 9 as having been correctly parsed and 9 > 0;

Now you wonder, if the last whitespace was parsed correctly, why is it not followed by the end of string parser?

Let's investigate a bit more and add another debugging parser at the last whitespace.

```
const pDoc := 
  (WS.e_I(Nat))
  .Rep()
  .I_e(WS.Debug("LastWS", di, de))
  .Debug("End", di, de)
  .End
```
Now the trace is:
```
> End: 9 " "
< End: 9 " "
| R: 0 "EOS"
| Was committed
| Error:
| 1:  1 2 3 4
|             ^
| expected a digit
|
```

LastWS is not even displayed! Because `.I_e` is only a concatenation operation if the parser to the left of `.I_e` succeeds, it means the parser to the left of `.I_e(WS)` did not succeed.

We now place new debugging suffixes to debug the inner loop parser as well as the outer loop parser:

```
const pDoc := 
  WS.e_I(Nat).Debug("I", di, de)
  .Rep().Debug("Z", di, de)
  .I_e(WS)
  .End
```
The trace is now (abbreviated)
```
> Z: 9 " "
...
> I: 3 " "
< I: 3 " "
 (Success)
> I: 1 " "
< I: 1 " "
| R: 0 "EOS"
| Was committed
| Error:
| 1:
|     ^
| expected a digit
...
```
Here you can see something interesting: The parser named `I` to parse whitespace + number (`WS.e_I(Nat)`) was called on the last white space, and it complained that it was expecting a digit after the whitespace.
`.Rep()` did not conclude to success because the inner parser was "committed", meaning it did start to parse something from where it was called (1 > 0). If the parse result was a recoverable failure that did not consume any input (had we had `I: 0` or `R: 1`), the parser combinator `.Rep()` would have concluded with success.
Now you might understand what's wrong. The last space is parsed by:

`WS.e_I(Nat)`

and since `WS` succeed, it complains that a nat is missing.
To solve this issue, you might discover that it would be preferable to start the loop by parsing `Nat`,
so that if `Nat` fails, the loop terminates with success:


```
const pDoc := 
  WS              // White space
  .e_I(           // Then
    Nat.I_e(WS)   //   Nat then space
    .Rep()        //   Zero or more times
  )
  .End()          // Then end
```

Finally, this works:
```
Success
[1, 2, 3, 4]
```

Another way would be to indicate that if `WS.e_I(Nat)` fails, then the input should not be consumed. We can achieve this with the `??()` combinator. In case of failure, it ensures that the failure considers that it consumed nothing.

```
const pDoc := 
  WS
  .e_I(Nat)
  .??()   / If fails, don't consume
  .Rep()
  .I_e(WS)
  .End()
```

This also works. However, you should avoid that solution in general. Indeed:
- It is likely less efficient since a failure is detected indirectly
- If you replaced `Nat` with anything else, you might skip the interesting parse errors.

So in general, you should prefer the first solution.