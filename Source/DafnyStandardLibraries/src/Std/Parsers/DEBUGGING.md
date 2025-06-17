# How to debug a parser created with this library?

Developing parsers can be pretty challenging sometimes. Fortunately, this library provides tools to debug parsers.

Let's say you develop the following parser to parse a list of space-separated numbers on the command line:

<!-- %check-run-output -->
```dafny
import opened Std.Parsers.StringBuilders

const pDoc :=
  WS.e_I(Nat)   // Space then nat
  .Rep()        // Zero or more times
  .I_e(WS)      // Then space
  .End()        // Then end

method Main() {
  var input := " 1 2 3 4 ";
  var result := pDoc.Apply(input);
  expect result.ParseFailure?;
  print FailureToString(input, result);
}
```

Note that `.Rep()` is a parser combinator that repeats the parser to its left until it fails (its loop body), at which point it should emit the sequence of parsed elements.
You see the unexpected result:

<!-- %check-expect -->
```expect
Error:
1:  1 2 3 4 
            ^
expected a digit
```

It's expecting a digit where it should have just accepted the end of the string. To figure out what went wrong,
let's first define two debug functions like below - they can't be defined in the library because they have print effects. You could change the type of the output of string if you were to customize them.

<!-- %no-check -->
```dafny
// Debug start
function dIn(
  name: string, input: string): string {
  input
} by method {
  PrintDebugSummaryInput(name, input);
  return input;
}

// Debug end
function dOut<K>(
  name: string,
  di_result: string,
  result: P.ParseResult<K>): () {
  ()
} by method {
  PrintDebugSummaryOutput(name, di_result, result);
  return ();
}
```

Now you can use the `.Debug("some name", dIn, dOut)` suffix on any parser builder to debug its input and parse result. Let's use it on our example just before parsing the end
<!-- %no-check -->
```dafny
const pDoc := 
  WS.e_I(Nat)
  .Rep()
  .I_e(WS)
  .Debug("End", dIn, dOut)
  .End
```

Running this parser on `" 1 2 3 4 "` displays the following trace.

<!-- %no-check -->
```dafny
> [End] ' ' and 8 chars left
< [End] ' ' and 8 chars left
| Unparsed: '' (end of string)
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

<!-- %no-check -->
```dafny
const pDoc := 
  (WS.e_I(Nat))
  .Rep()
  .I_e(WS.Debug("LastWS", dIn, dOut))
  .Debug("End", dIn, dOut)
  .End
```
Now the trace is:
<!-- %no-check -->
```dafny
> [End] ' ' and 8 chars left
< [End] ' ' and 8 chars left
| Unparsed: 0 "EOS"
| Was committed
| Error:
| 1:  1 2 3 4
|             ^
| expected a digit
|
```

LastWS is not even displayed! Because `.I_e` is only a concatenation operation if the parser to the left of `.I_e` succeeds, it means the parser to the left of `.I_e(WS)` did not succeed.

We now place new debugging suffix operations to debug the inner loop parser as well as the outer loop parser:

<!-- %no-check -->
```dafny
const pDoc := 
  WS.e_I(Nat).Debug("I", dIn, dOut)
  .Rep().Debug("Z", dIn, dOut)
  .I_e(WS)
  .End
```
The trace is now (abbreviated)
<!-- %no-check -->
```dafny
> [Z] ' ' and 8 chars left
...
> [I] ' ' and 2 chars left
< [I] ' ' and 2 chars left
 (Success)
> [I] ' ' and end of string
< [I] ' ' and end of string
| Unparsed: '' (end of string)
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

<!-- %no-check -->
```dafny
const pDoc := 
  WS              // White space
  .e_I(           // Then
    Nat.I_e(WS)   //   Nat then space
    .Rep()        //   Zero or more times
  )
  .End()          // Then end
```

Finally, this works:
<!-- %no-check -->
```dafny
Success
[1, 2, 3, 4]
```

Another way would be to indicate that if `WS.e_I(Nat)` fails, then the input should not be consumed. We can achieve this with the `??()` combinator. In case of failure, it ensures that the failure considers that it consumed nothing.

<!-- %no-check -->
```dafny
const pDoc := 
  WS
  .e_I(Nat)
  .??()   // If fails, don't commit
  .Rep()
  .I_e(WS)
  .End()
```

This also works. However, you should avoid that solution in general. Indeed:
- It is likely less efficient since a failure is detected indirectly
- If you replaced `Nat` with anything else, you might skip the interesting parse errors.

So in general, you should prefer the first solution.