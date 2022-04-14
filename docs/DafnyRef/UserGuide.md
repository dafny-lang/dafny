<!--PDF NEWPAGE-->
# 24. Dafny User's Guide {#sec-user-guide}

Most of this document describes the Dafny programming language.
This section describes the `dafny` tool, a combined verifier and compiler
that implements the Dafny language.

The development of the dafny language and tool is a GitHub project at [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny).
The project is open source, with collaborators from various organizations and additional contributors welcome.
The software itself is licensed under the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).

## 24.1. Introduction

The dafny tool implements the following capabilities:

- checking that the input files represent a valid Dafny program (i.e., syntax, grammar and type checking);
- verifying that the program meets its specifications, by translating the program to verification conditions
and checking those with Boogie and an SMT solver, typically Z3;
- compiling the program to a target language, such as C#, Java, Javascript, Go (and others in development);
- running the executable produced by the compiler.

Using various command-line flags, the tool can perform various combinations of the last three actions (the first
action is always performed).

## 24.2. Dafny Programs and Files

A Dafny program is a set of modules.
Modules can refer to other modules, such as through `import` declarations
or `refines` clauses.
A Dafny program consists of all the modules needed so that all module
references are resolved.

Dafny files (`.dfy`) in the operating system each hold
some number of top-level declarations. Thus a full program may be
distributed among multiple files.
To apply the `dafny` tool to a Dafny program, the `dafny` tool must be
given all the files making up a complete program (or, possibly, more than
one program at a time). This can be effected either by listing all of the files
by name on the command-line or by using `include` directives within a file
to stipulate what other files contain modules that the given file needs.
Thus the complete set of modules are all the modules in all the files listed
on the command-line or referenced, recursively, by `include` directives
within those files. It does not matter if files are repeated either as
includes or on the command-line.[^fn-duplicate-files]

Note however that although the complete set of files, command-line plus
included files, make up the program, by default, only those files listed on
the command-line are verified. To do a complete verification, each file
must be verified; it may well happen that a verification failure in one
file (which is not on the command-line and thus not checked) may hide a
verification failure in a file that is being checked.
Thus it is important to eventually check all files, preferably in an order
in which the files without dependencies are checked first, then those that
depend on them, etc., until all files are checked.

[^fn-duplicate-files]: File names are considered equal if they
have the same absolute path, compared as case-sensitive strings
(regardless of whether the underlying file-system is case sensitive).
Use of symbolic links
may make the same file have a different absolute path; this will generally
cause duplicate declaration errors.

## 24.3. Installing Dafny

The instructions for installing dafny and the required dependencies and environment
are described on the Dafny wiki:
[https://github.com/dafny-lang/dafny/wiki/INSTALL](https://github.com/dafny-lang/dafny/wiki/INSTALL).
They are not repeated here to avoid replicating information that
easily becomes inconsistent and out of date.

As of this writing, users can install pre-built Dafny binaries
or build directly from the source files maintained in the github project.

Current and past Dafny binary releases can be found at
[https://github.com/dafny-lang/dafny/releases](https://github.com/dafny-lang/dafny/releases) for each supported platform.
Each release is a .zip file with a name combining the release name and the
platform. Current platforms are Windows 10, Ubuntu 16ff, and MacOS 10.14ff.

The principal dependency of the dafny tool is that it uses `dotnet`, which
is available and must be installed on Linux and Mac platforms to use dafny.

## 24.4. Dafny Code Style

There are code style conventions for Dafny code, recorded [here](https://dafny-lang.github.io/dafny/StyleGuide/Style-Guide).
Most significantly, code is written without tabs and with a 2 space indentation.


## 24.5. IDEs for Dafny

Dafny source files are text files and can of course be edited with any
text editor. However, some tools provide syntax-aware features:

- There is a [Dafny mode for
    Emacs](https://github.com/boogie-org/boogie-friends).

- VSCode, a cross-platform editor for many programming languages has an extension for dafny, installed from within VSCode. VSCode is available [here](http://code.visualstudio.com). The extension provides syntax highlighting, in-line parser, type and verification errors, and code navigation.

- An old Visual Studio plugin is no longer supported

Information about installing IDE extensions for Dafny is found
on the [Dafny INSTALL page in the wiki](https://github.com/dafny-lang/dafny/wiki/INSTALL).


## 24.6. The Dafny Server

Before Dafny [implemented](https://github.com/dafny-lang/dafny/tree/master/Source/DafnyLanguageServer) the official [Language Server Protocol](https://microsoft.github.io/language-server-protocol/), it implemented its own protocol for [Emacs](https://github.com/boogie-org/boogie-friends), which resulted in a project called [DafnyServer](https://github.com/dafny-lang/dafny/tree/master/Source/DafnyServer).

The Dafny Server has [integration tests](https://github.com/dafny-lang/dafny/tree/master/Test/server) that serve as the basis of the documentation.

The server is essentially a REPL, which produces output in the same format as the Dafny CLI; clients thus
do not need to understand the internals of Dafny's caching.  A typical editing session proceeds as follows:

* When a new Dafny file is opened, the editor starts a new instance of the
  Dafny server.  The cache is blank at that point.
* The editor sends a copy of the buffer for initial verification.  This takes
  some time, after which the server returns a list of errors.
* The user makes modifications; the editor periodically sends a new copy of
  the buffer's contents to the Dafny server, which quickly returns an updated
  list of errors.

The client-server protocol is sequential, uses JSON, and works over ASCII
pipes by base64-encoding utf-8 queries.  It defines one type of query, and two
types of responses:

Queries are of the following form:

     verify
     <base64 encoded JSON payload>
     [[DAFNY-CLIENT: EOM]]

Responses are of the following form:

     <list of errors and usual output, as produced by the Dafny CLI>
     [SUCCESS] [[DAFNY-SERVER: EOM]]

or

     <error message>
     [FAILURE] [[DAFNY-SERVER: EOM]]

The JSON payload is an utf-8 encoded string resulting of the serialization of
a dictionary with 4 fields:
   * args:   An array of Dafny arguments, as passed to the Dafny CLI
   * source: A Dafny program, or the path to a Dafny source file.
   * sourceIsFile: A boolean indicating whether the 'source' argument is a
                   Dafny program or the path to one.
   * filename:     The name of the original source file, to be used in error
                   messages

For small files, embedding the Dafny source directly into a message is
convenient; for larger files, however, it is generally better for performance
to write the source snapshot to a separate file, and to pass that to Dafny
by setting the 'sourceIsFile' flag to true.

For example, if you compile and run `DafnyServer.exe`, you could paste the following command:

```dafny
verify
eyJhcmdzIjpbIi9jb21waWxlOjAiLCIvcHJpbnRUb29sdGlwcyIsIi90aW1lTGltaXQ6MjAiXSwi
ZmlsZW5hbWUiOiJ0cmFuc2NyaXB0Iiwic291cmNlIjoibWV0aG9kIEEoYTppbnQpIHJldHVybnMg
KGI6IGludCkge1xuICBiIDo9IGE7XG4gIGFzc2VydCBmYWxzZTtcbn1cbiIsInNvdXJjZUlzRmls
ZSI6ZmFsc2V9
[[DAFNY-CLIENT: EOM]]
```

The interpreter sees the command `verify`, and then starts reading every line until it sees `[[DAFNY-CLIENT: EOM]]`
The payload is a base64 encoded string that you could encode or decode using JavaScript's `atob` and `btoa` function.
For example, the payload above was generated using the following code:
```js
btoa(JSON.stringify({
  "args": [
    "/compile:0",
    "/printTooltips",
    "/timeLimit:20"
   ],
   "filename":"transcript",
   "source":
`method A(a:int) returns (b: int) {
   b := a;
   assert false;
}
`,"sourceIsFile": false}))
=== "eyJhcmdzIjpbIi9jb21waWxlOjAiLCIvcHJpbnRUb29sdGlwcyIsIi90aW1lTGltaXQ6MjAiXSwiZmlsZW5hbWUiOiJ0cmFuc2NyaXB0Iiwic291cmNlIjoibWV0aG9kIEEoYTppbnQpIHJldHVybnMgKGI6IGludCkge1xuICBiIDo9IGE7XG4gIGFzc2VydCBmYWxzZTtcbn1cbiIsInNvdXJjZUlzRmlsZSI6ZmFsc2V9"
```

Thus to decode such output, you'd manually use `JSON.parse(atob(payload))`.
The Dafny Server is still supported, but we recommend using the [Language Server](https://github.com/dafny-lang/dafny/tree/master/Source/DafnyLanguageServer) that is both available in Emacs and [VSCode](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode). The Language Server also provides features such as ghost highlighting or symbol hovering.

## 24.7. Using Dafny From the Command Line

`dafny` is a conventional command-line tool, operating just like other
command-line tools in Windows and Unix-like systems.


- The format of a command-line is determined by the shell program that is executing the command-line (.e.g. bash, the windows shell, COMMAND, etc.). The command-line typically consists of file names and options, in any order, separated by spaces.
- Files are designated by absolute paths or paths relative to the current
working directory. A command-line argument not matching a known option is considered a filepath.
- Files containing dafny code must have a `.dfy` suffix.
- There must be at least one `.dfy` file.
- The command-line may contain other kinds of files appropriate to
the language that the dafny files are being compiled to.

The command `Dafny.exe /?` gives the current set of options supported
by the tool. The most commonly used options are described in [Section 24.10](#sec-command-line-options).

- Options may begin with either a `/` (as is typical on Windows) or a `-` (as is typical on Linux)
- If an option is repeated (e.g., with a different argument), then the later instance on the command-line supersedes the earlier instance.
- If an option takes an argument, the option name is followed by a `:` and then by the argument value, with no
intervening white space; if the argument itself contains white space, the argument must be enclosed in quotes.
- Escape characters are determined by the shell executing the command-line.

The dafny tool performs several tasks:

- Checking the form of the text in a `.dfy` file. This step is always performed, unless the tool is simply asked for
help information or version number.
- Running the verification engine to check all implicit and explicit specifications. This step is performed by
default, but can be skipped by using the `-noVerify` or `-dafnyVerify:0` option
- Compiling the dafny program to a target language. This step is performed by default if the verification is
successful but can be skipped or always executed by using variations of the `-compile` option.
- Whether the source code of the compiled target is written out is controlled by `-spillTargetCode`
- The particular target language used is chosen by `-compileTarget`
- Whether or not the dafny tool attempts to run the compiled code is controlled by `-compile`

The dafny tool terminates with these exit codes:

* 0 -- success
* 1 -- invalid command-line arguments
* 2 -- parse or types errors
* 3 -- compilation errors
* 4 -- verification errors

Errors in earlier phases of processing typically hide later errors.
For example, if a program has parsing errors, verification or compilation will
not be attempted.
The option `-countVerificationErrors:0` forces the tool to always end with a 0
exit code.

## 24.8. Verification

In this section, we suggest a methodology to figure out [why a single assertion might not hold](#sec-verification-debugging), we propose techniques to deal with [assertions that slow a proof down](#sec-verification-debugging-slow), we explain how to [verify assertions in parallel or in a focused way](#sec-assertion-batches), and we also give some more examples of [useful options and attributes to control verification](#sec-command-line-options-and-attributes-for-verification).

### 24.8.1. Verification debugging when verification fails {#sec-verification-debugging}

Let's assume one assertion is failing ("assertion might not hold" or "postcondition might not hold"). What should you do next?

The following section is textual description of the animation below, which illustrates the principle of debugging an assertion by computing the weakest precondition:  
![weakestpreconditionDemo](https://user-images.githubusercontent.com/3601079/157976402-83fe4d37-8042-40fc-940f-bcfc235c7d2b.gif)

#### 24.8.1.1. Failing postconditions {#sec-failing-postconditions}
Let's look at an example of a failing postcondition.
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    return j;
  }//^^^^^^^ a postcondition might not hold on this return path.
  i := 2;
}
```
One first thing you can do is replace the statement `return j;` by two statements `i := j; return;` to better understand what is wrong:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    return;
  }//^^^^^^^ a postcondition might not hold on this return path.
  i := 2;
}
```
Now, you can assert the postcondition just before the return:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    assert 2 <= i; // This assertion might not hold
    return;
  }
  i := 2;
}
```
That's it! Now the postcondition is not failing anymore, but the `assert` contains the error!
you can now move to the next section to find out how to debug this `assert`.

#### 24.8.1.2. Failing asserts {#sec-failing-asserts}
In the [previous section](#sec-failing-postconditions), we arrive to the point where we have a failing assertion:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    i := j;
    assert 2 <= i; // This assertion might not hold
    return;
  }
  i := 2;
}
```
To debug why this assert might not hold, we need to _move this assert up_, which is similar to [_computing the weakest precondition_](https://en.wikipedia.org/wiki/Predicate_transformer_semantics#Weakest_preconditions).
For example, if we have `x := Y; assert F;` and the `assert F;` might not hold, the weakest precondition for it to hold before `x := Y;` can be written as the assertion `assert F[x:= Y];`, where we replace every occurence of `x` in `F` into `Y`.
Let's do it in our example:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  if b {
    assert 2 <= j; // This assertion might not hold
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
Yay! The assertion `assert 2 <= i;` is not proven wrong, which means that if we manage to prove `assert 2 <= j;`, it will work.
Now, this assert should hold only if we are in this branch, so to _move the assert up_, we need to guard it.
Just before the `if`, we can add the weakest precondition `assert b ==> (2 <= j)`:
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  var j := if !b then 3 else 1;
  assert b  ==>  2 <= j;  // This assertion might not hold
  if b {
    assert 2 <= j;
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
Again, now the error is only on the topmost assert, which means that we are making progress.
Now, either the error is obvious, or we can one more time replace `j` by its value and create the assert `assert b ==> ((if !b then 3 else 1) >= 2);`
```dafny
method FailingPostcondition(b: bool) returns (i: int)
  ensures 2 <= i
{
  assert b  ==>  2 <= (if !b then 3 else 1);  // This assertion might not hold
  var j := if !b then 3 else 1;
  assert b  ==>  2 <= j;
  if b {
    assert 2 <= j;
    i := j;
    assert 2 <= i;
    return;
  }
  i := 2;
}
```
At this point, this is pure logic. We can simplify the assumption:
```
b ==>  2 <= (if !b then 3 else 1)
!b ||  (if !b then 2 <= 3 else 2 <= 1)
!b ||  (if !b then true else false)
!b || !b;
!b;
```
Now we can understand what went wrong: When b is true, all of these formulas above are false, this is why the Dafny verifier was not able to prove them.
In the next section, we will explain how to "move asserts up" in certain useful patterns.

#### 24.8.1.3. Failing asserts cases {#sec-failing-asserts-special-cases}

This list is not exhaustive but can definitely be useful to provide the next step to figure out why Dafny could not prove an assertion.

 Failing assert           | Suggested rewriting
--------------------------|---------------------------------------
 <br>`x := Y;`<br>`assert P;` | `assert P[x := Y];`<br>`x := Y;`<br>`assert P;`
 <br>`if B {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}` | `assert B ==> P;`<br>`if B {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}`
 <br>`if B {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}` | `assert !B ==> P;`<br>`if B {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  assert P;`<br>&nbsp;&nbsp;`  ...`<br>`}`
 <br><br>`if X {`<br>&nbsp;&nbsp;`  ...`<br>`} else {`<br>&nbsp;&nbsp;`  ...`<br>`}`<br>`assert A;` | `if X {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A;`<br>`} else {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A;`<br>`}`<br>`assert A;`
 <br><br><br><br><br>`assert forall x :: Q(x);` | [`forall x`](#sec-forall-statement)<br>&nbsp;&nbsp;`  ensures Q(x)`<br>`{`<br>&nbsp;&nbsp;`  assert Q(x);`<br>`};`<br>` assert forall x :: Q(x);`
 <br><br><br><br><br>`assert forall x :: P(x) ==> Q(x);` | [`forall x | P(x)`](#sec-forall-statement)<br>&nbsp;&nbsp;`  ensures Q(x)`<br>`{`<br>&nbsp;&nbsp;`  assert Q(x);`<br>`};`<br>` assert forall x :: P(x) ==> Q(x);`
 <br>`assert exists x | P(x) :: Q(x);`<br>`assert exists x | P(x) :: Q'(x);` | `if x :| P(x) {`<br>&nbsp;&nbsp;`  assert Q(x);`<br>&nbsp;&nbsp;`  assert Q'(x);`<br>`} else {`<br>&nbsp;&nbsp;`  assert false;`<br>`}`
 <br>`assert exists x :: P(x);`<br> | `assert P(x0);`<br>`assert exists x :: P(x);`<br>for a given expression `x0`.
 <br>`ensures exists i :: P(i);`<br> | `returns (j: int)`<br>`ensures P(j) ensures exists i :: P(i)`<br>in a lemma, so that the `j` can be computed explicitly.
 <br><br>`assert A == B;`<br>`callLemma(x);`<br>`assert B == C;`<br> | [`calc == {`](#sec-calc-statement)<br>&nbsp;&nbsp;`  A;`<br>&nbsp;&nbsp;`  B;`<br>&nbsp;&nbsp;`  { callLemma(x); }`<br>&nbsp;&nbsp;`  C;`<br>`};`<br>`assert A == B;`<br>where the [`calc`](#sec-calc-statement) statement can be used to make intermediate computation steps explicit. Works with `<`, `>`, `<=`, `>=`, `==>`, `<==` and `<==>` for example.
 <br><br><br>`assert A ==> B;` | `if A {`<br>&nbsp;&nbsp;`  assert B;`<br>`};`<br>`assert A ==> B;`
 <br><br>`assert A && B;` | `assert A;`<br>`assert B;`<br>`assert A && B;`
 <br>`assert P(x);`<br>where `P` is an [`{:opaque}`](#sec-opaque) predicate | [`reveal P();`](#sec-reveal-statement)<br>`assert P(x);`<br><br>
 `assert P(x);`<br>where `P` is an [`{:opaque}`](#sec-opaque) predicate<br><br> | [`assert P(x) by {`](#sec-assert-statement)<br>[&nbsp;&nbsp;`  reveal P();`](#sec-reveal-statement)<br>`}`
 `assert P(x);`<br>where `P` is not an [`{:opaque}`](#sec-opaque) predicate with a lot of `&&` in its body and is assumed | Make `P` [`{:opaque}`](#sec-opaque) so that if it's assumed, it can be proven more easily. You can always [reveal](#sec-reveal-statement) it when needed.
 `ensures P ==> Q` on a lemma<br> | `requires P ensures Q` to avoid accidentally calling the lemma on inputs that do not satisfy `P`
 `seq(size, i => P)` | `seq(size, i requires 0 <= i < size => P);`
  <br><br>`assert forall x :: G(i) ==> R(i);` |  `assert G(i0);`<br>`assert R(i0);`<br>`assert forall i :: G(i) ==> R(i);` with a guess of the `i0` that makes the second assert to fail.
  <br><br>`assert forall i | 0 < i <= m :: P(i);` |  `assert forall i | 0 < i < m :: P(i);`<br>`assert forall i | i == m :: P(i);`<br>`assert forall i | 0 < i <= m :: P(i);`<br><br>
  <br><br>`assert forall i | i == m :: P(m);` |  `assert P(m);`<br>`assert forall i | i == m :: P(i);`
  `method m(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n() {`<br>&nbsp;&nbsp;`  ...`<br><br><br>&nbsp;&nbsp;`  var x := m(a);`<br>&nbsp;&nbsp;`  assert P(x);` | `method m(i) returns (j: T)`<br>&nbsp;&nbsp;`  requires A(i)`<br>&nbsp;&nbsp;`  ensures B(i, j)`<br>`{`<br>&nbsp;&nbsp;`  ...`<br>`}`<br><br>`method n() {`<br>&nbsp;&nbsp;`  ...`<br>&nbsp;&nbsp;`  assert A(k);`<br>&nbsp;&nbsp;`  assert forall x :: B(k, x) ==> P(x);`<br>&nbsp;&nbsp;`  var x := m(k);`<br>&nbsp;&nbsp;`  assert P(x);`

### 24.8.2. Verification debugging when verification is slow {#sec-verification-debugging-slow}

In this section, we describe techniques to apply in the case when verification is slower than expected, does not terminate, or timeouts.

#### 24.8.2.1. `assume false;` {#sec-assume-false}

Assuming `false` is an empirical way to short-circuit the verifier and usually stop verification at a given point[^explainer-assume-false], and since the final compilation steps do not accept this command, it is safe to use it during development.
Another similar command, `assert false;`, would also short-circuit the verifier, but it would still make the verifier try to prove `false`, which can also lead to timeouts.

[^explainer-assume-false]: `assume false` tells the Dafny verifier "Assume everything is true from this point of the program". The reason is that, 'false' proves anything. For example, `false ==> A` is always true because it is equivalent to `!false || A`, which reduces to `true || A`, which reduces to `true`.

Thus, let us say a program of this shape takes forever to verify.

```dafny
method NotTerminating(b: bool) {
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
}
```

What we can first do is add an `assume false` at the beginning of the method:

```dafny
method NotTerminating() {
   assume false; // Will never compile, but everything verifies instantly
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assert W;
}
```

This verifies instantly. This gives use a strategy to bissect, or do binary search to find the assertion that slows everything down.
Now, we move the `assume false;` below the next assertion:

```dafny
method NotTerminating() {
   assert X;
   assume false;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assert W;
}
```

If verification is slow again, we can use [techniques seen before](#sec-verification-debugging) to decompose the assertion and find which component is slow to prove.

If verification is fast, that's the sign that `X` is probably not the problem,. We now move the `assume false;` after the if/then block:

```dafny
method NotTerminating() {
   assert X;
   if b {
     assert Y;
   } else {
     assert Z;
     assert P;
   }
   assume false;
   assert W;
}
```

Now, if verification is fast, we know that `assert W;` is the problem. If it is slow, we know that one of the two branches of the `if` is the problem.
The next step is to put an `assume false;` at the end of the `then` branch, and an `assume false` at the beginning of the else branch:

```dafny
method NotTerminating() {
   assert X;
   if b {
     assert Y;
     assume false;
   } else {
     assume false;
     assert Z;
     assert P;
   }
   assert W;
}
```

Now, if verification is slow, it means that `assert Y;` is the problem.
If verification is fast, it means that the problem lies in the `else` branch.
One trick to ensure we measure the verification time of the `else` branch and not the then branch is to move the first `assume false;` to the top of the then branch, along with a comment indicating that we are short-circuiting it for now.
Then, we can move the second `assume false;` down and identify which of the two assertions makes the verifier to be slow.


```dafny
method NotTerminating() {
   assert X;
   if b {
     assume false; // Short-circuit because this branch is verified anyway
     assert Y;
   } else {
     assert Z;
     assume false;
     assert P;
   }
   assert W;
}
```

If verification is fast, which of the two assertions `assert Z;` or `assert P;` causes the slowdown?[^answer-slowdown]

[^answer-slowdown]: `assert P;`.

We now hope you know enough of `assume false;` to locate assertions that make verification slow.
Nest, we will describe some other strategies at the assertion level to figure out what happens and perhaps fix it.

#### 24.8.2.2. `assert ... by {}` {#sec-verification-debugging-assert-by}

If an assertion `assert X;` is slow, it is possible that calling a lemma or invoking other assertions can help proving it: The postcondition of this lemma, or the added assertions, could help the Dafny verifier figure out faster how to prove the result.

```dafny
  assert SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
  LEMMA();
  assert X;
...
lemma () 
  requires LEMMA_PRECONDITION
  ensures X { ... }
```

However, this approach has the problem that it exposes the asserted expressions and lemma postconditions not only for the assertion we want to prove faster,
but also for every assertion that appears afterwards. This can result in slowdowns[^verifier-lost].
A good practice consists of wrapping the intermediate verification steps in an `assert ... by {}`, like this:


```dafny
  assert X by {
    assert SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
    LEMMA();
  }
```

Now, only `X` is available for the Dafny Verifier to prove the rest of the method.

[^verifier-lost]: By default, the expression of an assertion or a precondition is added to the knowledge base of the Dafny verifier for further assertions or postconditions. However, this is not always desirable, because if the verifier has too much knowledge, it might get lost trying to prove something in the wrong direction.

#### 24.8.2.3. Labeling and revealing assertions {#sec-labeling-revealing-assertions}

Another way to prevent assertions or preconditions from cluttering the verifier[^verifier-lost] is to label and reveal them.
Labeling an assertion has the effect of "hiding" its result, until there is a "reveal" calling that label.

The example of the [previous section](#sec-verification-debugging-assert-by) could be written like this.

```dafny
  assert p: SOMETHING_HELPING_TO_PROVE_LEMMA_PRECONDITION;
  // p is not available here.
  assert X by {
    reveal p;
    LEMMA();
  }
```

Similarly, if a precondition is only needed to prove a specific result in a method, one can label and reveal the precondition, like this:

```dafny
method Slow(i: int, j: int)
  requires greater: i > j {
  
  assert i >= j by {
    reveal greater;
  }
}
```

#### 24.8.2.4. Non-opaque `function method` {#sec-non-opaque-function-method}

Functions are normally used for specifications, but their functional syntax is sometimes also desirable to write application code.
However, doing so naively results in the body of a `function method Fun()` be available for every caller, which can cause the verifier to time out or get extremely slow[^verifier-lost].
A solution for that is to add the attribute [`{:opaque}`](#sec-opaque) right between `function method` and `Fun()`, and use [`reveal Fun();`](#sec-reveal-statement) in the calling functions or methods when needed.

#### 24.8.2.5. Conversion to and from bitvectors {#sec-conversion-to-and-from-bitvectors}

Bitvectors and natural integers are very similar, but they are not treated the same by the Dafny verifier. As such, conversion from `bv8` to an `int` and vice-versa is not straightforward, and can result in slowdowns.

There are two solutions to this for now. First, one can define a [subset type](#sec-subset-types) instead of using the built-in type `bv8`:

```dafny
type byte = x | 0 <= x < 256
```

One of the problems of this approach is that additions, substractions and multiplications do not enforce the result to be in the same bounds, so it would have to be checked, and possibly truncated with modulos. For example:

```dafny
  var a: byte := 250;
  var b: byte := 200;
  var c := b - a;               // inferred to be an 'int', its value will be 50.
  var d := a + b;               // inferred to be an 'int', its value will be 450.
  var e := (a + b) % 256;       // still inferred to be an 'int'...
  var f: byte := (a + b) % 256; // OK
```

A better solution consists of creating a [newtype](#sec-newtypes) that will have the ability to check bounds of arithmetic expressions, and can actually be compiled to bitvectors as well.

```dafny
newtype {:nativeType "char"} byte = x | 0 <= x < 256
  var a: byte := 250;
  var b: byte := 200;
  var c := b - a; // OK, inferred to be a byte
  var d := a + b; // Error: cannot prove that the result of a + b is of type `byte`.
  var f := ((a as int + b as int) % 256) as byte // OK
```

One might consider refactoring this code into separate functions if used over and over.

#### 24.8.2.6. Nested loops {#sec-nested-loops}

In the case of nested loops, the verifier might timeout sometimes because of the information available[^verifier-lost].
One way to mitigate this problem, when it happens, is to isolate the inner loop by refactoring it into a separate method, with suitable pre and postconditions that will usually assume and prove the invariant again.
For example,

```dafny
`while X
   invariant Y
 {
   while X'
     invariant Y'
   {
 
   }
 }
```

could be refactored as this:

```dafny
`while X
   invariant Y
 {
   innerLoop();
 }
...
method innerLoop()
  require Y'
  ensures Y'
```

In the next section, when everything can be proven in a timely manner, we explain another strategy to decrease proof time by parallelizing it if needed, and making the verifier focus on certain parts.

### 24.8.3. Assertion batches {#sec-assertion-batches}

To understand how to control verification,
it is first useful to understand how Dafny verifies functions and methods.

For every method (or function, constructor, etc.), Dafny extracts _assertions_. Here is a non-exhaustive list of such extracted assertions:

**Integer assertions:**

* Every [division](#sec-numeric-types) yields an _assertion_ that the divisor is never zero.
* Every [bounded number operation](#sec-numeric-types) yields an _assertion_ that the result will be within the same bounds (no overflow, no underflows).
* Every [conversion](#sec-as-expression) yields an _assertion_ that conversion is compatible.
* Every [bitvector shift](#sec-bit-vector-types) yields an _assertion_ that the shift amount is never negative, and that the shift amount is within the width of the value.

**Object assertions:**

* Every [object property access](#sec-class-types) yields an _assertion_ that the object is not null.
* Every assignment `o.f := E;` yield an _assertion_ that `o` is among the set of objects of the `modifies` clause of the enclosing [loop](#sec-loop-framing) or [method](#sec-modifies-clause).
* Every read `o.f` yield an _assertion_ that `o` is among the set of objects of the [`reads`](#sec-reads-clause) clause of the enclosing function or predicate; or the [`modifies`](#sec-modifies-clause) clause of the enclosing method.
* Every [array access](#sec-array-types) `a[x]` yield the assertion that `0 <= x < a.Length`.
* Every [sequence access](#sec-sequences) `a[x]` yield an _assertion_, that `0 <= x < |a|`, because sequences are never null.
* Every [datatype update expression](#sec-datatype-update-suffix) and [datatype destruction](#sec-algebraic-datatype) yields an _assertion_ that the object has the given property.
* Every method overriding a [`trait`](#sec-trait-types) yield an _assertion_ that any postcondition it provides is equal to or more detailed than in its parent trait, and an _assertion_ that any precondition it provides is equal to or more permissive than in its parent trait.

**Other implicit assertions:**

* Every value whose type is assigned to a [subset type](#sec-subset-types) yields an _assertion_ that it satisfies the subset type constraint.
* Every non-empty [subset type](#sec-subset-types) yields an _assertion_ that its witness satisfies the constraint.
* [Assign-such-that operators](#sec-update-and-call-statement) `x :| P(x)` yield an _assertion_ that `exists x :: P(x)`.
* Every recursive function yield an _assertion_ that [it terminates](#sec-loop-termination).
* Every [match expression](#sec-match-expression) or [alternative if statement](#sec-if-statement) yield an _assertion_ that all cases are covered.

**Explicit assertions:**

* Any explicit [`assert`](#sec-assert-statement) statement is _an assertion_[^precision-requires-clause].
* A consecutive pair of lines in a [`calc`](#sec-calc-statement) statement forms _an assertion_ that the expressions are related according to the common operator.
* Every call to a function or method with a [`requires`](#sec-requires-clause) clause yields _one assertion per requires clause_[^precision-requires-clause]
  (special cases such as sequence indexing come with a special require clause that the index is within bounds).
* Every [`ensures`](#sec-ensures-clause) clause yields an _assertion_ at the end of the method and on every return, and on [`forall`](#sec-forall-statement) statements.
* Every [`invariant`](#sec-invariant-clause) clause yields an _assertion_ that it holds before the loop and an _assertion_ that it holds at the end of the loop.
* Every [`decreases`](#sec-decreases-clause) clause yields an _assertion_ at either a call site or at the end of a while loop.
* Every [`yield ensures`](#sec-iterator-specification) clause on [iterator](#sec-iterator-types) yield _assertions_ that the clause hold at every yielding point.
* Every [`yield requires`](#sec-iterator-specification) clause on [iterator](#sec-iterator-types) yield _assertions_ that the clause hold at every point when the iterator is called.


[^precision-requires-clause]: Dafny actually breaks things down further. For example, a precondition `requires A && B` or an assert statement `assert A && B;` turns into two assertions, more or less like `requires A requires B` and `assert A; assert B;`.

It is useful to mentally visualize all these assertions as a list that roughly follows the order in the code,
except for `ensures` or `decreases` that generate assertions that seem earlier in the code but, for verification purposes, would be placed later.
In this list, each assertion depends on other assertions, statements and expressions that appear earlier in the control flow[^complexity-path-encoding].

[^complexity-path-encoding]: All the complexities of the execution paths (if-then-else, loops, goto, break....) are, down the road and for verification purposes, cleverly encoded with variables recording the paths and guarding assumptions made on each path. In practice, a second clever encoding of variables enables grouping many assertions together, and recovers which assertion is failing based on the value of variables that the SMT solver returns.

The fundamental unit of verification in Dafny is an _assertion batch_, which consists of one or more assertions from this "list", along with all the remaining assertions turned into assumptions. To reduce overhead, by default Dafny collects all the assertions in the body of a given method into a single assertion batch that it sends to the verifier, which tries to prove it correct.

* If the verifier says it is correct[^smt-encoding], it means that all the assertions hold.
* If the verifier returns a counterexample, this counterexample is used to determine both the failing assertion and the failing path.
  In order to retrieve additional failing assertions, Dafny will again query the verifier after turning previously failed assertions into assumptions.[^example-assertion-turned-into-assumption] [^caveat-about-assertion-and-assumption]
* If the verifier returns `unknown` or times out, or even preemptively for difficult assertions or to reduce the chance that the verifier will ‘be confused’ by the many assertions in a large batch, Dafny may partition the assertions into smaller batches[^smaller-batches]. An extreme case is the use of the `/vcsSplitOnEveryAssert` command-line option or the [`{:vcs_split_on_every_assert}` attribute](#sec-vcs_split_on_every_assert), which causes Dafny to make one batch for each assertion.

[^smt-encoding]: The formula sent to the underlying SMT solver is the negation of the formula that the verifier wants to prove - also called a VC or verification condition. Hence, if the SMT solver returns "unsat", it means that the SMT formula is always false, meaning the verifier's formula is always true. On the other side, if the SMT solver returns "sat", it means that the SMT formula can be made true with a special variable assignment, which means that the verifier's formula is false under that same variable assignment, meaning it's a counter-example for the verifier. In practice and because of quantifiers, the SMT solver will usually return "unknown" instead of "sat", but will still provide a variable assignment that it couldn't prove that it does not make the formula true. Dafny reports it as a "counter-example" but it might not be a real counter-example, only provide hints about what Dafny knows.

[^example-assertion-turned-into-assumption]: This [post](https://github.com/dafny-lang/dafny/discussions/1898#discussioncomment-2344533) gives an overview of how assertions are turned into assumptions for verification purposes.

[^caveat-about-assertion-and-assumption]: Caveat about assertion and assumption: One big difference between an "assertion transformed in an assumption" and the original "assertion" is that the original "assertion" can unroll functions twice, whereas the "assumed assertion" can unroll them only once. Hence, Dafny can still continue to analyze assertions after a failing assertion without automatically proving "false" (which would make all further assertions vacuous).

[^smaller-batches]: To create a smaller batch, Dafny duplicates the assertion batch, and arbitrarily transforms the clones of an assertion into assumptions except in exactly one batch, so that each assertion is verified only in one batch. This results in "easier" formulas for the verifier because it has less to prove, but it takes more overhead because every verification instance have a common set of axioms and there is no knowledge sharing between instances because they run independently.

#### 24.8.3.1. Controlling assertion batches {#sec-assertion-batches-control}

Here is how you can control how Dafny partitions assertions into batches.

* [`{:focus}`](#sec-focus) on an assert generates a separate assertion batch for the assertions of the enclosing block.
* [`{:split_here}`](#sec-split_here) on an assert generates a separate assertion batch for assertions after this point.
* [`{:vcs_split_on_every_assert}`](#sec-vcs_split_on_every_assert) on a function or a method generates one assertion batch per assertion

We discourage the use of the following _heuristics attributes_ to partition assertions into batches.
The effect of these attributes may vary, because they are low-level attributes and tune low-level heuristics, and will result in splits that could be manually controlled anyway.
* [`{:vcs_max_cost N}`](#sec-vcs_max_cost) on a function or method enables splitting the assertion batch until the "cost" of each batch is below N.
  Usually, you would set [`{:vcs_max_cost 0}`](#sec-vcs_max_cost) and [`{:vcs_max_splits N}`](#sec-vcs_max_splits) to ensure it generates N assertion batches.
* [`{:vcs_max_keep_going_splits N}`](#sec-vcs_max_keep_going_splits) where N > 1 on a method dynamically splits the initial assertion batch up to N components if the verifier is stuck the first time.

### 24.8.4. Command-line options and other attributes to control verification {#sec-command-line-options-and-attributes-for-verification}

There are many great options that control various aspects of verifying dafny programs. Here we mention only a few:

- Control of output: [`/dprint`](#sec-controlling-output), [`/rprint`](#sec-controlling-output), `/stats`, [`/compileVerbose`](#sec-controlling-compilation)
- Whether to print warnings: `/proverWarnings`
- Control of time: `/timeLimit`
- Control of resources: `/rLimit` and [`{:rlimit}`](#sec-rlimit)
- Control of the prover used: `/prover`
- Control of how many times to _unroll_ functions: [`{:fuel}`](#sec-fuel)

You can search for them in [this file](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef) as some of them are still documented in raw text format.

## 24.9. Compilation {#sec-compilation}

The `dafny` tool can compile a Dafny program to one of several target languages. Details and idiosyncrasies of each
of these are described in the following subsections. In general note the following:

- The compiled code originating from `dafny` can be compiled with other source and binary code, but only the `dafny`-originated code is verified.
- Output file names can be set using `-out`.
- Code generated by Dafny relies requires a Dafny-specific runtime library.  By default the runtime is included in the generated code for most languages (use `-useRuntimeLib` to omit it).  For Java and C++ the runtime must be linked to separately, except when running the generated code using Dafny's `-compile:3` or `-compile:4`.  All runtime libraries are part of the Binary (`./DafnyRuntime.*`) and Source (`./Source/DafnyRuntime/DafnyRuntime.*`) releases.
- Names in Dafny are written out as names in the target language. In some cases this can result in naming conflicts. Thus if a Dafny program is intended to be compiled to a target language X, you should avoid using Dafny identifiers that are not legal identifiers in X or that conflict with reserved words in X.

### 24.9.1. Main method {#sec-user-guide-main}

To generate a stand-alone executable from a Dafny program, the
Dafny program must use a specific method as the executable entry point.
That method is determined as follows:

* If the /Main option is specified on the command-line with an argument of "-", then no entry point is used at all
* If the /Main option is specified on the command-line and its argument is
not an empty string, then its argument is
interpreted as the fully-qualified name of a method to be used as the entry point. If there is no matching method, an error message is issued.
* Otherwise, the program is searched for a method with the attribute `{:main}`.
If exactly one is found, that method is used as the entry point; if more
than one method has the `{:main}` attribute, an error message is issued.
* Otherwise, the program is searched for a method with the name `Main`.
If more than one is found
an error message is issued.

Any abstract modules are not searched for candidate entry points,
but otherwise the entry point may be in any module or type. In addition,
an entry-point candidate must satisfy the following conditions:

* The method takes no parameters or type parameters
* The method is not a ghost method
* The method has no requires or modifies clauses, unless it is marked `{:main}`
* If the method is an instance (that is, non-static) method and the
  enclosing type is a class,
  then that class must not declare any constructor.
  In this case, the runtime system will
  allocate an object of the enclosing class and will invoke
  the entry-point method on it.
* If the method is an instance (that is, non-static) method and the
  enclosing type is not a class,
  then the enclosing type must, when instantiated with auto-initializing
  type parameters, be an auto-initialing type.
  In this case, the runtime system will
  invoke the entry-point method on a value of the enclosing type.

Note, however, that the following are allowed:

* The method is allowed to have `ensures` clauses
* The method is allowed to have `decreases` clauses, including a
  `decreases *`. (If Main() has a `decreases *`, then its execution may
  go on forever, but in the absence of a `decreases *` on Main(), Dafny
  will have verified that the entire execution will eventually
  terminate.)

If no legal candidate entry point is identified, `dafny` will still produce executable output files, but
they will need to be linked with some other code in the target language that
provides a `main` entry point.

### 24.9.2. extern declarations

TO BE WRITTEN

### 24.9.3. C\#

TO BE WRITTEN

### 24.9.4. Java

The Dafny-to-Java compiler writes out the translated files of a file _A_`.dfy`
to a directory _A_-java. The `-out` option can be used to choose a
different output directory. The file _A_`.dfy` is translated to _A_`.java`,
which is placed in the output directory along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
directory name is taken from the first file, and `.java` files are written
for each of the `.dfy` files.

TO BE WRITTEN

### 24.9.5. Javascript

TO BE WRITTEN

### 24.9.6. Go

TO BE WRITTEN

### 24.9.7. C++

The C++ backend was written assuming that it would primarily support writing
C/C++ style code in Dafny, which leads to some limitations in the current
implementation.

- We do not support BigIntegers, so do not use `int`, or raw instances of
  `arr.Length`, or sequence length, etc. in executable code.  You can however,
  use `arr.Length as uint64` if you can prove your array is an appropriate
  size.  The compiler will report inappropriate integer use.
- We do not support more advanced Dafny features like traits or co-inductive
  types.
- Very limited support for higher order functions even for array init.  Use
  extern definitions like newArrayFill (see [extern.dfy]
  (https://github.com/dafny-lang/dafny/blob/master/Test/c++/extern.dfy)) or
  similar.  See also the example in [`functions.dfy`]
  (https://github.com/dafny-lang/dafny/blob/master/Test/c++/functions.dfy).
- The current backend also assumes the use of C++17 in order to cleanly and
  performantly implement datatypes.

## 24.10. Dafny Command Line Options {#sec-command-line-options}

There are many command-line options to the `dafny` tool.
The most current documentation of the options is within the tool itself,
using the `/?` option.
Here we give an expanded description of the most important options.

Remember that options can be stated with either a leading `/` or a leading `-`.

### 24.10.1. Help and version information

* `-?` or `-help` : prints out the current list of command-line options and terminates
* `-version` : prints the version of the executable being invoked and terminates

### 24.10.2. Controlling errors and exit codes

* `-countVerificationErrors:<n>` - if 0 then always exit with a 0 exit code, regardless of whether errors are found.  If 1 (the default) then use the usual exit code.  This option is deprecated.

* `-warningsAsErrors` - treat warnings as errors

### 24.10.3. Controlling output {#sec-controlling-output}

* `-dprint:<file>` - print the Dafny program after parsing (use `-` for `<file> to print to the console)

* `-rprint:<file>` - print the Dafny program after type resolution (use `-` for <file> to print to the console)

TO BE WRITTEN

### 24.10.4. Controlling aspects of the tool being run

* `-deprecation:<n>` - controls warnings about deprecated features

   * 0 - no warnings
   * 1 (default) - issue warnings
   * 2 - issue warnings and advise about alternate syntax

* `-warnShadowing` - emits a warning if the name of a declared variable caused another variable to be shadowed

TO BE WRITTEN

### 24.10.5. Controlling verification

* `-verifyAllModules` - verify modules that come from include directives

By default, Dafny only verifies files explicitly listed on the command line: if `a.dfy` includes `b.dfy`, a call to `Dafny a.dfy` will detect and report verification errors from `a.dfy` but not from `b.dfy`'s.

With this flag, Dafny will instead verify everything: all input modules and all their transitive dependencies.  This way `Dafny a.dfy` will verify `a.dfy` and all files that it includes (here `b.dfy`), as well all files that these files include, etc.

Running Dafny with `/verifyAllModules` on the file containing your main result is a good way to ensure that all its dependencies verify.

### 24.10.6. Controlling boogie

* `-print:<file>` - print the translation of the Dafny file to a Boogie file.

If you have Boogie installed locally, you can run the printed Boogie file with the following script:

```
DOTNET=$(which dotnet)

BOOGIE_ROOT="path/to/boogie/Source"
BOOGIE="$BOOGIE_ROOT/BoogieDriver/bin/Debug/netcoreapp3.1/BoogieDriver.dll"

if [[ ! -x "$DOTNET" ]]; then
    echo "Error: Dafny requires .NET Core to run on non-Windows systems."
    exit 1
fi

#Uncomment if you prefer to use the executable instead of the DLL
#BOOGIE=$(which boogie)

BOOGIE_OPTIONS="/infer:j"
PROVER_OPTIONS="\
  /proverOpt:O:auto_config=false \
  /proverOpt:O:type_check=true \
  /proverOpt:O:smt.case_split=3 \
  /proverOpt:O:smt.qi.eager_threshold=100 \
  /proverOpt:O:smt.delay_units=true \
  /proverOpt:O:smt.arith.solver=2 \
  "

"$DOTNET" "$BOOGIE" $BOOGIE_OPTIONS $PROVER_OPTIONS "$@"
#Uncomment if you want to use the executable instead of the DLL
#"$BOOGIE" $BOOGIE_OPTIONS $PROVER_OPTIONS "$@"
```

### 24.10.7. Controlling the prover

TO BE WRITTEN

### 24.10.8. Controlling compilation {#sec-controlling-compilation}

* `-compile:<n>` - controls whether compilation happens

   * 0 - do not compile the program
   * 1 (default) - upon successful verification, compile the program to the target language
   * 2 - always compile, regardless of verification success
   * 3 - if verification is successful, compile the program (like option 1), and then if there is a `Main` method, attempt to run the program
   * 4 - always compile (like option 2), and then if there is a `Main` method, attempt to run the program

* `-compileTarget:<s>` - sets the target programming language for the compiler

   * `cs` - C\#
   * `go` - Go
   * `js` - Javascript
   * `java` - Java
   * `py` - Python
   * `cpp` - C++

* `-spillTargetCode:<n>` - controls whether to write out compiled code in the target language (instead of just holding it in internal temporary memory)

   * 0 (default) - do not write out code
   * 1 - write it out to the target language, if it is being compiled
   * 2 - write the compiled program if it passes verification, regardless of the `-compile` setting
   * 3 - write the compiled program regardless of verification success and the `-compile` setting

* `-out:<file>` - sets the name to use for compiled code files.

By default, Dafny reuses the name of the Dafny file being compiled.  Compilers that generate a single file use the file name as-is (e.g. the C# backend will generate `<file>.dll` and optionally `<file>.cs` with `-spillTargetCode`).  Compilers that generate multiple files use the file name as a directory name (e.g. the Java backend will generate files in directory `<file>-java/`).  Any file extension is ignored, so `-out:<file>` is the same as `-out:<file>.<ext>` if `<file>` contains no periods.

* `-compileVerbose:<n>` - whether to write out compilation information

  * 0 - do not print any information (silent mode)
  * 1 (default) - print information such as the files being created by the compiler

TO BE WRITTEN

### 24.10.9. Options intended for debugging

* `-dprelude:<file>` - choose an alternate prelude file
* `-pmtrace` - print pattern-match compiler debugging information
* `-titrace` - print type inference debugging information

TO BE WRITTEN

## 24.11. Full list of -command-line options <!-- PDFOMIT -->
For the on-line version only, the output of `dafny /?` follows: <!--PDFOMIT-->
{% include_relative Options.txt %} <!-- PDFOMIT -->
