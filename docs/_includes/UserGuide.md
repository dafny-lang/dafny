<!--PDF NEWPAGE-->
# Dafny User's Guide {#user-guide}
## Introduction

The dafny tool implements the following capabilities:

- checking that the input files represent a valid dafny program (i.e., syntax, grammar and type checking);
- verifying that the program meets its specifications, by translating the program to verification conditions
and checking those with Boogie and an SMT solver, typically Z3;
- compiling the program to a target language, such as C#, Java, Javascript, Go (and others in development);
- running the executable produced by the compiler.

Using various command-line flags, the tool can perform various combinations of the last three actions (the first
action is always performed).

The development of the dafny language and tool is a GitHub project at [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny).
The project is open source, with collaborators from various organizations and additional contributors welcome.
The software itself is licensed under the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).

## Installing Dafny From Binaries
**Windows:** To install Dafny on your own machine, download Dafny.zip and
**save** it to your disk. Then, before you open or unzip it, right-click
on it and select Properties; at the bottom of the dialog, click the
Unblock button and then the OK button. Now, open Dafny.zip and copy its
contents into a directory on your machine. (You can now delete the
Dafny.zip file.)

Then:

- To run Dafny from the command line, simply run Dafny.exe from the
    `Binaries` directory.

- There is also a [Dafny mode for
    Emacs](https://github.com/boogie-org/boogie-friends).

**Linux and Mac:** Make sure you have Mono version 4. Then save the
contents of the Dafny.zip for the appropriate version of your platform.
You can now run Dafny from the command line by invoking the script file
`dafny`. For an IDE, use the [Dafny mode for
Emacs](https://github.com/boogie-org/boogie-friends).

**Mac using brew:** On a Mac, you can install dafny, along with its dependencies, mono and z3,  using the `brew` package manager.

## Building Dafny from Source
The current version of the Dafny executable builds and runs with Visual Studio 2012 or later.

First, install the following external dependencies:

-   Visual Studio

-   [Code contract extension](https://visualstudiogallery.msdn.microsoft.com/1ec7db13-3363-46c9-851f-1ce455f66970)

-   [NUnit test adapter](https://visualstudiogallery.msdn.microsoft.com/6ab922d0-21c0-4f06-ab5f-4ecd1fe7175d)

-   To install lit (for test run):
    -   first, install [python](https://www.python.org/downloads/)
    -   second, install [pip](http://pip.readthedocs.org/en/stable/installing/)
    -   last, run "pip install lit" and "pip install OutputCheck"

Second, clone source code (into sibling directories)

-   [Dafny](https://github.com/Microsoft/dafny)
-   [Boogie](https://github.com/boogie-org/boogie)

Last, follow the conventions:

-   Visual Studio
    -   Set "General:Tab" to "2 2"
    -   For `"C#:Formatting:NewLines` Turn everything off except the first option.

Dafny performs its verification by translating the Dafny source into
the Boogie intermediate verification language. So Dafny references
data structures defined in the Boogie project. So the first step
is to clone and build Boogie from sources. See
<https://github.com/boogie-org/boogie>.

Follow these steps.

Let _work_ be a working directory.

Clone Boogie using

```
cd work
git clone https://github.com/boogie-org/boogie.git
```

Build Boogie using the directions from the Boogie web site,
which for Windows currently are:

1. Open Source\\Boogie.sln in Visual Studio
2. Right click the Boogie solution in the Solution Explorer and click Enable NuGet Package Restore. You will probably get a prompt asking to confirm this. Choose Yes.
3. Click BUILD > Build Solution.

Clone Dafny using git. The Dafny directory must be a sibling
of the Boogie directory in order for it to find the Boogie files it needs.

```
cd work
git clone https://github.com/Microsoft/dafny.git
```

Build the command-line Dafny executables.
1. Open dafny/Source/Dafny.sln in Visual Studio
2. Click BUILD > Build Solution.

## Using Dafny From Visual Studio
To test your installation, you can open Dafny test files
from the dafny/Test subdirectory in Visual Studio 2012.
You will want to use "VIEW/Error List" to ensure that
you see any errors that Dafny detects, and
"VIEW/Output" to see the result of any compilation.

An example of a valid Dafny test is

```
dafny\Test\vstte2012\Tree.dfy
```

You can choose "Dafny/Compile" to compile the Dafny
program to C\#. Doing that for the above test
produces `Tree.cs` and `Tree.dll` (since this test does
not have a main program).

The following file in the Dafny repository:

```
dafny\Test\dafny0\Array.dfy
```

is an example of a Dafny file with verification errors.
The source will show red squiggles or dots where there
are errors, and the Error List window will describe the
errors.

## Using Dafny From the Command Line
### Dafny Command Line Options
The command `Dafny.exe /?` gives the following description of
options that can be passed to Dafny.

```
  ---- Dafny options ---------------------------------------------------------

  Multiple .dfy files supplied on the command line are concatenated into one
  Dafny program.

  /dprelude:<file>
                choose Dafny prelude file
  /dprint:<file>
                print Dafny program after parsing it
                (use - as <file> to print to console)
  /printMode:<Everything|NoIncludes|NoGhost>
                NoIncludes disables printing of {:verify false} methods incorporated via the
                include mechanism, as well as datatypes and fields included from other files.
                NoGhost disables printing of functions, ghost methods, and proof statements
                in implementation methods.  It also disables anything NoIncludes disables.
  /rprint:<file>
                print Dafny program after resolving it
                (use - as <file> to print to console)
  /dafnyVerify:<n>
                0 - stop after typechecking
                1 - continue on to translation, verification, and compilation
  /compile:<n>  0 - do not compile Dafny program
                1 (default) - upon successful verification of the Dafny
                    program, compile Dafny program to .NET assembly
                    Program.exe (if the program has a Main method) or
                    Program.dll (othewise), where Program.dfy is the name
                    of the last .dfy file on the command line
                2 - always attempt to compile Dafny program to C\# program
                    out.cs, regardless of verification outcome
                3 - if there is a Main method and there are no verification
                    errors, compiles program in memory (i.e., does not write
                    an output file) and runs it
  /spillTargetCode:<n>
                0 (default) - don't write the compiled Dafny program (but
                    still compile it, if /compile indicates to do so)
                1 - write the compiled Dafny program as a .cs file
  /dafnycc      Disable features not supported by DafnyCC
  /noCheating:<n>
                0 (default) - allow assume statements and free invariants
                1 - treat all assumptions as asserts, and drop free.
  /induction:<n>
                0 - never do induction, not even when attributes request it
                1 - only apply induction when attributes request it
                2 - apply induction as requested (by attributes) and also
                    for heuristically chosen quantifiers
                3 (default) - apply induction as requested, and for
                    heuristically chosen quantifiers and ghost methods
  /inductionHeuristic:<n>
                0 - least discriminating induction heuristic (that is, lean
                    toward applying induction more often)
                1,2,3,4,5 - levels in between, ordered as follows as far as
                    how discriminating they are:  0 < 1 < 2 < (3,4) < 5 < 6
                6 (default) - most discriminating
  /noIncludes   Ignore include directives
  /noNLarith    Reduce Z3's knowledge of non-linear arithmetic (*,/,%).
                Results in more manual work, but also produces more predictable behavior.
  /autoReqPrint:<file>
                Print out requirements that were automatically generated by autoReq.
  /noAutoReq    Ignore autoReq attributes
  /allowGlobals Allow the implicit class '_default' to contain fields, instance functions,
                and instance methods.  These class members are declared at the module scope,
                outside of explicit classes.  This command-line option is provided to simply
                a transition from the behavior in the language prior to version 1.9.3, from
                which point onward all functions and methods declared at the module scope are
                implicitly static and fields declarations are not allowed at the module scope.
                The reference manual is written assuming this option is not given.


  /nologo       suppress printing of version number, copyright message
  /env:<n>      print command line arguments
                  0 - never, 1 (default) - during BPL print and prover log,
                  2 - like 1 and also to standard output
  /wait         await Enter from keyboard before terminating program
  /xml:<file>   also produce output in XML format to <file>

  ---- Boogie options --------------------------------------------------------

  Multiple .bpl files supplied on the command line are concatenated into one
  Boogie program.

  /proc:<p>      : limits which procedures to check
  /noResolve     : parse only
  /noTypecheck   : parse and resolve only

  /print:<file>  : print Boogie program after parsing it
                   (use - as <file> to print to console)
  /pretty:<n>
                0 - print each Boogie statement on one line (faster).
                1 (default) - pretty-print with some line breaks.
  /printWithUniqueIds : print augmented information that uniquely
                   identifies variables
  /printUnstructured : with /print option, desugars all structured statements
  /printDesugared : with /print option, desugars calls

  /overlookTypeErrors : skip any implementation with resolution or type
                        checking errors

  /loopUnroll:<n>
                unroll loops, following up to n back edges (and then some)
  /soundLoopUnrolling
                sound loop unrolling
  /printModel:<n>
                0 (default) - do not print Z3's error model
                1 - print Z3's error model
                2 - print Z3's error model plus reverse mappings
                4 - print Z3's error model in a more human readable way
  /printModelToFile:<file>
                print model to <file> instead of console
  /mv:<file>    Specify file where to save the model in BVD format
  /enhancedErrorMessages:<n>
                0 (default) - no enhanced error messages
                1 - Z3 error model enhanced error messages

  /printCFG:<prefix> : print control flow graph of each implementation in
                       Graphviz format to files named:
                         <prefix>.<procedure name>.dot

  /useBaseNameForFileName : When parsing use basename of file for tokens instead
                            of the path supplied on the command line

  ---- Inference options -----------------------------------------------------

  /infer:<flags>
                use abstract interpretation to infer invariants
                The default is /infer:i
                   <flags> are as follows (missing <flags> means all)
                   i = intervals
                   c = constant propagation
                   d = dynamic type
                   n = nullness
                   p = polyhedra for linear inequalities
                   t = trivial bottom/top lattice (cannot be combined with
                       other domains)
                   j = stronger intervals (cannot be combined with other
                       domains)
                or the following (which denote options, not domains):
                   s = debug statistics
                0..9 = number of iterations before applying a widen (default=0)
  /noinfer      turn off the default inference, and overrides the /infer
                switch on its left
  /checkInfer   instrument inferred invariants as asserts to be checked by
                theorem prover
  /interprocInfer
                perform interprocedural inference (deprecated, not supported)
  /contractInfer
                perform procedure contract inference
  /instrumentInfer
                h - instrument inferred invariants only at beginning of
                    loop headers (default)
                e - instrument inferred invariants at beginning and end
                    of every block (this mode is intended for use in
                    debugging of abstract domains)
  /printInstrumented
                print Boogie program after it has been instrumented with
                invariants

  ---- Debugging and general tracing options ---------------------------------

  /trace        blurt out various debug trace information
  /traceTimes   output timing information at certain points in the pipeline
  /tracePOs     output information about the number of proof obligations
                (also included in the /trace output)
  /log[:method] Print debug output during translation

  /break        launch and break into debugger

  ---- Verification-condition generation options -----------------------------

  /liveVariableAnalysis:<c>
                0 = do not perform live variable analysis
                1 = perform live variable analysis (default)
                2 = perform interprocedural live variable analysis
  /noVerify     skip VC generation and invocation of the theorem prover
  /verifySnapshots:<n>
                verify several program snapshots (named <filename>.v0.bpl
                to <filename>.vN.bpl) using verification result caching:
                0 - do not use any verification result caching (default)
                1 - use the basic verification result caching
                2 - use the more advanced verification result caching
  /verifySeparately
                verify each input program separately
  /removeEmptyBlocks:<c>
                0 - do not remove empty blocks during VC generation
                1 - remove empty blocks (default)
  /coalesceBlocks:<c>
                0 = do not coalesce blocks
                1 = coalesce blocks (default)
  /vc:<variety> n = nested block (default for /prover:Simplify),
                m = nested block reach,
                b = flat block, r = flat block reach,
                s = structured, l = local,
                d = dag (default, except with /prover:Simplify)
                doomed = doomed
  /traceverify  print debug output during verification condition generation
  /subsumption:<c>
                apply subsumption to asserted conditions:
                0 - never, 1 - not for quantifiers, 2 (default) - always
  /alwaysAssumeFreeLoopInvariants
                usually, a free loop invariant (or assume
                statement in that position) is ignored in checking contexts
                (like other free things); this option includes these free
                loop invariants as assumes in both contexts
  /inline:<i>   use inlining strategy <i> for procedures with the :inline
                attribute, see /attrHelp for details:
                  none
                  assume (default)
                  assert
                  spec
  /printInlined
                print the implementation after inlining calls to
                procedures with the :inline attribute (works with /inline)
  /lazyInline:1
                Use the lazy inlining algorithm
  /stratifiedInline:1
                Use the stratified inlining algorithm
  /fixedPointEngine:<engine>
                Use the specified fixed point engine for inference
  /recursionBound:<n>
                Set the recursion bound for stratified inlining to
                be n (default 500)
  /inferLeastForUnsat:<str>
                Infer the least number of constants (whose names
                are prefixed by <str>) that need to be set to
                true for the program to be correct. This turns
                on stratified inlining.
  /smoke        Soundness Smoke Test: try to stick assert false; in some
                places in the BPL and see if we can still prove it
  /smokeTimeout:<n>
                Timeout, in seconds, for a single theorem prover
                invocation during smoke test, defaults to 10.
  /causalImplies
                Translate Boogie's A ==> B into prover's A ==> A && B.
  /typeEncoding:<m>
                how to encode types when sending VC to theorem prover
                   n = none (unsound)
                   p = predicates (default)
                   a = arguments
                   m = monomorphic
  /monomorphize
                Do not abstract map types in the encoding (this is an
                experimental feature that will not do the right thing if
                the program uses polymorphism)
  /reflectAdd   In the VC, generate an auxiliary symbol, elsewhere defined
                to be +, instead of +.

  ---- Verification-condition splitting --------------------------------------

  /vcsMaxCost:<f>
                VC will not be split unless the cost of a VC exceeds this
                number, defaults to 2000.0. This does NOT apply in the
                keep-going mode after first round of splitting.
  /vcsMaxSplits:<n>
                Maximal number of VC generated per method. In keep
                going mode only applies to the first round.
                Defaults to 1.
  /vcsMaxKeepGoingSplits:<n>
                If set to more than 1, activates the keep
                going mode, where after the first round of splitting,
                VCs that timed out are split into <n> pieces and retried
                until we succeed proving them, or there is only one
                assertion on a single path and it timeouts (in which
                case error is reported for that assertion).
                Defaults to 1.
  /vcsKeepGoingTimeout:<n>
                Timeout in seconds for a single theorem prover
                invocation in keep going mode, except for the final
                single-assertion case. Defaults to 1s.
  /vcsFinalAssertTimeout:<n>
                Timeout in seconds for the single last
                assertion in the keep going mode. Defaults to 30s.
  /vcsPathJoinMult:<f>
                If more than one path join at a block, by how much
                multiply the number of paths in that block, to accomodate
                for the fact that the prover will learn something on one
                paths, before proceeding to another. Defaults to 0.8.
  /vcsPathCostMult:<f1>
  /vcsAssumeMult:<f2>
                The cost of a block is
                    (<assert-cost> + <f2>*<assume-cost>) *
                    (1.0 + <f1>*<entering-paths>)
                <f1> defaults to 1.0, <f2> defaults to 0.01.
                The cost of a single assertion or assumption is
                currently always 1.0.
  /vcsPathSplitMult:<f>
                If the best path split of a VC of cost A is into
                VCs of cost B and C, then the split is applied if
                A >= <f>*(B+C), otherwise assertion splitting will be
                applied. Defaults to 0.5 (always do path splitting if
                possible), set to more to do less path splitting
                and more assertion splitting.
  /vcsDumpSplits
                For split #n dump split.n.dot and split.n.bpl.
                Warning: Affects error reporting.
  /vcsCores:<n>
                Try to verify <n> VCs at once. Defaults to 1.
  /vcsLoad:<f>  Sets vcsCores to the machine's ProcessorCount * f,
                rounded to the nearest integer (where 0.0 <= f <= 3.0),
                but never to less than 1.

  ---- Prover options --------------------------------------------------------

  /errorLimit:<num>
                Limit the number of errors produced for each procedure
                (default is 5, some provers may support only 1)
  /timeLimit:<num>
                Limit the number of seconds spent trying to verify
                each procedure
  /errorTrace:<n>
                0 - no Trace labels in the error output,
                1 (default) - include useful Trace labels in error output,
                2 - include all Trace labels in the error output
  /vcBrackets:<b>
                bracket odd-charactered identifier names with |'s.  <b> is:
                   0 - no (default with non-/prover:Simplify),
                   1 - yes (default with /prover:Simplify)
  /prover:<tp>  use theorem prover <tp>, where <tp> is either the name of
                a DLL containing the prover interface located in the
                Boogie directory, or a full path to a DLL containing such
                an interface. The standard interfaces shipped include:
                    SMTLib (default, uses the SMTLib2 format and calls Z3)
                    Z3 (uses Z3 with the Simplify format)
                    Simplify
                    ContractInference (uses Z3)
                    Z3api (Z3 using Managed .NET API)
  /proverOpt:KEY[=VALUE]
                Provide a prover-specific option (short form /p).
  /proverLog:<file>
                Log input for the theorem prover.  Like filenames
                supplied as arguments to other options, <file> can use the
                following macros:
                    @TIME@    expands to the current time
                    @PREFIX@  expands to the concatenation of strings given
                              by /logPrefix options
                    @FILE@    expands to the last filename specified on the
                              command line
                In addition, /proverLog can also use the macro '@PROC@',
                which causes there to be one prover log file per
                verification condition, and the macro then expands to the
                name of the procedure that the verification condition is for.
  /logPrefix:<str>
                Defines the expansion of the macro '@PREFIX@', which can
                be used in various filenames specified by other options.
  /proverLogAppend
                Append (not overwrite) the specified prover log file
  /proverWarnings
                0 (default) - don't print, 1 - print to stdout,
                2 - print to stderr
  /proverMemoryLimit:<num>
                Limit on the virtual memory for prover before
                restart in MB (default:100MB)
  /restartProver
                Restart the prover after each query
  /proverShutdownLimit<num>
                Time between closing the stream to the prover and
                killing the prover process (default: 0s)
  /platform:<ptype>,<location>
                ptype = v11,v2,cli1
                location = platform libraries directory

  Simplify specific options:
  /simplifyMatchDepth:<num>
                Set Simplify prover's matching depth limit

  Z3 specific options:
  /z3opt:<arg>  specify additional Z3 options
  /z3multipleErrors
                report multiple counterexamples for each error
  /useArrayTheory
                use Z3's native theory (as opposed to axioms).  Currently
                implies /monomorphize.
  /useSmtOutputFormat
                Z3 outputs a model in the SMTLIB2 format.
  /z3types      generate multi-sorted VC that make use of Z3 types
  /z3lets:<n>   0 - no LETs, 1 - only LET TERM, 2 - only LET FORMULA,
                3 - (default) any
  /z3exe:<path>
                path to Z3 executable

  CVC4 specific options:
  /cvc4exe:<path>
                path to CVC4 executable

```


