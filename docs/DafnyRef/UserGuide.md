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

TO BE WRITTEN

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

There are a great many options that control various aspects of verifying dafny programs. Here we mention only a few:

- Control of output: `-dprint`, `-rprint`, `-stats`, `-compileVerbose`
- Whether to print warnings: `-proverWarnings`
- Control of time: `-timeLimit`
- Control of the prover used: `-prover`

TO BE WRITTEN - advice on use of verifier, debugging verification problems

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

* `-countVerificationErrors:<n>` - if 0 then always exit with a 0 exit code; if 1 (the default) then use the usual exit code

TO BE WRITTEN

### 24.10.3. Controlling output

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

TO BE WRITTEN

### 24.10.7. Controlling the prover

TO BE WRITTEN

### 24.10.8. Controlling compilation

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
   * `cpp` - C++
   * `php` - PHP

* `-spillTargetCode:<n>` - controls whether to write out compiled code in the target language (instead of just holding it in internal temporary memory)

   * 0 (default) - do not write out code
   * 1 - write it out to the target language, if it is being compiled
   * 2 - write the compiled program if it passes verification, regardless of the `-compile` setting
   * 3 - write the compiled program regardless of verification success and the `-compile` setting

* `-out:<file>` - TODO

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
