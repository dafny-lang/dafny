<!--PDF NEWPAGE-->
# 26. Dafny User's Guide {#user-guide}

Most of this document decribes the Dafny programming langauge.
This section describes the `dafny` tool, a combined verifier and compiler
that implements the Dafny language.

The development of the dafny language and tool is a GitHub project at [https://github.com/dafny-lang/dafny](https://github.com/dafny-lang/dafny).
The project is open source, with collaborators from various organizations and additional contributors welcome.
The software itself is licensed under the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).

## 26.1. Introduction

The dafny tool implements the following capabilities:

- checking that the input files represent a valid Dafny program (i.e., syntax, grammar and type checking);
- verifying that the program meets its specifications, by translating the program to verification conditions
and checking those with Boogie and an SMT solver, typically Z3;
- compiling the program to a target language, such as C#, Java, Javascript, Go (and others in development);
- running the executable produced by the compiler.

Using various command-line flags, the tool can perform various combinations of the last three actions (the first
action is always performed).

## 26.2. Dafny Programs and Files

A Dafny program is a set of modules.
Modules can refer to other modules, such as through `import` declarations
or `refines` clauses.
A Dafny program consists of all the modules needed so that all module
references are resolved.

Dafny files (`.dfy`) in the operating system each hold
the declarations of some number of modules. Thus a full program may be
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
in which the files without dependences are checked first, then those that
depend on them, etc., until all files are checked.

[^fn-duplicate-files]: File names are considered equal if they
have the same absolute path, reduced to lower case, even on file
systems that support case-sensitive file names.
Use of symbolic links
may make the same file have a different absolute path; this will generally
cause duplicate declaration errors.

## 26.3. Installing Dafny From Binaries

Current and past Dafny binary releases can be found at
[https://github.com/dafny-lang/dafny/releases](https://github.com/dafny-lang/dafny/releases) for each supported platform.
Each release is a .zip file with a name combining the release name and the
platform. For convenience we will call that zip file `Dafny.zip`, though the
names generally are something like `dafny-3.0.0-pre-1-x64-ubuntu-16.04.zip`.

### 26.3.1. Windows
To install Dafny on your own machine, download Dafny.zip and
**save** it to your disk. Then, before you open or unzip it, right-click
on it and select Properties; at the bottom of the dialog, click the
Unblock button and then the OK button. Now, open Dafny.zip and copy its
contents into a clean, new directory (called `$DAFNY` subsequently)
on your machine. (You can now delete the
Dafny.zip file.)

Then: To run Dafny from the command line, simply run dafny.exe from the
    `$DAFNY/dafny/Binaries` directory.

### 26.3.2. Linux and Mac
Make sure you have Mono version 4. Then save the
contents of the Dafny.zip for the appropriate version of your platform.
You can now run Dafny from the command line by invoking the script file
`$DAFNY/dafny/Binaries/dafny`.

### 26.3.3. Mac using brew
 On a Mac, you can install dafny, along with its dependencies, mono and z3,  using the `brew` package manager.
If `brew` is installed, simply issue the command `brew install dafny`.
The tool is executed as `$DAFNY/dafny/Binaries/dafny`.
(Monno is needed; it is also available from `brew`


## 26.4. Building Dafny from Source

### 26.4.1. Dependencies

TO BE WRITTEN

The current version of the Dafny executable builds and runs with Visual Studio 2012 or later.

### 26.4.2. Installing the source code

The source code is available from github, by cloning the repository:

* create a new directory of your choice (here called $DAFNY)
* make it the current working directory (i.e., `cd` to it)
* Issue the command `git clone https://github.com/dafny-lang/dafny.git`

### 26.4.3. Building the source code

TO BE WRITTEN

### 26.4.4. Running the executable

After a successful build, the executable to run is

* `$DAFNY/dafny/Binaries/dafny.exe` on windows and
* `$DAFNY/dafny/Binaries/dafny` on linux-like and mac platforms.

### 26.4.5. Running tests

To install lit (for test run):
    -   first, install [python](https://www.python.org/downloads/)
    -   second, install [pip](http://pip.readthedocs.org/en/stable/installing/)
    -   last, run "pip install lit" and "pip install OutputCheck"

Then, to run all the tests,

* `lit $DAFNY/dafny/Test`

The argument to the `lit` command can be any number of .dfy files or folders
containing .dfy files (all of which must be under the `Test` directory).


## 26.5. IDEs for Dafny

Dafny source files are text files and can of course be edited with any
text editor. However, some tools provide syntax-aware features:

- There is a [Dafny mode for
    Emacs](https://github.com/boogie-org/boogie-friends).

- VSCode, a cross-platform editor for many programming languages has an extension for dafny, installed from within VSCode. VSCode is available [her](http://code.visualstudio.com). The extension provides syntax highlighting, in-line parser, type and verification errors, and code navigation.

## 26.6. Dafny Code Style

There are code style conventions for Dafny code, recorded [here](https://dafny-lang.github.io/dafny/StyleGuide/Style-Guide).
Most significantly, code is written without tabs and with a 2 space indentation.
## 26.7. Using Dafny From Visual Studio

1. Open dafny/Source/Dafny.sln in Visual Studio
2. Click BUILD > Build Solution.

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

## 26.8. The Dafny Server

TO BE WRITTEN

## 26.9. Using Dafny From the Command Line

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
by the tool. The most commonly used options are described [here](#options).

- Options may begin with either a `/` (as is typical on Windows) or a `-` (as is typical on Linux)
- If an option is repeated (e.g., with a different argument), then the later instance on the command-line supercedes the earlier instance.
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

## 26.10. Verification

There are a great many options that control various aspects of verifying dafny programs. Here we mention only a few:

- Control of output: `-nologo`, `-dprint`, `-rprint`, `-stats`, `-compileVerbose`
- Whether to print warnings: `-proverWarnings`
- Control of time: `-timeLimit`
- Control of the prover used: `-prover`

TO BE WRITTEN - advice on use of verifier, debugging verification problems

## 26.11. Compilation

The dafny tool can compile a Dafny program to one of several target languages. Details and idiosyncracies of each
of these are described in the following subsections. In general note that,

- the compiled code originating from dafny can be compiled with other source and binary code, but only the dafny-originated code is verified
- the output file names can be set using `-out`
- for each target language, there is a runtime library that must be used with the dafny-generated code when executing that code; the runtime libraries are
part of the Binary and Source releases (typically in the Binaries folder)
- names in Dafny are written out as names in the target language. In some cases this can result in naming conflicts.
Thus if a Dafny program is intended to be compiled to a target language X, you should avoid using Dafny identifiers
that are not legal identifiers in X or that conflict with reserved words in X.


TODO - location of DafnyRuntime files

### 26.11.1. Main method

To generate a stand-alone executable from a Dafny program, the
Dafny program must contain exactly one method named `Main`, with no input arguments.
This `Main` method is the entry point for the program.
Without a `Main` method, dafny will still produce executable output files, but
they will need to be linked with some other code in the target language that
provides a `main` entry point.

TO BE WRITTEN

TODO - non-static main in a class.

### 26.11.2. extern declarations

TO BE WRITTEN

### 26.11.3. C\#

TO BE WRITTEN

### 26.11.4. Java

TO BE WRITTEN

### 26.11.5. Javascript

TO BE WRITTEN

### 26.11.6. Go

TO BE WRITTEN

### 26.11.7. C++

The C++ back-end is still very preliminary and is available for experimentation only.

TO BE WRITTEN


## 26.12. Dafny Command Line Options {#options}

There are many command-line options to the `dafny` tool.
The most current documentation of the options is within the tool itself,
using the `/?` option.
Here we give an expanded description of the most important options.

Remember that options can be stated with either a leading `/` or a leading `-`.

### 26.12.1. Help and version information

* `-?` or `-help` : prints out the current list of command-line options and terminates
* `-version` : prints the version of the executable being invoked and terminates

### 26.12.2. Controlling errors and exit codes

* `-countVerificationErrors:<n>` - if 0 then always exit with a 0 exit code; if 1 (the default) then use the usual exit code

TO BE WRITTEN

### 26.12.3. Controlling output

* `-dprint:<file>` - print the Dafny program after parsing (use `-` for `<file> to print to the console)

* `-rprint:<file>` - print the Dafny program after type resolution (use `-` for <file> to print to the console)

TO BE WRITTEN

### 26.12.4. Controlling aspects of the tool being run

* `-deprecation:<n>` - controls warnings about deprecated features

   * 0 - no warnings
   * 1 (default) - issue warnings
   * 2 - issue warnings and advise about alternate syntax

* `-warnShadowing` - emits a warning if the name of a declared variable caused another variable to be shadowed

TO BE WRITTEN

### 26.12.5. Controlling verification

* `-verifyAllModules` - verify modules that come from include directives (default is to not verify included modules)
TO BE WRITTEN

### 26.12.6. Controlling boogie

TO BE WRITTEN

### 26.12.7. Controlling the prover

TO BE WRITTEN

### 26.12.8. Controlling compilation

* `-compile:<n>` - controls whether compilation happens

   * 0 - do not compile the program
   * 1 (default) - upon successful verification, compile the program to the target language
   * 2 - always compile, regardless of verification success
   * 3 - if verification is successful, compile the programi (like option 1), and then if there is a `Main` method, attempt to run the program
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

### 26.12.9. Options intended for debugging

* `-dprelude:<file>` - choose an alternate prelude file
* `-pmtrace` - print pattern-match compiler debugging information
* `-titrace` - print type inference debugging information

TO BE WRITTEN

## 26.13. Full list of -command-line options <!-- PDFOMIT -->
For the on-line version only, the output of `dafny /?` follows: <!--PDFOMIT-->
{% include Options.txt %} <!-- PDFOMIT -->
