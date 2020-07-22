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

- To install Dafny for use inside Visual Studio 2012, double-click on
    `DafnyLanguageService.vsix` to run the installer. You may first need
    to uninstall the old version of the extension from within Visual
    Studio (Tools ==\> Extensions and Updates). Then, whenever you open a
    file with the extension .dfy in Visual Studio, the Dafny mode will
    kick in. (If you don't intend to run Dafny from the command line, you
    can delete the directory into which you copied the contents of
    Dafny.zip.)

- There is also a [Dafny mode for
    Emacs](https://github.com/boogie-org/boogie-friends).

**Linux and Mac:** Make sure you have Mono version 4. Then save the
contents of the Dafny.zip for the appropriate version of your platform.
You can now run Dafny from the command line by invoking the script file
`dafny`. For an IDE, use the [Dafny mode for
Emacs](https://github.com/boogie-org/boogie-friends).

**Mac using brew:** On a Mac, you can install dafny, along with its dependencies, mono and z3,  using the `brew` package manager.

## Building Dafny from Source
The current version of the Dafny executable builds and runs with Visual Studio 2012 or later,
but the Visual Studio extensions for Dafny currently only build with Visual Studio 2012.
So if you intend to run Dafny from within Visual Studio (using extensions that you have
built yourself), you must install Visual Studio 2012.

First, install the following external dependencies:

-   Visual Studio 2012 Ultimate

-   [Visual Studio 2012 sdk extension](https://visualstudiogallery.msdn.microsoft.com/b2fa5b3b-25eb-4a2f-80fd-59224778ea98)

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
    -   For `"C\#:Formatting:NewLines` Turn everything off except the first option.


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

Download and install the Visual Studio 2012 SDK from

* <https://www.microsoft.com/en-us/download/details.aspx?id=30668>.

This is needed to build the Visual Studio Extension that
runs Dafny from within Visual Studio 2012.

Build the command-line Dafny executables.
1. Open dafny/Source/Dafny.sln in Visual Studio
2. Click BUILD > Build Solution.

Build and install the Dafny Visual Studio extensions

1. Open dafny/Source/DafnyExtension.sln in Visual Studio
2. Click BUILD > Build Solution.
3. This builds DafnyLanguageService.vsix and DafnyMenu.vsix
in the dafny/Binaries directory.
4. Install these by clicking on them from Windows Explorer. When
prompted, check installing into Visual Studio 2012, and optionally
also for later versions of Visual Studio if you have installed them.

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

As a command-line tool, Dafny operates just like other command-line tools
in Windows and Unix-like systems.

- The format of a command-line is determined by the shell program that is executing the command-line (.e.g. bash, the windows shell, COMMAND, etc.). The command-line typically consists of file names and options, in any order, separated by spaces. 
- Files are designated by absolute paths or paths relative to the current 
working directory. Command-line argument not matching a known option is considered a filepath.
- Files containing dafny code must have a `.dfy` suffix.
- There must be at least one .dfy file.
- The command-line may contain other kinds of files appropriate to 
the language that the dafny files are being compiled to.

The command-line options are documented [here](#options).

- Options may begin with either a `/` (as is typical on Windows) or a `-` (as is typical on Linux)
- If an option is repeated (e.g. with a different argument), then the later instance on the command-line supercedes the earlier instance.
- If an option takes an argument, the option name is followed by a `:` and then by the argument value, with no
intervening white space; if the argument itself contains white space, the argument must be enclosed in quotes.
- Escape characters are determined by the shell executing the command-line. 

The dafny tool performs several tasks:

- Checking the form of the text in a .dfy file. This step is always performed, unless the tool is simply asked for
help information or version number.
- Running the verification engine to check all implicit and explicit specifications. This step is performed by
default, but can be skipped by using the `-noVerify` or `-dafnyVerify:0` option
- Compiling the dafny program to a target language. This step is performed by default if the verification is
successful but can be skipped or always executed by using variations of the `-compile` option.
- Whether the source code of the compiled target is written out is controlled by `-spillTargetCode`
- The particular target language used is chosen by `-compileTarget`
- Whether or not the dafny tool attempts to run the compiled code is controlled by `-compile`

## Verification

There are a great many options that control various aspects of verifying dafny programs. Here we mention only a few:

- Control of output: `-nologo`, `-dprint`, `-rpiomnt`, `-stats`, `-compileVerbose`
- Whether to print warnings: `-proverWarnings`
- Control of time: `-timeLimit`
- Control of the prover used: `-prover`

TO BE WRITTEN - advice on use of verifier, debugging verification problems

## Compilation

The dafny tool can compile a dafny program to one of several target languages. Details and idiosyncracies of each
of these are described in the following subsections. In general note that,

- the compiled code originating from dafny can be compiled with other source and binary code, but only the dafny-originated code is verified
- the output file names can be set using `-out`
- for each target language, there is a runtime library that must be used with the dafny-generated code when executing that code
- names in dafny are written out as names in the target language. In some cases this can result in naming conflicts.
Thus if  dafny program is intended to be compiled to a target language X, you should avoid using dafny identifiers
that are not legal identifiers in X or that conflict with reserved words in X.


TODO - location of DafnyRuntime files

### C#

TO BE WRITTEN

### Java

TO BE WRITTEN

### Javascript

TO BE WRITTEN 

### Go

TO BE WRITTEN

### C++

The C++ back-end is still very preliminary and is available for experimentation only.

TO BE WRITTEN


## Dafny Command Line Options {#options}
The command `Dafny.exe /?` gives the following description of
options that can be passed to Dafny.

{% include Options.txt %}
