---
title: Installation Instructions
---

This page has instructions for installing Dafny by typical users:

* Using IDEs: [VSCode](#Visual-Studio-Code), [Emacs](#Emacs)
* Installing a binary build ([Windows](#windows-binary), [Linux](#linux-binary), or [Mac](#Mac-binary))
* [Installing the tools necessary to compile to other languages](#compiling-dafny)


* Instructions for creating an environment in which to develop Dafny and compile it from source 
are in the [Dafny project wiki](https://github.com/dafny-lang/dafny/wiki/INSTALL)

System Requirements
===================

The `dafny tool` is a .NET 8.0 artifact, but it compiles to native executables on supported platforms.
That and the Z3 tool are all that is needed to use dafny for verification; additional tools are 
need for compilation, as described below.

## Operating Systems

In addition to running dafny, the host OS must also be able to run the Z3 executable that is bundled with dafny.
(The Dafny tools are tested using github runners, which limits the set of platforms that can be tested.)

- Linux: `dafny` is tested on Ubuntu 20.04 and 22.04.
- MacOS: `dafny` is tested on MacOS 11 (Big Sur) and MacOS 12 (Monterey)
- Windows: `dafny` is tested on Windows 2019 and Windows 2022

## Compilers {#compiling-dafny}

The Dafny compiler performs two tasks:
- It translates a Dafny program into a target (source) programming language. This action requires only
the Dafny tool.
- The tool launches external processes, including the target language tools installed on the host OS,
to compile and run the previously generated source code.

In addition, the Dafny toolkit supplies runtime libraries, either in source form or compiled for the target programming language.

### C#

- Dafny targeting C# produces C#10-compatible source code.
- Only the .NET 8.0 set of tools (which includes the C# compiler) is needed to compile and run the generated C# code.
- The Dafny runtime library is included as C# source along with the generated C# code, so the user can compile those sources
and any user code in one project.

### Java

- Dafny targeting Java produces Java 8-compatible source.
- The 'javac', 'jar, and 'java' executables are needed on the host system to compile and run Dafny-generated Java source code.
- A Dafny-produced Java program must be run with the supplied DafnyRuntime.jar. This jar is compiled to run with Java 8.

### Javascript

- Dafny targeting Javascript produces Javascript source consistent with Node.js v 16.0.0

### Python

- Dafny targeting Python produces targets Python 3.7 source.
- Only the python executable is needed to compile and run Dafny-generated Python source code.
- The Dafny runtime library is included as source, so both the generated code, the library and any user python code can be compiled together
with the user's choice of python tool (that compiles at least 3.7).

### Go

- Dafny targeting Go produces Go source content consistent with Go 1.18.

### Rust

- Partial and growing support

### C++

C++ has only rudimentary special purpose support at present.


Using an IDE
============

The easiest way to get started with Dafny is using the Dafny IDEs, since they continuously run the verifier in
the background. Be sure to check out the [Dafny tutorial](https://dafny.org/latest/OnlineTutorial/guide)!

For most users, we recommend using Dafny with VS Code, which has an easy installation, as explained next:

## Visual Studio Code {#Visual-Studio-Code}

0. Install [Visual Studio Code](https://code.visualstudio.com/)
1. If you are on a Mac or Linux, install .NET 8.0, as described under those platforms below.
2. In Visual Studio Code, press `Ctrl+P` (or `⌘P` on a Mac), and enter `ext install dafny-lang.ide-vscode`.
3. If you open a `.dfy` file, Dafny VSCode will offer to download and install the latest Dafny. You can also browse extensions:
  ![vs-code-dafny-2 0 1-install](https://user-images.githubusercontent.com/3601079/141353551-5cb5e23b-5536-47be-ba17-e5af494b775c.gif)

## Emacs {#Emacs}

The README at [https://github.com/boogie-org/boogie-friends](https://github.com/boogie-org/boogie-friends) has plenty of
information on how to set-up Emacs to work with Dafny. In short, it boils down
to running `[M-x package-install RET boogie-friends RET]` and adding the following
to your `.emacs`:
```
(setq flycheck-dafny-executable "[path to dafny]/dafny/Scripts/dafny")
```

Do look at the README, though! It's full of useful tips.



Install the binaries from the github releases
=============================================

The following instructions
tell you how to install Dafny so that you can run it from various operating systems as a command-line tool.

If you wish to compile to target languages, see the instructions in a subsequent section to
install the correct dependencies for the desired language.

## Windows (Binary) {#windows-binary}

To install Dafny on your own machine, 

* Install (if not already present) .NET Core 8.0: `https://dotnet.microsoft.com/download/dotnet/8.0`
* Download the windows zip file from the [releases page](https://github.com/dafny-lang/dafny/releases/latest) and **save** it to your disk. 
* Then, **before you open or unzip it**, right-click on it and select Properties; at the bottom of the dialog, click the **Unblock** button and then the OK button. 
* Now, open the zip file and copy its contents into a directory on your machine. (You can now delete the zip file.)

Then:

-   To run Dafny from the command line, simply run `Dafny.exe`.

## Linux (Binary) {#linux-binary}

To install a binary installation of dafny on Linux (e.g., Ubuntu), do the following:
* Install .NET 8.0. See: `https://docs.microsoft.com/dotnet/core/install/linux` or `sudo apt install dotnet-sdk-8.0`
* Install the Linux binary version of Dafny, from `https://github.com/dafny-lang/dafny/releases/latest`
* Unzip the downloaded file in a (empty) location of your choice

Within the unzipped Linux distribution, the dafny executable is `dafny/dafny`

If you intend to use the Dafny compiler, install the appropriate tools as described [here](#compiling-dafny)

After the compiler dependencies are installed, you can run a quick test of the installation by running the script 
`$INSTALL/dafny/quicktest.sh`

## Mac (Binary) {#Mac-binary}

To install a binary installation of Dafny on macOS, do one of the following:

Either  
   * Install the Mac binary version of Dafny, from `https://github.com/dafny-lang/dafny/releases/latest`
   * Unzip the downloaded file in a (empty) location of your choice (`$INSTALL`)
   * `cd` into the installation directory (`$INSTALL/dafny`) and run the script `./allow_on_mac.sh`
   * Dafny is run with the command `$INSTALL/dafny/dafny`

or
   * Install Dafny using brew, with the command `brew install dafny` (the version on brew sometimes lags the
     project release page)
   * Run Dafny with the command `dafny`

If you intend to use the Dafny compiler, install the appropriate tools as described [here](#compiling-dafny).

After the compiler dependencies are installed, you can run a quick test of the installation by running the script 
`$INSTALL/dafny/quicktest.sh`

## NuGet (Binary)

The .NET [NuGet](https://www.nuget.org/) repository collects .NET libraries and tools for easy installation. Dafny is available on NuGet, and can be installed as follows:

* Install .NET 8.0 as described for your platform in one of the subsections above.
* Install a binary version of Z3 4.12.1 for your platform from its [GitHub releases page](https://github.com/Z3Prover/z3/releases/tag/Z3-4.12.1) and put the `z3` executable in your `PATH`.
* Install Dafny using `dotnet tool install --global dafny` (or leave out the `--global` to use with `dotnet tool run` from the source directory of a .NET project).


## Compiling Dafny {#compiling-dafny}

The instructions here describe the dependencies needed to have the tools to compile to various languages
and the procedure to use for simple programs.

Note that a pure Dafny program (say `A.dfy`) can be compiled and run in one step using `dafny run A.dfy`
and can be run for a particular programming language with the `--target` option (the default target is C#). 
Additional instructions are found in the [Dafny User Guide](DafnyRef/DafnyRef#sec-dafny-run).

### C# (.Net)

Install .NET 8.0:
* Windows) `https://dotnet.microsoft.com/download/dotnet/8.0`
* Linux) Install .NET 8.0. See: `https://docs.microsoft.com/dotnet/core/install/linux` or `sudo apt install dotnet-sdk-8.0`
* Mac) Install .NET 8.0: `brew install dotnet-sdk` or from `https://docs.microsoft.com/dotnet/core/install/macos`


To separately compile and run your program for .NET:
- `dafny build -t:cs MyProgram.dfy`
- `MyProgram.exe`


### Javascript

To set up Dafny to compile to JavaScript (node.js):
* Install node.js from [https://nodejs.org/en/download](https://nodejs.org/en/download) or
   * Linux: `sudo apt install nodejs npm` and make sure `node` and `npm` are on your path
   * Mac: `brew install node`

To separately compile and run your program for JavaScript:
- `npm install bignumber.js`
- `dafny build -t:js MyProgram.dfy`
- `node MyProgram.js`

### Go

To set up Dafny to compile to Go:
* Install Go from [https://golang.org/dl](https://golang.org/dl) or
   * Linux: `sudo apt install golang`
   * Mac: `brew install golang`
* Install `goimports` from [https://pkg.go.dev/golang.org/x/tools/cmd/goimports](https://pkg.go.dev/golang.org/x/tools/cmd/goimports)
   * `go install golang.org/x/tools/cmd/goimports@latest`
* Make sure `go` and `goimports` are on your path

To separately compile and run your program for Go:
- `dafny build --target:go MyProgram.dfy`
- `./MyProgram` or ``(cd MyProgram-go; GO111MODULE=auto GOPATH=`pwd` go run src/MyProgram.go )``

### Java

To set up Dafny to compile to Java:
* Install Java (at least Java 8) from https://www.oracle.com/java/technologies/javase-downloads.html
  or install Amazon Corretto from https://docs.aws.amazon.com/corretto/latest/corretto-11-ug/what-is-corretto-11.html
  (see the platform-specific links on the left of that page)
  or, on a Mac, `brew install java`
* Install [gradle](https://gradle.org/) or, on a Mac, `brew install gradle`

To separately compile and run your program for Java:
- `dafny build -t:java MyProgram.dfy`
- `java -jar MyProgram.jar`

### Python

To setup Dafny to compile to python3:
* Install python3:
   * Windows)
   * Linux)
   * Mac) Likely already installed in the MacOS, but otherwise use `brew install python3`

To separately compile and run your program for Python:
- `dafny build -t:py MyProgram.dfy`
- `python3 MyProgram-py/MyProgram.py`

### Rust

To setup Dafny to compile to Rust:
* Install Rust from https://rustup.rs/
