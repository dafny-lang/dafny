Building on Linux
=================

Originally written for a fresh Ubuntu 16.04 image, updated by testing on Fedora 29. Note that we now have [official releases for Linux](https://github.com/dafny-lang/dafny/releases),
so these instructions mostly apply to people interested in looking at Dafny's sources or who want to use the latest features from the master branch.

0. Dependencies: [Install .NET](https://dotnet.microsoft.com/download)

1. Create an empty base directory

       mkdir BASE-DIRECTORY
       cd BASE-DIRECTORY

2. Download and build Dafny:

       cd BASE-DIRECTORY
       git clone https://github.com/dafny-lang/dafny.git --recurse-submodules
       dotnet build dafny/Source/Dafny.sln

3. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/). To know which version to install, read the commit message of the latest commit in the [history](https://github.com/dafny-lang/dafny/commits/master/Binaries/z3.exe) of `Binaries/z3.exe`.

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
       unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
       mv z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04 dafny/Binaries/z3

4. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

5. Run Dafny using the `dafny` shell script in the Binaries directory

6. In Visual Studio Code, open any `.dfy` file, and when asked if you want to install the Dafny extension, click "install". This will install both the latest release of Dafny (which you decided not to use), but also the editor extension (which you want to use with your locally compiled Dafny version). To make sure the editor extension uses your locally compiled Dafny version, open the Settings page, search for "dafny base path", and set it to `BASE-DIRECTORY/dafny/Binaries`.

7. (Optional -- for testing) The Dafny test infrastructure uses a python tool 'lit'. Install it as follows:
   * install python (https://www.python.org/downloads/)
   * install pip (https://pip.readthedocs.io/en/stable/installing/)
   * run "pip install lit" and "pip install OutputCheck"
Navigate to the Test directory in the repo and run 'lit .'
The tests take a while, depending on your machine, but emit progress output.

Building on Mac OS X
====================

You can use [Homebrew](https://brew.sh) to install Dafny:

       brew install dafny

Tested on Mac OS X 10.12.6 (Sierra).  Note that we now have
[official releases for Mac OS X](https://github.com/dafny-lang/dafny/releases),
so these instructions mostly apply to people interested in looking at
Dafny's sources or who want to use the latest features from the master branch.

0. Dependencies: [Install .NET](https://dotnet.microsoft.com/download)

1. Create an empty base directory

       mkdir BASE-DIRECTORY
       cd BASE-DIRECTORY

2. Download and build Dafny:

       cd BASE-DIRECTORY
       git clone https://github.com/dafny-lang/dafny.git --recurse-submodules
       dotnet build dafny/Source/Dafny.sln

3. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/). To know which version to install, read the commit message of the latest commit in the [history](https://github.com/dafny-lang/dafny/commits/master/Binaries/z3.exe) of `Binaries/z3.exe`.

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
       unzip z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
       mv z3-4.8.4.d6df51951f4c-x64-osx-10.14.1 dafny/Binaries/z3

4. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

5. Run Dafny using the `dafny` shell script in the Binaries directory (it calls mono as appropriate)

6. In Visual Studio Code, open any `.dfy` file, and when asked if you want to install the Dafny extension, click "install". This will install both the latest release of Dafny (which you decided not to use), but also the editor extension (which you want to use with your locally compiled Dafny version). To make sure the editor extension uses your locally compiled Dafny version, open the Settings page, search for "dafny base path", and set it to `BASE-DIRECTORY/dafny/Binaries`.

7. (Optional -- for testing) The Dafny test infrastructure uses a python tool 'lit'. Install it as follows:
   * install python (use `brew install python3`, or see https://www.python.org/downloads/)
   * install pip (above `brew` command will install it, or see https://pip.readthedocs.io/en/stable/installing/)
   * run `pip install lit` and `pip install OutputCheck`
   * (Optional) Install java (possibly use `brew cask install java` and then `java -version`)
   * Navigate to the Test directory in the repo and run `lit .`. The tests take a while, depending on your machine, but emit progress output.

8. (Optional -- building the reference manual pdf) --- currently only on Linux and MacOS
i	make -C BASE-DIRECTORY refman
   * The reference manual html does not require building. It is at
	https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef
   * The reference manual pdf is at 
        BASE-DIRECTORY/docs/DafnyReferenceManual/DafnyRef.pdf
