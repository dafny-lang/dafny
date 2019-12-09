Building on Linux
=================

Originally written for a fresh Ubuntu 16.04 image, updated by testing on Fedora 29. Note that we now have [official releases for Linux](https://github.com/dafny-lang/dafny/releases),
so these instructions mostly apply to people interested in looking at Dafny's sources or who want to use the latest features from the master branch.

0. Dependencies: [Install Mono](https://www.mono-project.com/download/stable/#download-lin) from the official repositories; the version in most distribution repositories is too out of date. The `mono-devel` package is what you need. On Fedora, you'll also need the `msbuild` package.

1. Create an empty base directory

       mkdir BASE-DIRECTORY
       cd BASE-DIRECTORY

2. Download and build Boogie:

       git clone https://github.com/boogie-org/boogie
       cd boogie
       wget https://nuget.org/nuget.exe
       mono ./nuget.exe restore Source/Boogie.sln
       msbuild Source/Boogie.sln
       cd ..

3. Download and build Dafny:

       cd BASE-DIRECTORY
       git clone https://github.com/dafny-lang/dafny.git
       msbuild dafny/Source/Dafny.sln

4. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/). To know which version to install, read the commit message of the latest commit in the [history](https://github.com/dafny-lang/dafny/commits/master/Binaries/z3.exe) of `Binaries/z3.exe`.

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
       unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
       mv z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04 dafny/Binaries/z3

5. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

6. Run Dafny using the `dafny` shell script in the Binaries directory (it calls `mono` as appropriate)

7. In Visual Studio Code, open any `.dfy` file, and when asked if you want to install the Dafny extension, click "install". This will install both the latest release of Dafny (which you decided not to use), but also the editor extension (which you want to use with your locally compiled Dafny version). To make sure the editor extension uses your locally compiled Dafny version, open the Settings page, search for "dafny base path", and set it to `BASE-DIRECTORY/dafny/Binaries`.


Building on Mac OS X
====================

You can use [Homebrew](https://brew.sh) to install Dafny:

       brew install dafny

Tested on Mac OS X 10.12.6 (Sierra).  Note that we now have
[official releases for Mac OS X](https://github.com/dafny-lang/dafny/releases),
so these instructions mostly apply to people interested in looking at
Dafny's sources or who want to use the latest features from the master branch.

0. Dependencies (using [Homebrew](https://brew.sh))

       brew install mono
       brew cask install mono-mdk

1. Create an empty base directory

       mkdir BASE-DIRECTORY
       cd BASE-DIRECTORY

2. Download and build Boogie:

       git clone https://github.com/boogie-org/boogie
       cd boogie
       wget https://nuget.org/nuget.exe
       mono ./nuget.exe restore Source/Boogie.sln
       msbuild Source/Boogie.sln
       cd ..

    Note: If the xbuild step above fails, try running it again.

3. Download and build Dafny:

       cd BASE-DIRECTORY
       git clone https://github.com/dafny-lang/dafny.git
       msbuild dafny/Source/Dafny.sln

4. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/). To know which version to install, read the commit message of the latest commit in the [history](https://github.com/dafny-lang/dafny/commits/master/Binaries/z3.exe) of `Binaries/z3.exe`.

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
       unzip z3-4.8.4.d6df51951f4c-x64-osx-10.14.1.zip
       mv z3-4.8.4.d6df51951f4c-x64-osx-10.14.1 dafny/Binaries/z3

5. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

6. Run Dafny using the `dafny` shell script in the Binaries directory (it calls mono as appropriate)

7. In Visual Studio Code, open any `.dfy` file, and when asked if you want to install the Dafny extension, click "install". This will install both the latest release of Dafny (which you decided not to use), but also the editor extension (which you want to use with your locally compiled Dafny version). To make sure the editor extension uses your locally compiled Dafny version, open the Settings page, search for "dafny base path", and set it to `BASE-DIRECTORY/dafny/Binaries`.
