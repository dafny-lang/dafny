Building on Linux
=================

Tested on a fresh Ubuntu 16.04 image. Note that we now have
[official releases for Linux](https://github.com/Microsoft/dafny/releases), 
so these instructions mostly apply to people interested in looking at
Dafny's sources.

0. Dependencies: [Install Mono](http://www.mono-project.com/download/#download-lin) from the official repositories; the version in most distribution repositories is too out of date. The `mono-devel` package is what you need.

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
       git clone https://github.com/Microsoft/dafny.git 
       msbuild dafny/Source/Dafny.sln

4. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/)

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/z3-4.6.0-x64-ubuntu-16.04.zip
       unzip z3-4.6.0-x64-ubuntu-16.04.zip
       mv z3-4.6.0-x64-ubuntu-16.04 dafny/Binaries/z3

5. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

6. Run Dafny using the `dafny` shell script in the Binaries directory (it calls `mono` as appropriate)


Building on Mac OS X 
====================

Tested on Mac OS X 10.12.6 (Sierra).  Note that we now have
[official releases for Mac OS X](https://github.com/Microsoft/dafny/releases),
so these instructions mostly apply to people interested in looking at
Dafny's sources.

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
       git clone https://github.com/Microsoft/dafny.git 
       msbuild dafny/Source/Dafny.sln

4. Download and unpack z3 (Dafny looks for `z3` in Binaries/z3/bin/)

       cd BASE-DIRECTORY
       wget https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/z3-4.6.0-x64-osx-10.11.6.zip
       unzip z3-4.6.0-x64-osx-10.11.6.zip
       mv z3-4.6.0-x64-osx-10.11.6 dafny/Binaries/z3

5. (Optional) If you plan to use Boogie directly, copy (or symlink) the z3 binary so that Boogie, too, can find it:

       cd BASE-DIRECTORY
       rm -f boogie/Binaries/z3.exe
       cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe

6. Run Dafny using the `dafny` shell script in the Binaries directory (it calls mono as appropriate)


Editing in Emacs
================

The README at https://github.com/boogie-org/boogie-friends has plenty of
information on how to set-up Emacs to work with Dafny. In short, it boils down
to running [M-x package-install RET boogie-friends RET] and adding the following
to your .emacs:
    
    (setq flycheck-dafny-executable "BASE-DIRECTORY/dafny/Binaries/dafny")

Do look at the README, though! It's full of useful tips.
