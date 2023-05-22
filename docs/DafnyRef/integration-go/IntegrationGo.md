---
title: Integrating Dafny and Go code
---

The Dafny compilation process translates Dafny programs into target language
source code, in particular a `.go` file, compiles the result, and then potentially runs the result. 

The Dafny-to-Go compiler writes out the translated files of a file _A_`.dfy`
to a folder _A_`-go/src`. The `-out` option can be used to choose a
different output folder. The file _A_`.dfy` is translated to _A_`.go`,
which is placed in the output folder along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
folder name is taken from the first file, but just
one `.go` file is written ithat combines the user source files, 
along with additional System and library `.go` files.

A multi-language program that combines Dafny and Go
code "just" needs to be sure that the translated Dafny code fits in
to the Go code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Go
- ensuring that the types are the same on both sides

## **The Dafny runtime library**

The step of compiling Go files requires the Dafny runtime library. That library is automatically included in the output files if `dafny` is doing the compilation,
but not if `dafny` is only doing translation.

## **Manually executing Dafny-generated Go code**

Suppose a Dafny program is contained in a `.dfy` file, `A.dfy`, which containingthe Dafny `Main` method. One can build the corresponding Go program (without running it) using this command:

`dafny build --target:go A.dfy`

The compiled program is then executed using the command `./A`
or `(cd A-go; GO111MODULE=auto GOPATH=\`pwd\` go run src/A.go)`

Alternatively the build and run steps can be combined:
`dafny run --target:go A.dfy`

## **Combining Go and Dafny source files**

The dafny tool is not yet able to automatically combined Go and Dafny source files.
