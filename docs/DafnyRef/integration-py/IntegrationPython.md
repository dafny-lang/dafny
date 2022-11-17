---
title: Integrating Dafny and Python code
---

The Dafny compilation process translates Dafny programs into target language
source code and then potentially runs the result. 

The Dafny-to-Python compiler writes out the translated files of a file _A_`.dfy`
to a folder _A_`-py`. The `-out` option can be used to choose a
different output folder. The input `.dfy` files are translated to various `.py` files 
which are placed in the output folder along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
folder name is taken from the first file.

A multi-language program that combines Dafny and Python
code "just" needs to be sure that the translated Dafny code fits in
to the Python code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Python
- ensuring that the types are the same on both sides

## **The Dafny runtime library**

The step of compiling or running Python files requires the Dafny runtime library for Python. That library is automatically included if `dafny` is doing the compilation,
but not if `dafny` is only doing translation.

## **Manually executing Dafny-generated Python code**

Suppose a Dafny program is contained in a `.dfy` file, `A.dfy`, which also contains the `Main` method. One can build the corresponding Java program (without running it) using this command:

`dafny build --target:py A.dfy`

The compiled program is then executed using the command
`PYTHONPATH=A-py python3 A-py/A.py`
or
`(cd A-py; python3 A.py)`

Alternatively the build and run steps can be combined:
`dafny run --target:py A.dfy`

If there are multiple `.dfy` files, general practice has the dependencies included within their client files using Dafny `include` directives.

## **Combining Python and Dafny**

Combining Python and Dafny source is complicated by two things.
- To run a python program, `python` is invoked on the one `.py` file that
contains the python `main` method. However, currently (as of v3.9.1) dafny only
detects `main` methods in the `.py` files created from `.dfy` files.
- For dafny to call python methods in some separate `.py` file, the
calling file must `import` the called file (module). There is no syntax in
Dafny to insert such `import` statements in the `.py` file generated from
a `.dfy` file.

When the `main` is in a `.py` file, proceed as in this example:

In Demo2.dfy:
```dafny
module {:extern "M"} M {
  class C {
    static method p() {
      print "Hello, World\n";
    }
  }
}
```

In Demo2x.py
```python
import M

def main():
    print("Hi");
    M.C.p();

main()
```

And then execute these commands:
```
dafny build --target:py Demo2.dfy
PYTHONPATH=.:Demo2-py python3 Demo2x.py
```
The first command translates `Demo2.dfy` into a `.py` file; by using `build`,
all the supporting runtime library routines are included as well.
The second command then uses `python` to execute the `main()` method in
`Demo2x.py`, which imports the module `M` from `Demo2` and calls `M.C.p()`.

To call python from Dafny, one must edit the trnaslation of the `.dfy` file to 
add the needed imports.

## **Matching Dafny and Python types**

The correspondence between the Dafny and Python types is shown in this table.

|-------------------------------|-----------------------------|
|  Dafny type                   |   Python type                 |
|-------------------------------|-----------------------------|
| bool                          | bool                     |
| int                           | int        |
| int64                         | int                        |
| int32                         | int                         |
| int16                         | int                       |
| int8                          | int                        |
| char                          | int                        |
| bitvector                     | int  |
| ORDINAL                       | int        |
| real                          | _dafny.BigRational           |
|                               | float                       |
| string                        | _dafny.Seq  |
| ?                             | str                        |
| C, C? (for class, iterator C) | class                   |
| (trait) T                     | class                |
| datatype, codatatype          | class                   |
| subset type                   | same as base type           |
| tuple                         | (python) tuple              |
| array<T>                      | _dafny.Array                       |
| seq<T>                        | _dafny.Seq |
| set<T>, iset<T>               | _dafny.Set      |
| multiset<T>                   | _dafny.MultiSet      |
| map<T,U>, imap<T,U>           | _dafny.Map      |
| imap<T,U>, imap<T,U>          | _dafny.Map      |
| function (arrow) types        | class 'function' |
|-------------------------------|------------------------------|

