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

Suppose a Dafny program is contained in a `.dfy` file, `A.dfy`, which contains the Dafny `Main` method. One can build the corresponding Go program (without running it) using this command:

`dafny build --target:go A.dfy`

The compiled program is then executed using the command `./A`
or `(cd A-go; GO111MODULE=auto GOPATH=\`pwd\` go run src/A.go)`

Alternatively the build and run steps can be combined:
`dafny run --target:go A.dfy`

## **Combining Go and Dafny source files**

The dafny tool is not yet able to automatically combined Go and Dafny source files.

## **Equality of extern types**

A Dafny `class` or `trait` has object identity, and the verifier assumes that `==`
and the built-in collections compare such values by identity.

An extern Go type must implement the runtime's `EqualsGeneric` interface to be
compared correctly. This is the opposite of what the other backends require: in
C# and Java an extern class inherits reference equality and is correct as written,
so the guidance there is to leave `Equals` alone. Go's default is structural, so
an extern type has to opt in to identity. Dafny cannot supply the implementation,
because Go does not allow methods to be declared on a type belonging to another
package. Where it is
missing, the runtime's `AreEqual` falls back to `reflect.DeepEqual`, which follows
the pointer and compares the pointees structurally; two distinct objects that
happen to hold equal fields then compare equal, contradicting what the verifier
proved. Direct `==` on an extern class is unaffected, since it compiles to Go's
`==`; the discrepancy shows up through the built-in collections, for instance in
the cardinality of a set of extern objects.

For an extern `class` or `trait`, implement it as identity:

```go
func (_this *Box) Equals(other *Box) bool {
	return _this == other
}

func (_this *Box) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*Box)
	return ok && _this.Equals(other)
}
```

`MutableMap`, `AtomicBox` and `Lock` in the `Std_Concurrent` externs of the Dafny
standard libraries are written exactly this way.

Implementing `EqualsGeneric` structurally on a `class` or `trait` is worse than
leaving it out, because it makes the two comparison paths disagree: `a != b`
evaluates to `true` while `{a, b}` has one element, so a verified assertion
`|{a, b}| == 2` fails at run time even though the program never compares the two
objects directly. Structural equality is sound only for a type whose equality the
verifier leaves uninterpreted, such as an opaque `type {:extern} T(==)`. A type
whose equality should be structural is otherwise better modelled as a Dafny
`datatype`. See also the equality discussion in
[Dafny compilation to Go](../Compilation/Go).
