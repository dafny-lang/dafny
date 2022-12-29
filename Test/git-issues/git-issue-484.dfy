// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype MyInt = int

datatype Bar = Bar(b: MyInt)

function update0(bar: Bar, i: int): Bar {
  // Regression test: the following once suppressed the error:
  bar.(b := i) // error: int not assignable to MyInt
}

function update1(bar: Bar, i: int): Bar {
  bar.(b := i as MyInt)
}

function update2(bar: Bar, i: real): Bar {
  // Regression test: the following once caused a crash:
  bar.(b := i) // error: real is not assignable to MyInt
}

function update3(bar: Bar, i: int): Bar {
  Bar(i) // error: int is not assignable to MyInt
}

newtype byte = b:int | 0 <= b < 0x100

datatype Foo = Foo(b: byte)

function update10(foo: Foo, i: int): Foo
  requires 0 <= i < 0x100
{
  // Regression test: the following once suppressed the error:
  foo.(b := i) // error: int is not assignable to byte
}

function update11(foo: Foo, i: int) : Foo
  requires 0 <= i < 0x100
{
  Foo(i) // error: int is not assignable to byte
}

function update12(foo: Foo, i: int): Foo
  requires 0 <= i < 0x100
{
  foo.(b := i as byte)
}

function update13(foo: Foo, i: int) : Foo
  requires 0 <= i < 0x100
{
  Foo(i as byte)
}
