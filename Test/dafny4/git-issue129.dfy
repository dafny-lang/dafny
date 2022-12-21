// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method Foo(): (int, int)
{
    (1, 2)
}

method Bar()
    ensures var (x, y) := Foo(); x < y
{
    var (x, y) := Foo();
}

datatype Point = Point(x: int, y: int)

function method FooPoint(): Point
{
    Point(1, 2)
}

method BarPoint()
    ensures var Point(x, y) := FooPoint(); x < y
{
    var Point(x, y) := FooPoint();
}

datatype Option<A> = Some(val: A) | None

method UseOption()
{
    var x := Some(3);
    var Some(n) := x;
    x := None;
    var Some(m) := x;  // error: RHS is not certain to look like the pattern 'Some'
}
