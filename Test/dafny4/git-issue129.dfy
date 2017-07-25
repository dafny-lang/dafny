// RUN: %dafny /compile:0 "%s" > "%t"
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
