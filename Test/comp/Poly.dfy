// Currently only enabled for Go due to seq<TRAIT> etc.
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Shape {
    function method Center(): (real, real) reads this
    method PrintCenter() {
        print "Center: ", this.Center(), "\n";
    }
}

class Square extends Shape {
    var x1: real, y1: real, x2: real, y2: real
    constructor(x1: real, y1: real, x2: real, y2: real) {
        this.x1 := x1;
        this.y1 := y1;
        this.x2 := x2;
        this.y2 := y2;
    }
    function method Center(): (real, real) reads this {
        var x := (this.x1 + this.x2) / 2.0;
        var y := (this.y1 + this.y2) / 2.0;
        (x, y)
    }
}

class Circle extends Shape {
    var x: real, y: real, r: real
    constructor(x: real, y: real, r: real) {
        this.x := x;
        this.y := y;
        this.r := r;
    }
    function method Center(): (real, real) reads this {
        (this.x, this.y)
    }
}

method PrintArray(shapes: array<Shape?>) {
    var i : int := 0;
    while i < shapes.Length
        invariant 0 <= i <= shapes.Length
        decreases shapes.Length - i
    {
        if shapes[i] != null {
            shapes[i].PrintCenter();
        }
        i := i + 1;
    }
}

method PrintSeq(shapes: seq<Shape>) {
    var i : int := 0;
    while i < |shapes|
        invariant 0 <= i <= |shapes|
        decreases |shapes| - i
    {
        shapes[i].PrintCenter();
        i := i + 1;
    }
}

method PrintSet(shapes: set<Shape>) {
    print "Centers: ", (set x | x in shapes :: x.Center()), "\n";
}

method PrintMultiSet(shapes: multiset<Shape>) {
    print "Centers: ", (set x | x in shapes :: x.Center()), "\n";
}

method Main() {
    var square := new Square(0.0, 1.0, 1.0, 0.0);
    print "Center of square: ", square.Center(), "\n";

    var circle := new Circle(1.0, 1.0, 4.0);
    print "Center of circle: ", circle.Center(), "\n";

    var shapes : array<Shape?> := new Shape?[2];
    shapes[0] := square;
    shapes[1] := circle;
    PrintArray(shapes);

    PrintSeq([square, circle]);
    PrintSet({square, circle});
    PrintMultiSet(multiset{square, circle});
}
