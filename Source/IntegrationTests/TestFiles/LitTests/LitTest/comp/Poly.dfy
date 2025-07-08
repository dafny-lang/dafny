// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4174
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation

trait Shape extends object {
  function Center(): (real, real) reads this
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
  function Center(): (real, real) reads this {
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
  function Center(): (real, real) reads this {
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

lemma ThereIsASmallest(s: set<Shape>) returns (shape: Shape)
  requires s != {}
  ensures shape in s && forall shape' :: shape' in s ==> shape.Center().0 <= shape'.Center().0
{
  shape :| shape in s;
  if shape' :| shape' in s && shape'.Center().0 < shape.Center().0 {
    var s' := s - {shape};
    assert shape' in s';
    shape := ThereIsASmallest(s');
  }
}

method PrintSet(shapes: set<Shape>) {
  var s := shapes;
  var ordered := [];
  while |s| != 0 {
    ghost var _ := ThereIsASmallest(s);
    var shape: Shape :| shape in s && forall shape': Shape :: shape' in s ==> shape.Center().0 <= shape'.Center().0;
    ordered := ordered + [shape];
    s := s - {shape};
  }
  PrintSeq(ordered);
}

lemma ThereIsASmallestInMultiset(s: multiset<Shape>) returns (shape: Shape)
  requires s != multiset{}
  ensures shape in s && forall shape' :: shape' in s ==> shape.Center().0 <= shape'.Center().0
{
  shape :| shape in s;
  if shape' :| shape' in s && shape'.Center().0 < shape.Center().0 {
    var s' := s - multiset{shape};
    assert shape' in s';
    shape := ThereIsASmallestInMultiset(s');
  }
}

method PrintMultiSet(shapes: multiset<Shape>) {
  var s := shapes;
  var ordered := [];
  while |s| != 0 {
    ghost var _ := ThereIsASmallestInMultiset(s);
    var shape: Shape :| shape in s && forall shape': Shape :: shape' in s ==> shape.Center().0 <= shape'.Center().0;
    ordered := ordered + [shape];
    s := s - multiset{shape};
  }
  PrintSeq(ordered);
}

lemma ThereIsASmallestInt(s: set<int>) returns (k: int)
  requires s != {}
  ensures k in s && forall k' :: k' in s ==> k <= k'
{
  k :| k in s;
  if k' :| k' in s && k' < k {
    var s' := s - {k};
    assert s == s' + {k};
    assert k' in s';  // prove s' is nonempty
    k := ThereIsASmallestInt(s');
  }
}

method PrintMap(shapes: map<nat, Shape>) {
  var s := shapes.Keys;
  var ordered := [];
  while |s| != 0
    invariant s <= shapes.Keys
  {
    ghost var _ := ThereIsASmallestInt(s);
    var k :| k in s && forall k' :: k' in s ==> k <= k';
    ordered := ordered + [shapes[k]];
    s := s - {k};
  }
  PrintSeq(ordered);
}

method Main() {
  var square := new Square(0.0, 1.0, 1.0, 0.0);
  print "Center of square: ", square.Center(), "\n";  // (0.5, 0.5)

  var circle := new Circle(1.0, 1.0, 4.0);  // (1.0, 1.0)
  print "Center of circle: ", circle.Center(), "\n";

  var shapes : array<Shape?> := new Shape?[2];
  shapes[0] := square;
  shapes[1] := circle;
  PrintArray(shapes);

  PrintSeq([square, circle]);
  PrintSet({square, circle});
  PrintMultiSet(multiset{square, circle});
  PrintMap(map[0 := square, 1 := circle]);
}
