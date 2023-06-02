// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype ABC = ABC(nameonly a: int, nameonly b: int, nameonly c: int)

function JustChangeB(abc: ABC): ABC {
  // The following line once gave an error, complaining 'a' wasn't specified by name. That's been fixed.
  abc.(b := 42)
}

function ChangeEvathang(abc: ABC): ABC {
  // The following line once gave an error, complaining 'a' wasn't specified by name. That's been fixed.
  abc.(b := 42, a := 100, c := 90)
}

datatype XYZ = XYZ(x: int, nameonly y: int := 5, z: int := 7)

function MakeSureDefaultValuesAreNotUsedInUpdate(xyz: XYZ): XYZ {
  xyz.(x := 3)
}

method Main() {
  var abc := ABC(a := 19, c := 23, b := 21);
  assert abc.b == 21;
  print abc, "\n"; // 19 21 23

  abc := JustChangeB(abc);
  assert abc.b == 42 && abc.c == 23;
  print abc, "\n"; // 19 42 23

  abc := ChangeEvathang(abc);
  assert abc.b == 42 && abc.c == 90;
  print abc, "\n"; // 100 42 90

  var xyz := XYZ(0);
  assert xyz.y == 5;
  print xyz, "\n"; // 0 5 7

  xyz := XYZ(88, y := 89, z := 90);
  assert xyz.y == 89;
  print xyz, "\n"; // 88 89 90

  xyz := MakeSureDefaultValuesAreNotUsedInUpdate(xyz);
  assert xyz.y == 89;
  print xyz, "\n"; // 3 89 90
}
