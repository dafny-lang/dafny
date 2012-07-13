
ghost module R1 {
  var f: int;
  method m(y: set<int>) returns (r: int)
  {
    var t := y;
  }
}

ghost module R2 refines R1 {
  var g: nat;
  method m ...
  {
    ...;
    var x := 3;
    t := {1}; // bad: previous local
    r := 3; // bad: out parameter
    f := 4; // bad: previous field
    x := 6; // fine: new local
    g := 34;// fine: new field
  }
}
