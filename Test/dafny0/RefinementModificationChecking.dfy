
ghost module R1 {
  var f: int;
  method m(y: set<int>) returns (r: int)
    modifies this;
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
    t := {1}; // error: previous local
    r := 3; // error: out parameter
    f := 4; // fine: all fields, will cause re-verification
    x := 6; // fine: new local
    g := 34;// fine: new field
  }
}
