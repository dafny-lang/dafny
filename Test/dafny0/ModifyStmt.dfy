// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  var x: int;
  var y: int;
  ghost var g: int;

  method M(S: set<MyClass>, mc: MyClass)
    requires this == mc;
    modifies this, S;
  {
    if mc == this {
      modify mc, this;
    }
    modify {this}, this, {this}, S;
    modify this;
    modify {:myAttribute} {:another true} {this}, this, S;
    modify {} ;
  }

  method N()
    modifies this;
  {
    x := 18;
    modify this;
    assert x == 18;  // error: cannot conclude this here
  }

  method P(other: MyClass?)
    modifies this;
  {
    x := 18;
    var previous := if other == null then 0 else other.x;
    modify this;
    assert other != null && other != this ==> other.x == previous;
  }

  method FieldSpecific0()
    modifies `x;
  {
    modify this;  // error: this is a larger frame than what FieldSpecific0 is allowed to modify
  }

  method FieldSpecific1()
    modifies `x, `y;
  {
    modify this;  // error: this is a larger frame than what FieldSpecific0 is allowed to modify
  }

  method FieldSpecific2()
    modifies this;
  {
    modify `x;
  }

  method FieldSpecific3()
    modifies `x;
  {
    modify this`x;
    modify `y;  // error: this is a larger frame than what FieldSpecific3 is allowed to modify
  }

  method FieldSpecific4()
    modifies `x;
  {
    var xx, yy := x, y;
    modify this`x;
    assert y == yy;  // fine
    assert x == xx;  // error: x just changed
  }

  method GhostFrame4()
    modifies this;
  {
    var xx := x;
    ghost var gg := g;
    if g < 100 {
      // we're now in a ghost context
      var n := 0;
      while n < y
        modifies this;
      {
        g := g + 1;
        n := n + 1;
      }
    }
    assert x == xx;  // fine, since only ghost state is allowed to be modified inside the ghost if
    assert g == gg;  // error
  }

  ghost method Ghost0()
    modifies this;
  {
    var xx := x;
    var gg := g;
    modify this;  // since we're in the context of a ghost method, this will only modify ghost fields
    assert x == xx;  // fine
    assert g == gg;  // error
  }

  ghost method Ghost1()
    modifies this;
  {
    var xx := x;
    var gg := g;
    modify `g;  // since we're in the context of a ghost method, this will only modify
                // ghost fields, despite the specific mention of non-ghost fields
    assert x == xx;  // fine
    assert g == gg;  // error
  }

  method Ghost2()
    modifies this;
  {
    var xx := x;
    ghost var gg := g;
    if g < 100 {
      // the if guard mentions a ghost field, so we're now in a ghost context
      modify this;
      assert x == xx;  // fine, since the 'modify' statement only modified ghost fields
      assert g == gg;  // error: the 'modify' statement can affect the ghost field 'g'
    }
  }
}

class ModifyBody {
  var x: int;
  var y: int;
  method M0()
    modifies this;
  {
    modify {} {
      x := 3;  // error: violates modifies clause of the modify statement
    }
  }
  method M1()
    modifies this;
  {
    modify {} {
      var o := new ModifyBody;
      o.x := 3;  // fine
    }
  }
  method M2()
    modifies this;
  {
    modify this {
      x := 3;
    }
  }
  method M3(o: ModifyBody, p: ModifyBody)
    modifies this, o, p;
  {
    modify {this, o, p} {
      modify this, o;
      modify o, this {
        modify o {
          modify o;
          modify {} {
            modify {};
          }
        }
      }
    }
  }
  method P0()
    modifies this;
  {
   var xx := x;
    modify this;
    assert xx == x;  // error
  }
  method P1()
    modifies this;
  {
   var xx := x;
    modify this {
      y := 3;
    }
    assert xx == x;  // fine, because the modify body trumps the modify frame
  }
}
