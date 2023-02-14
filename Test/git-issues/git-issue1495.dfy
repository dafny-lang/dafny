// RUN: %dafny /compile:0 rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../libraries/src/Wrappers.dfy"
import opened Wrappers

datatype Bar = Bar(i: string)
function ParseBar(s: string): Result<Bar, string> {
   Success(Bar(s))
}

class Foo {
  const bar: Bar

  constructor (barLike: string)
    requires ParseBar(barLike).Success?
  {
     // Before (this) was assigned to a temporary variable.
     (this).bar :- assert ParseBar(barLike);
  }
}

// The fix for above should not remove the temporary variable.
// The following test should still pass.
class Wrapper {
  var arg: string
  constructor() {
    arg := "default";
  }
}

class Foo2 {
  var leftWrapper: Wrapper
  var rightWrapper: Wrapper
  var currentWrapper: Wrapper
  var isCurrentWrapperLeft: bool
  ghost var Repr: set<object>

  constructor ()
    ensures Valid() && fresh(Repr - {this}) && isCurrentWrapperLeft
  {
    leftWrapper := new Wrapper();
    rightWrapper := new Wrapper();
    currentWrapper := leftWrapper;
    isCurrentWrapperLeft := true;
    Repr := {this, leftWrapper, rightWrapper};
  }

  ghost predicate Valid()
    reads this
  {
    (if isCurrentWrapperLeft then
      currentWrapper == leftWrapper
    else currentWrapper == rightWrapper) &&
    Repr == {this, leftWrapper, rightWrapper}
  }

  method getNextValue() returns (s: Result<string, string>) 
    requires Valid()
    ensures Valid()
    ensures if old(isCurrentWrapperLeft) then currentWrapper == rightWrapper else currentWrapper == leftWrapper
    ensures isCurrentWrapperLeft == !old(isCurrentWrapperLeft)
    ensures if old(isCurrentWrapperLeft) then s == Success("left") else s == Failure("no next value")
    ensures old(leftWrapper) == leftWrapper
    ensures old(rightWrapper) == rightWrapper
    modifies this
  {
    if(isCurrentWrapperLeft) {
      currentWrapper := rightWrapper;
      isCurrentWrapperLeft := false;
      s := Success("left");
    } else {
      currentWrapper := leftWrapper;
      isCurrentWrapperLeft := true;
      s := Failure("no next value");
    }
  }

  method update() returns (r: Result<string, string>)
    requires Valid()
    ensures Valid()
    ensures old(isCurrentWrapperLeft) ==> r == Success("Assigned everything")
    ensures old(isCurrentWrapperLeft) ==> leftWrapper.arg == "left"
    ensures old(isCurrentWrapperLeft) ==> currentWrapper == rightWrapper
    modifies Repr
  {
    currentWrapper.arg :- getNextValue();
    // currentWrapper becomes rightWrapper after getNextValue, but leftWrapper.arg receives the new value
    r := Success("Assigned everything");
  }
}

method Main()
{
  var foo2: Foo2 := new Foo2();
  var updated: Result<string, string> := foo2.update();
  assert updated == Success("Assigned everything");
  assert foo2.leftWrapper.arg == "left";
}
