// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int


  predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&  // not needed, but speeds up verification

    (right != null ==> right in desc && left !in right.desc) &&

    (left != null ==>
      left in desc &&
      (right != null ==> desc == {left,right} + left.desc + right.desc)  &&
      (right == null ==> desc == {left} + left.desc)  &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==> desc == {right} + right.desc)  &&
      (right == null ==> desc == {})) &&

    (right != null ==> right.validDown()) &&

    (blocked() ==> forall m :: m in desc ==> m.blocked()) &&
    (after() ==> forall m :: m in desc ==> m.blocked() || m.after())
//    (left != null && right != null ==> left.desc !! right.desc)  // not needed
  }




  predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
  { validUp() && validDown() && desc !! anc }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }


  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    decreases *  // allow the method to not terminate
  {
//A
    pc := 1;
    if(left != null) {
      while(!left.sense)
        modifies left
        invariant validDown() // this seems necessary to get the necessary unfolding of functions
        invariant valid()
        decreases *  // to by-pass termination checking for this loop
      {
        // this loop body is supposed to model what the "left" thread
        // might do to its node. This body models a transition from
        // "before" to "blocked" by setting sense to true. A transition
        // all the way to "after" is not permitted; this would require
        // a change of pc.
        // We assume that "left" preserves the validity of its subtree,
        // which means in particular that it goes to "blocked" only if
        // all its descendants are already blocked.
        left.sense := *;
        assume left.blocked() ==> forall m :: m in left.desc ==> m.blocked();
      }
    }
    if(right != null) {
      while(!right.sense)
        modifies right
        invariant validDown() // this seems necessary to get the necessary unfolding of functions
        invariant valid()
        decreases *  // to by-pass termination checking for this loop
      {
        // analogous to the previous loop
        right.sense := *;
        assume right.blocked() ==> forall m :: m in right.desc ==> m.blocked();
      }
    }

//B
    pc := 2;
    if(parent != null) {
      sense := true;
    }
//C
    pc := 3;
    while(sense)
        modifies this
        invariant validUp() // this seems necessary to get the necessary unfolding of functions
        invariant valid()
        invariant left == old(left)
        invariant right == old(right)
        invariant sense ==> parent != null
        decreases *  // to by-pass termination checking for this loop
    {
      // this loop body is supposed to model what the "parent" thread
      // might do to its node. The body models a transition from
      // "blocked" to "after" by setting sense to false.
      // We assume that "parent" initiates this transition only
      // after it went to state "after" itself.
      sense := *;
      assume !sense ==> parent.after();
    }
//D
    pc := 4;
    if(left != null) {
      left.sense := false;
    }
//E
    pc := 5;
    if(right != null) {
      right.sense := false;
    }
//F
    pc := 6;
  }
}
