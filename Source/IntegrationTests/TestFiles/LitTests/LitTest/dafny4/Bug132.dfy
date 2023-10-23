// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var data: int

  ghost predicate P()
    reads this
  { data < 0 }

  ghost predicate Q(e: Cell?)
    reads this, e
  { e != null ==> e.data == data }

  method Test() {
    ghost var b;
    var c := new Cell;
    if {
      // In the current state, everything is allowed:
      case true =>  b := this.P();
      case true =>  b := c.P();
      case true =>  b := this.Q(this);
      case true =>  b := this.Q(c);
      case true =>  b := c.Q(this);
      case true =>  b := c.Q(c);

      // 'this' was allocated already in the 'old' state, so all of these are fine:
      case true =>  b := old(this.P());
      case true =>  b := old(P());  // same as previous line, of course
      case true =>  b := old(this.Q(this));

      // 'c' is freshly allocaed in this method, so it cannot be used inside 'old'
      case true =>  b := old(c.P());  // error: receiver argument must be allocated in the state in which the function is invoked
      case true =>  b := old(c.Q(this));  // error: receiver argument must be allocated in the state in which the function is invoked

      // The same rule should apply if 'c' is a non-receiver argument
      case true =>  b := old(this.Q(c));  // BOGUS: this should also generate an error

      // In the following, 'c' is used as both of the two arguments. It's not allowed as either argument.  However, since the error
      // about the receiver masks the error about the other parameter, only one error (about the receiver) should be reported.
      case true =>  b := old(c.Q(c));  // BOGUS: this should generate an error about the receiver
    }
  }
}

