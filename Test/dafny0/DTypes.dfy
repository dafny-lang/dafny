class C {
  var n: set<Node>;

  method M(v: Stack)
    requires v != null;
  {
    var o: object := v;
    assert o !in n;  // should be known from the types involved
  }

  method N(v: Stack)
    /* this time without the precondition */
  {
    var o: object := v;
    assert o !in n;  // error: v may be null
  }

  method A0(a: CP<int,C>, b: CP<int,object>)
  {
    var x: object := a;
    var y: object := b;
    assert x == y ==> x == null;
  }

  method A1(a: CP<int,C>)
  {
    var x: object := a;
    assert (forall b: CP<int,Stack> :: x == b ==> b == null);  // error (we don't add a type antecedent to
                                                               // quantifiers; is that what we want?)
  }

  var a2x: set<CP<C,Node>>;
  method A2(b: set<CP<Node,C>>)
    requires null !in b;
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y == {};
  }

  method A3(b: set<CP<Node,C>>)
    /* this time without the precondition */
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y <= {null};
  }

  method A4(b: set<CP<Node,C>>)
    /* again, without the precondition */
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y == {};  // error
  }

  method A5()
  {
    var a := new CP<int,C>;
    var b := new CP<int,object>;
    while (a != null)
      decreases *;  // omit loop termination check (in fact, the loop does not terminate)
    {
      var x: object := a;
      var y: object := b;
      assert x == y ==> x == null;
      a := a;  // make 'a' a loop target
    }
  }
}

class Stack { }
class Node { }

class CP<T,U> {
}
