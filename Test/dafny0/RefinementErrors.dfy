class A refines C {
}

class B refines A {
}

class C refines B {
}


class D {
  refines M()
  {
  }
}

class E {
  var x: int;
  
  method M() 
  {
    x := 0;
  }
}

class F {  
  replaces M by x == y;
}

class G refines E {
  var y: int;
  replaces x by x == y;
  
  refines M() returns (i: int)
  {
  }
}

class H refines E {
  var x: int;

  method M() 
  {
  }
}

class J refines E {
  var y: int;
  replaces x by x == y;

  refines M()
  {
    y := 1;
  }
}


