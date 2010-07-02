// Concrete language syntax for a Dafny extension with refinement. 
// 6/28/2010

class A { 
  var n : int;
    
  method Init() modifies this; 
  { n := 0;}

  method Inc() modifies this; 
  { n := n + 1;}

  method Dec() 
    modifies this;
    requires n > 0; 
  { n := n - 1;}  
  
  method Test1(p: int) returns (i: int) 
  {   
    assume true;
  }

  method Test2() returns (o: object)
  { o := this; }
}

class B refines A {
  var inc : int, dec : int;
    
  replaces n by n == inc - dec;
  // transforms n into inc - dec;
    
  refines Init() modifies this;
  { inc := 0; dec := 0;}
    
  refines Inc() modifies this;
  { inc := inc + 1; }  
  
  refines Dec() 
    modifies this;
    requires inc > dec; 
  { dec := dec + 1; }

  refines Test1(p: int) returns (i: int) 
  {
    i := p;
  }
}

    
    
