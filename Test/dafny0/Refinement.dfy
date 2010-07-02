// Concrete language syntax for a Dafny extension with refinement. 
// Counter example.
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

// Carrol Morgan's calculator
// 7/2/2010 Kuat

class ACalc {
  var vals: seq<int>;
  
  method reset() 
    modifies this;
  {
    vals := [];
  }
  
  method add(x: int) 
    modifies this;
  {
    vals := [x] + vals;
  }
  
  method mean() returns (m: int)     
    requires |vals| > 0;
  {
    m := seqsum(vals)/|vals|;
  }

  static function method seqsum(x:seq<int>) : int
    decreases x;
  {
    if (x == []) then 0 else x[0] + seqsum(x[1..])
  }
}


class CCalc refines ACalc {
  var sum: int;
  var num: int;
  replaces vals by sum == seqsum2(vals) && num == |vals|;

  refines reset() 
    modifies this;
  {
    sum := 0;
    num := 0;
  }

  refines add(x: int)
    modifies this;
  {
    sum := sum + x;
    num := num + 1;
  }

  refines mean() returns (m: int)
    requires num > 0;
  {
    m := sum/num;
  }

  static function method seqsum2(x:seq<int>) : int
    decreases x;
  {
    if (x == []) then 0 else x[0] + seqsum2(x[1..])
  }
}







    
    
