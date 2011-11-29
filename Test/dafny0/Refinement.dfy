// Concrete language syntax for a Dafny extension with refinement. 
// IntegerCounter example.
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
    i := p;
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

class Util {
  static function method seqsum(x:seq<int>) : int
    decreases x;
  {
    if (x == []) then 0 else x[0] + seqsum(x[1..])
  }
}


class ACalc {
  var util: Util;
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
    m := util.seqsum(vals)/|vals|;
  }
}



class CCalc refines ACalc {
  var util2: Util;
  var sum: int;
  var num: int;
  replaces vals by sum == util2.seqsum(vals) && num == |vals|;

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
}

// Sequence refined to a singly linked list
// 6/22/2010: Kuat Yessenov

class List<T> {
  var rep: seq<T>;
  method Clear() 
    modifies this;
  {
    rep := [];
  }
  
  method Append(x: T) 
    modifies this; 
  {
    rep := rep + [x];
  }
  
  method Prepend(x: T) 
    modifies this; 
  {
    rep := [x] + rep;
  }
  
  method Insert(i: int, x: T) 
    requires 0 <= i && i < |rep|;
    modifies this;
  {
    rep := rep[i:=x];
  }
}

class Node<T> {
  var data: T;
  var next: Node<T>;
}   

class LinkedList refines List {
  var first: Node<T>;
  ghost var nodes: set<Node<T>>;
    
  function Abstraction(n: Node<T>, nodes: set<Node<T>>, rep: seq<T>) : bool
  decreases nodes;
  reads n, nodes;
  {
    if (n == null) then 
            rep == [] &&
            nodes == {}
        else 
            |rep| >= 1 &&
            n.data == rep[0] &&
            n in nodes &&
            n.next in nodes + {null} &&
            Abstraction(n.next, nodes - {n}, rep[1..])
  }

  replaces rep by Abstraction(first, nodes, rep);     

  refines Clear() 
    modifies this;
  {
    first := null;
    nodes := {};
  }

  refines Prepend(x: T) 
    modifies this;
  {
    var n := new Node<T>;
    n.data := x;
    n.next := first;
    first := n;
    nodes := {n} + nodes;
    assert nodes - {n} == old(nodes); //set extensionality
  }
} 







    
    
