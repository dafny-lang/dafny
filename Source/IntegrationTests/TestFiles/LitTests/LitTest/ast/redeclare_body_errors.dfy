// RUN: ! %verify %s > %t
// RUN: %diff "%s.expect" "%t"
 
trait T {
  method foo() returns (r: int)  
    ensures r >= 3
  {
    return 3;
  }
}

trait Bad extends T {
  method foo() returns (r: int)  
    ensures r >= 1
  {
    return 4;
  }
}

class Better extends Bad {
  method foo() returns (r: int)  
    ensures r >= 2
  {
    return 4;
  }
}