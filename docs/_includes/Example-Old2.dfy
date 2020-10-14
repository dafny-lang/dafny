class A {
  var value: int
  constructor () 
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a 
   {
     label L:
     a.value := 12;
     label M:
     a := new A(); // Line X
     label N:
     a.value := 20;
     label P:

     assert old(a.value) == 11;
     assert old(a).value == 12; // this.a is from pre-state, 
                                // but .value in current state
     assert old@L(a.value) == 11;
     assert old@L(a).value == 12; // same as above
     assert old@M(a.value) == 12; // .value in M state is 12
     assert old@M(a).value == 12;
     assert old@N(a.value) == 10; // this.a in N is the heap
                                  // reference at Line X
     assert old@N(a).value == 20; // .value in current state is 20
     assert old@P(a.value) == 20;
     assert old@P(a).value == 20; 
  }
}
