datatype D = A | B | ghost C
method m(d: D) returns (r: bool) {
  r := match d {
   case A =>true 
   case B =>true 
   case C =>true 
  };
}
