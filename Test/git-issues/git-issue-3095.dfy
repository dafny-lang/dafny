// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(inputs...) {
  BigPreComputations(); // [1]
  match X {
  case 1 => assume false; // Proof already done, "commented out" by assume false;
  case 2 => // code in focus
  case 3 => assume false; // Proof to do...
  ...
  case n=> assume false; ...
 
  }
}