// RUN: echo 'lit should ignore this file' 

method VerifyMe() {
  assert false; // It should display this as not verified.
}