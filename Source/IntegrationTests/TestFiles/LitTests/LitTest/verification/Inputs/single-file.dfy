method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
  assert false by {
    assert false;
    assert false;
  }
}

method Loop() {
  var b := true;
  while(b) 
    invariant false 
  {
    b := false;
  }
  assert false;
}