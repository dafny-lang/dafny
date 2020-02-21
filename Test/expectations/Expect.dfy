

class OOAgent {
  function method Talk(): bool {
    true
  }
  function method Die(): bool {
    false
  }
}

method TestExpect() {
  var jamesBond := new OOAgent();
  // Do you...
  expect jamesBond.Talk();
  // No Mr. Bond, I...
  expect jamesBond.Die(); // Error: expectation violation
}

method Main() {
  TestExpect();
}
