
module V {
  import t = T;  // error: T is not visible (and isn't even a module)
}

module A {
  import B = C;
}

module C {
  import D = A;
}