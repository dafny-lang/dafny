
module V {
  module t = T;  // error: T is not visible (and isn't even a module)
}

module A {
  module B = C;
}

module C {
  module D = A;
}