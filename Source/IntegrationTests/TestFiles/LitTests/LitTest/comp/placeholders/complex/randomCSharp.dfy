
module RandomCSharp replaces Random {
  method GetRandomNat ... {
    var random := new Random();
    return 0;
  }
}

module {:extern "System"} CSharpSystem {
  class {:extern "Random" } Random {
    constructor() { }
  }
}