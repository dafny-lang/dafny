// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  ClientA.Test();
  ClientB.Test();
  ClientC.Test();
  ClientD.Test();
  ClientE.Test();
  ClientF.Test();
  ClientG.Test();
  Kevin.Test();
}

module Library {
  export reveals Max
  export X reveals More
  export Y reveals Less
  export Z extends Library, X
  compiled function Max(x: int, y: int): int {
    if x < y then y else x
  }
  compiled function More(x: int): int { x + 2 }
  compiled function Less(x: int): int { x - 2 }
}

module ClientA {
  import Library
  module Inner {
    import Library
    compiled function Five(): int {
      Library.Max(2, 5)
    }
  }
  method Test() {
    print "ClientA.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientB {
  import Library
  module Inner {
    import L = Library
    compiled function Five(): int {
      L.Max(2, 5)
    }
  }
  method Test() {
    print "ClientB.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientC {
  import L = Library
  module Inner {
    import K = Library
    compiled function Five(): int {
      K.Max(2, 5)
    }
  }
  method Test() {
    print "ClientC.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientD {
  import L = Library`X
  module Inner {
    import K = Library`Y
    compiled function Five(): int {
      K.Less(7)
    }
  }
  method Test() {
    print "ClientD.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientE {
  import L = Library`Z
  module Inner {
    import K = Library
    compiled function Five(): int {
      K.Max(2, 5)
    }
  }
  method Test() {
    print "ClientE.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientF {
  import opened L = Library`Z
  module Inner {
    import K = Library
    compiled function Five(): int {
      K.Max(2, 5)
    }
  }
  method Test() {
    print "ClientF.Inner.Five: ", Inner.Five(), "\n";
  }
}

module ClientG {
  import Library
  module Inner {
    import opened K = Library
    compiled function Five(): int {
      Max(2, 5)
    }
  }
  method Test() {
    print "ClientG.Inner.Five: ", Inner.Five(), "\n";
  }
}

module Kevin {
  module Joe {
    module Nick {
      import Frankie
      compiled function g(): int {
        Frankie.x
      }
    }
  }
  method Test() {
    print "Frankie: ", Joe.Nick.g(), "\n";
  }
}

module Frankie {
  const x := 3
}
