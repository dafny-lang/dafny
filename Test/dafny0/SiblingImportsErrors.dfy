// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  export reveals Max
  export X reveals More
  export Y reveals Less
  export Z extends Library, X
  function method Max(x: int, y: int): int {
    if x < y then y else x
  }
  function method More(x: int): int { x + 2 }
  function method Less(x: int): int { x - 2 }
}

module ClientA {
  import Library
  module Inner {
    import Library
    function method Five(): int {
      Library.Max(2, 5)
    }
    function method Nope(): int {
      Library.Less(7)  // error: what is Less?
    }
  }
}

module ClientB {
  import Library
  module Inner {
    import L = Library
    function method Five(): int {
      L.Max(2, 5)
    }
    function method Nope(): int {
      Library.Less(7)  // error: what is Library?
    }
  }
}

module ClientC {
  import L = Library
  module Inner {
    import K = Library
    function method Five(): int {
      K.Max(2, 5)
    }
    function method Nope(): int {
      L.Less(7)  // error: what is L?
    }
  }
}

module ClientD {
  import L = Library`X
  module Inner {
    import K = Library`Y
    function method Five(): int {
      K.Less(7)
    }
    function method Nope(): int {
      L.Less(7)  // error: what is Less?
    }
  }
}

module ClientE {
  import L = Library`Z
  module Inner {
    import K = Library
    function method Five(): int {
      K.Max(2, 5)
    }
    function method Nope(): int {
      Library.Max(2, 5)  // error: what is Library?
    }
  }
}

module ClientF {
  import opened L = Library`Z
  module Inner {
    import K = Library
    function method Five(): int {
      K.Max(2, 5)
    }
    function method Nope(): int {
      Max(2, 5)  // error: what is Max?
    }
  }
}

module ClientG {
  import Library
  module Inner {
    import opened K = Library
    function method Five(): int {
      Max(2, 5)
    }
    function method Nope(): int {
      Library.Max(2, 5)  // error: what is Library?
    }
  }
}

module Kevin {
  import Frankie
  module Joe {
    import Frankie
    module Nick {
      function method g(): int {
        Frankie.x  // error: who is Frankie?
      }
    }
  }
}

module Frankie {
  const x := 3
}
