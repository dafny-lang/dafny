// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The LibA and LibB examples are the same, except for the order of declarations.
//

import LibA  // error: duplicate module (note, error is on import, not the module)
module LibA { }

module LibB { }
import LibB  // error: duplicate module (note, error is on import, not the module)

// The following creates an anonymous local name for the opened import LibC
import opened LibC
module LibC { }

// The following creates an anonymous local name for the opened import LibD
module LibD { }
import opened LibD

module Outer {
  import LibW  // error: duplicate module (note, error is on import, not the module)
  module LibW { }

  module LibX { }
  import LibX  // error: duplicate module (note, error is on import, not the module)

  import opened LibY
  module LibY { }

  module LibZ { }
  import opened LibZ
}

module M { }
module M { }  // error: duplicate module name
import M  // error: import name same as a module's name
import M  // error: import name same as a module's name
import M0 = M
import M = M  // error: import name same as a module's name
import M = LibA  // error: import name same as a module's name

import N
import N  // error: duplicate name of import

module AA { }
module BB { }
import opened AA = BB  // error: can only reuse the name AA if RHS of import is AA, too
import opened BB = AA  // error: can only reuse the name BB if RHS of import is BB, too

module X {
  const x := 12
}
module Y {
  module X {
    const x := 10
  }
}
import opened X = Y.X  // error: import name same as a module's name

module S {
  module R { }
}
import opened R = S.R
import opened R = S.R  // error: duplicate name of import
