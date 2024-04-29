// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=full

// The following tests apply only --general-traits=full, since that mode allows a newtype to both
// be based on `real` and extend traits.
// Alternatively, if newtypes could have a datatype as the base type, then these tests could be
// changed (or appended) to use --general-traits=datatype and use a datatype as the newtype base type.

module TwoLevelsOfNewtype {
  module DuplicateInR0 {
    newtype R0 = real { const Floor: string } // error: duplicate member
    newtype R1 = R0
  }
  module DuplicateInR1 {
    newtype R0 = real
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
  module DuplicateInR0AndR1 {
    newtype R0 = real { const Floor: string } // error: duplicate member
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
}

module DuplicateFromBaseTypeAndParentType {
  module DuplicateInheritance {
    trait Parent { const Floor: string }
    newtype R0 extends Parent = real // error: duplicate inherited member
    newtype R1 = R0
  }
  module DuplicateInR0 {
    trait Parent { const Floor: string }
    newtype R0 extends Parent = real { // error: duplicate inherited member
      const Floor: string // error: duplicate member
    }
    newtype R1 = R0
  }
  module DuplicateInR1 {
    trait Parent { const Floor: string }
    newtype R0 extends Parent = real // error: duplicate inherited member
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
  module DuplicateInR0AndR1 {
    trait Parent { const Floor: string }
    newtype R0 extends Parent = real { // error: duplicate inherited member
      const Floor: string // error: duplicate member
    }
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
}

module DuplicateFromBaseTypeAndGrandParentType {
  module DuplicateInheritance {
    trait GrandParent { const Floor: string }
    trait Parent extends GrandParent { }
    newtype R0 extends Parent = real // error: duplicate inherited member
    newtype R1 = R0
  }
  module DuplicateInR0 {
    trait GrandParent { const Floor: string }
    trait Parent extends GrandParent { }
    newtype R0 extends Parent = real { // error: duplicate inherited member
      const Floor: string // error: duplicate member
    }
    newtype R1 = R0
  }
  module DuplicateInR1 {
    trait GrandParent { const Floor: string }
    trait Parent extends GrandParent { }
    newtype R0 extends Parent = real // error: duplicate inherited member
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
  module DuplicateInR0AndR1 {
    trait GrandParent { const Floor: string }
    trait Parent extends GrandParent { }
    newtype R0 extends Parent = real { // error: duplicate inherited member
      const Floor: string // error: duplicate member
    }
    newtype R1 = R0 { const Floor: string } // error: duplicate member
  }
}
