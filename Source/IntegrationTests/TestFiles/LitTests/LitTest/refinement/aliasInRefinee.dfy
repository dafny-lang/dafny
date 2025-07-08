// RUN: %baredafny resolve --use-basename-for-filename %s

module Aliased {
  module Nested {
    const x := 3
    const y := 4
  }
}

module Refinee {
  import opened Aliased.Nested
}

module Refiner refines Refinee {
  const z := y + 1 
  const x := "blocking"
}

module SecondNestedOpener {
  import opened Aliased.Nested
}

module Outer {
  import opened SecondNestedOpener
  import opened Refiner
}