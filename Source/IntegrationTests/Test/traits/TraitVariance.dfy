// RUN: %exits-with 2 %dafny /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NoVariance {
  trait Trait<Y> { }

  type AbstractType extends Trait<int> { }

  datatype Datatype extends Trait<int> = Value

  newtype Newtype extends Trait<int> = real

  class Class extends Trait<int> { }
}

module NonVariantTypeParameter {
  trait Trait<Y> { }

  type AbstractType<X, +Z> extends Trait<X> { }

  datatype Datatype<X, +Z> extends Trait<X> = Value

  // At this time, the parser does not allow newtype to have type parameters. This will change in the future.
  // newtype Newtype<X, +Z> extends Trait<X> = real
}

module VariantTypeParameter {
  trait Trait<Y> { }

  type AbstractType<+X, Z> extends Trait<X> { } // error: X not used according to its specification

  datatype Datatype<+X, Z> extends Trait<X> = Value // error: X not used according to its specification

  // At this time, the parser does not allow newtype to have type parameters. This will change in the future.
  // newtype Newtype<+X, Z> extends Trait<X> = real // error: X not used according to its specification
}
