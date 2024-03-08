/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
A collection of predicates that establish whether commonly known properties on functions, 
such as injectivity and commutativity, hold.
These properties can only be applied to functions on value types.
*/
module Std.Functions {

  ghost predicate Injective<X(!new), Y>(f: X --> Y)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
  }

  ghost predicate Commutative<T(!new), U(!new)>(f: (T,T) -> U)
    reads f.reads
    requires forall x,y :: f.requires(x,y) && f.requires(y,x)
  {
    forall x,y :: f(x,y) == f(y,x)
  }

  ghost predicate Associative<T(!new)>(f: (T,T) -> T)
    reads f.reads
    requires forall x, y, z :: f.requires(x,y) && f.requires(y,z) && f.requires(x,z)
  {
    forall x, y, z: T :: f(x,f(y,z)) == f(f(x,y),z)
  }
}