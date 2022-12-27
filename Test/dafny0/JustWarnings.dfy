// RUN: %baredafny verify %args --warn-shadowing "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests the behavior where the Resolver reports some warnings
// but no errors.  In the case of errors, resolution does not continue
// to clone modules and resolve them, but the cloning does proceed if there
// are only warnings.  Dafny should report only one copy of these warnings,
// and warnings are therefore turned off when processing the clones.  This
// test file makes sure the warnings don't appear twice.

method M(x: int)
{
  var x := 10;  // warning: this shadows the parameter 'x'
}

class C<T> {
  var u: T
  method P<T>(t: T)  // warning: this shadows the type parameter 'T'
  constructor (t: T) {
    u := t;
  }
}
