// RUN: %dafny /compile:4 /compileTarget:cs "%s" %S/ExternCopyFromTraitLibrary.cs > "%t"
// RUN: %diff "%s.expect" "%t"

/// This file tests inheritance of `:extern` annotation in traits.

/// First, we check that `:extern` is correctly inherited by child classes, and
/// can be overriden:

module {:extern "M"} M {
  trait {:extern} T1 {
    method {:extern "m1_ext"} m1()
  }
  class {:extern} C1 extends T1 {
    method {:extern "m1_ext_different"} m1() {
      print "";
    }
  }

  trait {:extern} T2 {
    method {:extern "m2_ext"} m2()
  }
  class {:extern} C2 extends T2 {
    method m2() {}
  }
}

/// Second, we check that Dafny does not complain about missing implementations
/// for `:extern` trait methods.  If `:extern` were completely separate from
/// `:compile false`, this would be best handled by `:compile false`.  But for
/// now `:extern "foo"` on a class method `M` means not just "expose `M` under
/// the name `foo`", but also "and do not compile it".  Hence, we use `:extern`
/// in the implementation check below.
///
/// The rationale for this is that Dafny does not have inheritance, but we might
/// still want to model external C#-style inheritance.  To do so we declare a
/// trait corresponding to a C# interface, list all of its methods, and annotate
/// non-abstract ones as using `:extern`.  This lets Dafny know that it
/// shouldn't insist on such methods being re-implemented in derived classes.
///
/// Note that the above mentions "interfaces" when talking about C#.  That is
/// because the feature below is not flexible enough to accommodate abstract
/// classes, as it does not add the `override` keyword on implementations.
/// Hence, the only use of this feature in C# is interfaces with explicit
/// implementations. The same problem means that this feature is not very
/// useful for Java either: Dafny translates the `extends` keywords to Java's
/// `implements`, not `extends`, and so `Asker` below must be an interface in
/// Java.

module {:extern "M1"} M1 {
  trait {:extern "Asker"} {:compile false} Asker {
    method Exclaim() // An abstract method, to be overridden
    method {:extern} Speak() // A method implemented by the trait
  }

  trait DoubleAsker extends Asker {
    method SpeakTwice() {
      Speak();
      Speak();
    }
  }

  class AC0 extends Asker {
    // No complaint about `Speak` being unimplemented thanks to `:extern`.

    method Exclaim() {
      print "  An argument!\n";
    }
  }

  class AC1 extends DoubleAsker {
    // No complaint about `Speak` being declared without a body thanks to `:extern`.
    method Speak()

    method Exclaim() {
      print "  Another argument!\n";
    }
  }

  method Main() {
    var ac0: Asker := new AC0;
    ac0.Speak();
    var ac1: DoubleAsker := new AC1;
    ac1.Speak();
    ac1.SpeakTwice();
  }
}
