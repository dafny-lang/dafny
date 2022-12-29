// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The birthday book example from the Z Reference Manual
// Rustan Leino, 22 Feb 2018

// This file contains the BirthdayBook example from the Z Reference
// manual. The comments in the code remark on similarities and
// differences between Z and Dafny.

abstract module Specification {
  // Names and dates are two types. We leave these types as opaque
  // for now.
  // We need to say that names support equality in compiled
  // code. This is done with the `(==)` suffix.
  type Name(==)
  type Date

  // Here are some example names and types
  const John: Name
  const Mike: Name
  const Susan: Name
  const Mar25: Date
  const Dec20: Date

  // We declare a class and mark it with `{:autocontracts}`. This attribute
  // will simplify our task of writing specifications by supplying various
  // method pre- and postconditions. Of interest to us is the following:
  //   * The auto-contracts feature allows us to declare an invariant.  It
  //     expects this invariant to be declared in a predicate called `Valid()`.
  //   * The invariant will be added as postcondition constructors and as
  //     a pre- and postcondition to every method.
  // The auto-contracts feature also performs some other rewrites. These
  // are not important for our example, but they can always be inspected
  // by looking at hover text in the Dafny IDEs.
  class {:autocontracts} BirthdayBook {
    // To allow them to change, we declare `known` and `birthday` as fields.
    // We could declare `birthday` to be a partial function, that is, to
    // have type `Name --> Date`. However, this example will be simpler to
    // do with a finite map in Dafny.
    var known: set<Name>
    var birthday: map<Name, Date>

    predicate Valid() {
      // In Z notation:  known = dom birthday
      known == birthday.Keys
    }

    // In Z, the convention is that inputs have names that end with a question
    // mark. You can do that in Dafny as well. However, this feels to me a little
    // confusing in Dafny, because a question mark at the end of an identifier is
    // sometimes used in different ways (datatype selectors and possibly null
    // reference types).  Moreover, since Dafny methods declare in-parameters
    // explictly, I don't think the need for Z's naming convention is crucial.
    // Therefore, instead of calling the in-parameters `name?` and `date?`, I
    // will simply call them `name` and `date`.
    method AddBirthday(name: Name, date: Date)
      // A precondition for this operation is that the given name is unknown.
      requires name !in known
      // In Z, one writes `\Delta BirthdayBook` to indicate that this operation
      // describes a state change. In Dafny, one instead says that the fields
      // of `this` may be modified. (Actually, the auto-contracts feature will
      // add this `modifies` clause automatically, so we don't need to show it
      // here.)
      modifies this
      // Here is the postcondition. Like in the Z example, we mention explicitly
      // only the change to `birthday`. Since the invariant (that is, the condition
      // given by predicate `Valid()`) is implicit in the postcondition (since
      // we used `{:autocontracts}`, a logical consequence of this specification is
      // that `known` will change correspondingly.
      ensures birthday == old(birthday)[name := date]

    // To make sure the specification of `AddBirthday` really does imply a
    // corresponding change to `known`, we give a proof by writing some code
    // that calls `AddBirthday` and observes, afterwards, that `known` has the
    // expected value.
    method ConsequenceOfAddBirthday(name: Name, date: Date)
      requires name !in known
    {
      AddBirthday(name, date);
      assert known == old(known) + {name};  // that's it, we proved it!

      // Well, if you want to see a longer proof in the proof-calculation style
      // of the proof in the Z Reference Manual, here is one:
      calc {
        known;
      ==  { assert Valid(); }  // invariant after
        birthday.Keys;
      ==  // specification of `AddBirthday`
        (old(birthday)[name := date]).Keys;
      ==  // fact about .Keys
        old(birthday).Keys + (map[name := date]).Keys;
      ==  // fact about .Keys
        old(birthday).Keys + {name};
      == { assert old(Valid()); }  // invariant before
        old(known) + {name};
      }

      // Note: It is common that proofs about programs are confined to "ghost"
      // declarations, that is, declarations for which the compiler will not
      // generate any code. In such a case, it would be natural to declare
      // `ConsequenceOfAddBirthday` as a `lemma`.  However, a lemma is
      // not allowed to change the program state, so it would not be allowed
      // to call method `AddBirthday`.
    }

    // Z's convention is to name outputs with something that ends with an
    // exclamation point. Exclamation points are not allowed in identifiers
    // in Dafny. However, since Dafny methods have to declare their
    // out-parameters, I think it's plenty clear in the following line that
    // `name` is an input and `date` is an output.
    method FindBirthday(name: Name) returns (date: Date)
      // Here is the precondition of the operation:
      requires name in known
      // The Z notation uses `\Xi BirthdayBook` to indicate that this operation
      // does not change the state of the birthday book. In Dafny, this is
      // normally done by just omitting a `modifies` clause. However, we
      // are using `{:autocontracts}` and it, in effect, adds `modifies this`.
      // We could therefore add a postcondition like:
      //     ensures known == old(known) && birthday == old(birthday)
      // but a more concise postcondition is the following:
      ensures unchanged(this)
      // In addition, we want to say that the method sets the out-parameter
      // to the birthday of `name`.
      ensures date == birthday[name]

    // Here is the `Remind` operation, which returns the set of names whose
    // birthday is is today
    method Remind(today: Date) returns (cards: set<Name>)
      ensures unchanged(this)  // again, this is `\Xi BirthdayBook` in Z
      // The following line shows some minor differences in the set-comprehension
      // notation in Z and Dafny. In Z, the "type" of `n` is `known`. But
      // in Dafny, `known` cannot be used as a type. Instead, the type of
      // `n` is (inferred to be) `Name` and `n in known` is a predicate that
      // is included in the range predicate of the set comprehension.
      ensures cards == set n | n in known && birthday[n] == today

    // Here is something we can prove from the postcondition of `Remind`.
    // The Z Reference Manual shows a formula like this, too.
    method ConsequenceOfRemind(today: Date, m: Name)
    {
      var cards := Remind(today);
      assert m in cards <==> m in known && birthday[m] == today;
    }

    // Finally, here is the specification of a constructor that initializes
    // `BirthdayBook` instances.  The Z Reference Manual calls this
    // operation `InitBirthdayBook`, but the last part of this name seems
    // a bit redundant, since the enclosing class is called `BirthdayBook`.
    // Hence, I'll just call it `Init`.
    constructor Init()
      ensures known == {}

    method ConsequenceOfInit()
    {
      var bb := new BirthdayBook.Init();
      assert bb.birthday == map[];
    }
  }
}

module Implementation refines Specification {
  type Name = string
  type Date = int

  const John := "John"
  const Mike := "Mike"
  const Susan := "Susan"
  const Mar25 := 325
  const Dec20 := 1220

  class BirthdayBook ... {
    method AddBirthday...
    {
      known := known + {name};
      birthday := birthday[name := date];
    }

    method FindBirthday(name: Name) returns (date: Date)
    {
      date := birthday[name];
    }

    method Remind(today: Date) returns (cards: set<Name>)
    {
      cards := set n | n in known && birthday[n] == today;
    }

    constructor Init...
    {
      known, birthday := {}, map[];
      Repr := {this};
    }
  }
}

method Main() {
  var bb := new Implementation.BirthdayBook.Init();

  bb.AddBirthday(Implementation.John, Implementation.Mar25);
  bb.AddBirthday(Implementation.Mike, Implementation.Dec20);
  bb.AddBirthday(Implementation.Susan, Implementation.Dec20);

  var f := bb.FindBirthday(Implementation.John);
  assert f == Implementation.Mar25;

  var cards := bb.Remind(Implementation.Dec20);
  print "Send cards to: ", cards, "\n";
}
