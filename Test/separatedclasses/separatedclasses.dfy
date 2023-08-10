// RUN: %exits-with 4 %baredafny verify %args --region-checks:true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SeparatedClasses {
  class WrapperNat {
    var value: nat
    constructor(value: nat) ensures Region == null && this.value == value {
      this.value := value;
      this.Region := null;
    }
  }
  class AtomicSendReceiveCounts {
    var sent: WrapperNat
    var received: WrapperNat
    var waiting: nat
    constructor()
      ensures Valid()
    {
      sent := new WrapperNat(0);
      received := new WrapperNat(0);
      waiting := 0;
      new;
      sent.Region := this;
      received.Region := this;
      this.Region := this;
    }
    ghost predicate {:invariant} Valid() reads this, sent, received { // TODO: Test where {:invariant} without region checks result in an error
      && received.value + waiting == sent.value
      && this.Region == this
      && sent != received
      && sent.Region == this && received.Region == this
    }
    function GetSent(): nat
      // Note: does not require the invariant
      reads this, sent
    { sent.value }
    function GetReceive(): nat
      reads this, received
    { received.value }
    function GetReceivedSent(): (result: (nat, nat))
      reads this, received, sent
      requires Valid()
      ensures result.1 <= result.0
    {
      (sent.value, received.value)
    }
    // Given a new send value, will swap it with the old sent value
    // but only if the value is greater or equal. Otherwise, it will return newSent
    method ReplaceSent(newSent: WrapperNat) returns (result: WrapperNat)
      requires Valid()
      requires newSent.Region == null // Checked at call site
      modifies this, sent, newSent
      ensures result.Region == null
      ensures unchanged(newSent`value)
      ensures unchanged(this`received)
      ensures unchanged(received)
      ensures
        if result.value == newSent.value then
          // No swap was done
          unchanged(this)
        else
          && this.sent == newSent
          && result == old(this.sent)
          && result.value < newSent.value
          && newSent.Region == this
      ensures Valid()
    {
      // Because of the region field, we can figure out this easily
      assert newSent as object !in {this, this.sent, this.received};
      if newSent.value <= sent.value {
        result := newSent;
      } else {
        result := this.sent;
        result.Region := null; // Now externally modifiable
        waiting := waiting + (newSent.value - sent.value);
        this.sent := newSent;
        newSent.Region := this;
      }
    }

    method GetReceivedSentM() returns (result: (nat, nat))
      requires Valid()
      //reads this // TODO:
      ensures result.1 <= result.0
      ensures Valid()
    {
      return GetReceivedSent();
    }

    method Send()
      requires Valid()
      modifies this, sent
      ensures Valid()
    {
      ExternalCall(this); // THe invariant is proven here.
      // And is assumed here.
      assert Valid();     // OK, can be proven
      this.sent.value := this.sent.value + 1;
      waiting := waiting + 1;
      ExternalCall(this); // THe invariant is proven here.
    }
    static method ExternalCall(a: AtomicSendReceiveCounts)
      modifies a
    {
      var a := a.GetSent();
      // Even though a is said to be modified, the invariant is still assumed
    }
    method Receive() returns (result: bool)
      requires Valid()
      modifies this, received
      ensures Valid()
      // This ensures is useless at the caller's site in multithreaded mode
      ensures if !result then received == old(received) && unchanged(received) else received.value == old(received.value) + 1
    {
      if sent.value > received.value {
        received.value := received.value + 1;
        waiting := waiting - 1;
        result := true;
      } else {
        result := false;
      }
    }
    method DontEnsureValidButOnlyReads()
      requires Valid()
      // A method that does not ensure Valid() but only reads can be called externally
    {

    }
  }
  // TODO: Make internal once threads are implemented
  class Promise<T> {
    var value: T
    constructor(t: T)/* {

    }
    predicate {:invariant} Valid() reads this { // This predicates make the value inaccessible yet
      this.Region == this 
    }*/
    method Join() returns (result: T )
  }
  // TODO: Remove returns once spawn is implemented
  method {:vcs_split_on_every_assert} RunSend(a: AtomicSendReceiveCounts, count: nat) returns (k: Promise<()>)
    // reads {}
    modifies {}
  {
    var i := count;
    var initialSent := a.GetSent();  // OK, no need to prove the reads clause
    a.DontEnsureValidButOnlyReads(); // OK, the invariant is assumed
    while i > 0 invariant i >= 0 {
      a.Send(); // No need to prove Valid() there and no modifies either
      i := i - 1;
    }
    k := new Promise(()); // TODO, should not be needed
  }
  method RunReceive(a: AtomicSendReceiveCounts, count: nat) returns (k: Promise<()>)
    decreases *
    modifies {}
  {
    var i := count;
    while i > 0
      invariant i >= 0
      decreases *
    {
      var result := a.Receive(); // No need to prove Valid() there and no modifies either
      if(result) {
        i := i - 1;
      }
    }
    k := new Promise(()); // TODO, should not be needed
  }
  method {:test} Test()
    decreases * // Necessary because spawning threads that might have blocking calls or infinite loops
  {
    var a := new AtomicSendReceiveCounts();
    var promise := /*spawn */RunSend(a, 10); // Will return a Promise<()>
    var promise2 := /*spawn */RunReceive(a, 7); // TODO: Put before send when threads work.
    var _ := promise.Join();
    var _ := promise2.Join();
    var sent := a.GetSent();
    var received := a.GetReceive();
  }

  // TODO: Call a separated class 
}