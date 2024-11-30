module {:extract_boogie} Sequences {
  export
    provides Boxes
    provides Seq, Length, AboutLength
    provides Empty, LengthEmpty0, LengthEmpty1
    provides Index, Append, IndexAppend
    provides Build, BuildInv0, BuildInv1, BuildInjective, LengthBuild
    provides Update, IndexUpdate, LengthUpdate
    provides Contains, SeqContainsItsElements, EmptyContainsNothing, AppendContains, BuildContains
    provides Equal, AboutEqual, Extensionality
    provides SameUntil, AboutSameUntil
    provides Take, LengthTake, IndexTake
    provides Drop, LengthDrop, IndexDrop0, IndexDrop1
    provides TakeContains, DropContains, AppendTakeDrop
    provides DropNothing, TakeNothing, DropDrop
    provides TakeUpdate0, TakeUpdate1, DropUpdate0, DropUpdate1, DropBuild
  // For friends, we also export the fact that a sequence is represented as a list.
  export Friends extends Sequences
    reveals Seq, Empty, Length, Index, Append, Build, Update
    provides Lists, TailContains

  import opened Lists
  import opened Boxes

  // boogie: type Seq;
  type {:extract_boogie_name "Seq"} Seq = List<Box>

  // boogie: function Seq#Length(Seq): int;
  function {:extract_boogie_name "Seq#Length"} Length(s: Seq): int {
    s.Length()
  }

  // boogie: axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));
  lemma {:extract_pattern Length(s)} AboutLength(s: Seq)
    ensures 0 <= Length(s)
  {
  }

  // boogie: function Seq#Empty(): Seq;
  function {:extract_boogie_name "Seq#Empty"} Empty(): Seq {
    Nil
  }

  // boogie: axiom Seq#Length(Seq#Empty()) == 0;
  lemma {:extract_used_by Empty} LengthEmpty0()
    ensures Length(Empty()) == 0
  {
  }

  // boogie axiom (forall s: Seq :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
  lemma {:extract_pattern Length(s)} LengthEmpty1(s: Seq)
    requires Length(s) == 0
    ensures s == Empty()
  {
  }

  // boogie:
  // The following would be a nice fact to include, because it would enable verifying the
  // GenericPick.SeqPick* methods in Test/dafny0/SmallTests.dfy.  However, it substantially
  // slows down performance on some other tests, including running seemingly forever on
  // some.
  //  axiom (forall s: Seq :: { Seq#Length(s) }
  //    Seq#Length(s) != 0 ==> (exists x: Box :: Seq#Contains(s, x)));

  // boogie: function Seq#Build(s: Seq, val: Box): Seq;
  function {:extract_boogie_name "Seq#Build"} Build(s: Seq, val: Box): Seq {
    s.Append(Cons(val, Nil))
  }

  // boogie: function Seq#Build_inv0(s: Seq) : Seq;
  function {:extract_boogie_name "Seq#Build_inv0"} BuildInv0(s: Seq): Seq {
    if s.Nil? then Nil else s.Take(s.Length() - 1)
  }
  // boogie: function Seq#Build_inv1(s: Seq) : Box;
  function {:extract_boogie_name "Seq#Build_inv1"} BuildInv1(s: Seq): Box {
    if s.Nil? then
      Boxes.arbitrary
    else
      s.AboutDrop(s.Length() - 1);
      s.Drop(s.Length() - 1).head
  }

  // boogie:
  // axiom (forall s: Seq, val: Box ::
  //   { Seq#Build(s, val) }
  //   Seq#Build_inv0(Seq#Build(s, val)) == s &&
  //   Seq#Build_inv1(Seq#Build(s, val)) == val);
  lemma {:extract_pattern Build(s, val)} BuildInjective(s: Seq, val: Box)
    ensures BuildInv0(Build(s, val)) == s
    ensures BuildInv1(Build(s, val)) == val
  {
    var b := Build(s, val);
    var valList := Cons(val, Nil);
    assert b == s.Append(valList) != Nil;
    assert L: b.Length() == s.Length() + 1 by {
      s.LengthAppend(valList);
    }

    calc {
      BuildInv0(b);
      s.Append(valList).Take(b.Length() - 1);
      { reveal L; }
      s.Append(valList).Take(s.Length());
      { s.AppendTake(valList); }
      s;
    }

    calc {
      BuildInv1(b);
      { b.AboutDrop(b.Length() - 1); }
      b.Drop(b.Length() - 1).head;
      { reveal L; }
      s.Append(valList).Drop(s.Length()).head;
      { s.AppendDrop(valList); }
      valList.head;
      val;
    }
  }

  // boogie:
  // axiom (forall s: Seq, v: Box ::
  //   { Seq#Build(s,v) }
  //   Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
  lemma {:extract_pattern Build(s, v)} LengthBuild(s: Seq, v: Box)
    ensures Length(Build(s, v)) == 1 + Length(s)
  {
    var valList := Cons(v, Nil);
    assert valList.Length() == 1;
    s.LengthAppend(valList);
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box :: { Seq#Index(Seq#Build(s,v), i) }
  //   (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  //   (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));
  lemma {:extract_pattern Index(Build(s, v), i)} IndexBuild(s: Seq, i: int, v: Box)
    ensures i == Length(s) ==> Index(Build(s, v), i) == v
    ensures i != Length(s) ==> Index(Build(s, v), i) == Index(s, i)
  {
    var b := Build(s, v);
    var valList := Cons(v, Nil);
    assert b == s.Append(valList) != Nil;
    assert b.Length() == s.Length() + 1 by {
      s.LengthAppend(valList);
    }

    if 0 <= i < b.Length() {
      calc {
        Index(Build(s, v), i);
        Index(s.Append(valList), i);
        s.Append(valList).At(i);
        { s.AppendAt(valList, i); }
        if i < Length(s) then s.At(i) else valList.At(0);
      }
    }
  }

  // boogie:
  // axiom (forall s0: Seq, s1: Seq :: { Seq#Length(Seq#Append(s0,s1)) }
  //   Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
  lemma {:extract_pattern Length(Append(s0, s1))} LengthAppend(s0: Seq, s1: Seq)
    ensures Length(Append(s0, s1)) == Length(s0) + Length(s1)
  {
    s0.LengthAppend(s1);
  }

  // boogie: function Seq#Index(Seq, int): Box;
  function {:extract_boogie_name "Seq#Index"} Index(s: Seq, i: int): Box {
    if 0 <= i < Length(s) then
      s.At(i)
    else
      Boxes.arbitrary
  }

  // boogie:
  // axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  //   (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  //   (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
  lemma {:extract_pattern Index(Append(s0, s1), n)} IndexAppend(s0: Seq, s1: Seq, n: int)
    ensures n < Length(s0) ==> Index(Append(s0, s1), n) == Index(s0, n)
    ensures Length(s0) <= n ==> Index(Append(s0, s1), n) == Index(s1, n - Length(s0))
  {
    if
    case n < 0 =>

    case 0 <= n < Length(s0) =>
      if n == 0 {
        calc {
          Index(Append(s0, s1), 0);
          Index(Cons(s0.head, Append(s0.tail, s1)), 0);
          s0.head;
          Index(Cons(s0.head, s0.tail), 0);
          Index(s0, 0);
        }
      } else {
        calc {
          Index(Append(s0, s1), n);
          // def. Append
          Index(Cons(s0.head, Append(s0.tail, s1)), n);
          // def. Index
          Index(Append(s0.tail, s1), n - 1);
          { IndexAppend(s0.tail, s1, n - 1); }
          Index(s0.tail, n - 1);
          // def. Index
          Index(Cons(s0.head, s0.tail), n);
          Index(s0, n);
        }
      }

    case Length(s0) <= n =>
      match s0
      case Nil =>
        calc {
          Index(Append(s0, s1), n);
          // def. Append
          Index(s1, n);
          // def. Length
          Index(s1, n - Length(s0));
        }
      case Cons(x, tail) =>
        calc {
          Index(Append(s0, s1), n);
          // def. Append
          Index(Cons(s0.head, Append(s0.tail, s1)), n);
          // def. Index
          Index(Append(s0.tail, s1), n - 1);
          { IndexAppend(s0.tail, s1, n - 1); }
          Index(s1, n - 1 - Length(s0.tail));
          // def. Length
          Index(s1, n - Length(s0));
        }
  }

  // boogie: function Seq#Update(Seq, int, Box): Seq;
  function {:extract_boogie_name "Seq#Update"} Update(s: Seq, i: int, val: Box): Seq {
    if !(0 <= i < s.Length()) then
      s
    else if i == 0 then
      Cons(val, s.tail)
    else
      Cons(s.head, Update(s.tail, i - 1, val))
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box :: { Seq#Length(Seq#Update(s,i,v)) }
  //   0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
  lemma {:extract_pattern Length(Update(s, i, v))} LengthUpdate(s: Seq, i: int, v: Box)
    requires 0 <= i < Length(s)
    ensures Length(Update(s, i, v)) == Length(s)
  {
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  //   0 <= n && n < Seq#Length(s) ==>
  //     (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
  //     (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
  lemma {:extract_pattern Index(Update(s, i, v), n)} IndexUpdate(s: Seq, i: int, v: Box, n: int)
    requires 0 <= n < Length(s)
    ensures i == n ==> Index(Update(s, i, v), n) == v
    ensures i != n ==> Index(Update(s, i, v), n) == Index(s, n)
  {
    if 0 == i < s.Length() {
      calc {
        Index(Update(s, i, v), n);
        { LengthUpdate(s, i, v); }
        Update(s, i, v).At(n);
        Cons(v, s.tail).At(n);
      }

    } else if 0 < i < s.Length() {
      LengthUpdate(s, i, v);
      calc {
        Index(Update(s, i, v), n);
        Update(s, i, v).At(n);
        Cons(s.head, Update(s.tail, i - 1, v)).At(n);
      }
      if n == 0 {
        calc {
          Cons(s.head, Update(s.tail, i - 1, v)).At(n);
          s.head;
          Cons(s.head, s.tail).At(n);
          s.At(n);
          Index(s, n);
        }
      } else {
        calc {
          Cons(s.head, Update(s.tail, i - 1, v)).At(n);
          Update(s.tail, i - 1, v).At(n - 1);
          { IndexUpdate(s.tail, i - 1, v, n - 1); }
          if i == n then v else Index(s.tail, n - 1);
          if i == n then v else Index(s, n);
        }
      }
    }
  }

  // boogie: function Seq#Append(Seq, Seq): Seq;
  function {:extract_boogie_name "Seq#Append"} Append(s0: Seq, s1: Seq): Seq {
    s0.Append(s1)
  }

  // boogie: function Seq#Contains(Seq, Box): bool;
  predicate {:extract_boogie_name "Seq#Contains"} Contains(s: Seq, val: Box) {
    exists i :: 0 <= i < Length(s) && Index(s, i) == val
  }

  lemma TailContains(s: Seq, val: Box)
    requires s.Cons?
    ensures Contains(s, val) <==> s.head == val || Contains(s.tail, val)
  {
    if Contains(s, val) {
      var i :| 0 <= i < Length(s) && Index(s, i) == val;
      if i != 0 {
        var j := i - 1;
        assert Index(s, i) == Index(s.tail, j);
        assert 0 <= j < Length(s.tail) && Index(s.tail, j) == val;
      }
    }

    if !Contains(s, val) {
      assert forall i :: 0 <= i < Length(s) ==> Index(s, i) != val;
      assert s.head == Index(s, 0) != val;
      forall j | 0 <= j < Length(s.tail)
        ensures Index(s.tail, j) != val
      {
        assert Index(s.tail, j) == Index(s, j + 1);
      }
    }
  }

  // boogie:
  // axiom (forall s: Seq, x: Box :: { Seq#Contains(s,x) }
  //   Seq#Contains(s,x) <==>
  //     (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
  lemma {:extract_pattern Contains(s, x)} SeqContainsItsElements(s: Seq, x: Box)
    ensures Contains(s, x) <==>
            exists i {:extract_pattern Index(s, i)} :: 0 <= i < Length(s) && Index(s, i) == x
  {
  }

  // boogie:
  // axiom (forall x: Box ::
  //   { Seq#Contains(Seq#Empty(), x) }
  //   !Seq#Contains(Seq#Empty(), x));
  lemma {:extract_pattern Contains(Empty(), x)} EmptyContainsNothing(x: Box)
    ensures !Contains(Empty(), x)
  {
  }

  // boogie:
  // axiom (forall s0: Seq, s1: Seq, x: Box ::
  //   { Seq#Contains(Seq#Append(s0, s1), x) }
  //   Seq#Contains(Seq#Append(s0, s1), x) <==>
  //     Seq#Contains(s0, x) || Seq#Contains(s1, x));
  lemma {:extract_pattern Contains(Append(s0, s1), x)} AppendContains(s0: Seq, s1: Seq, x: Box)
    ensures Contains(Append(s0, s1), x) <==> Contains(s0, x) || Contains(s1, x)
  {
    var a := Append(s0, s1);
    s0.LengthAppend(s1);

    if Contains(a, x) {
      var i :| 0 <= i < Length(a) && Index(a, i) == x;
      assert a.At(i) == if i < s0.Length() then s0.At(i) else s1.At(i - s0.Length()) by {
        s0.AppendAt(s1, i);
      }

      if i < s0.Length() {
        assert Contains(s0, x) by {
          assert 0 <= i < Length(s0) && Index(s0, i) == x;
        }
      } else {
        var j := i - s0.Length();
        assert Contains(s1, x) by {
          assert x == Index(s1, j);
        }
      }
    }

    if Contains(s0, x) {
      var i :| 0 <= i < Length(s0) && Index(s0, i) == x;
      assert Contains(a, x) by {
        assert Index(a, i) == x by {
          s0.AppendAt(s1, i);
        }
      }
    }

    if Contains(s1, x) {
      var j :| 0 <= j < Length(s1) && Index(s1, j) == x;
      var i := s0.Length() + j;
      assert Contains(a, x) by {
        assert Index(a, i) == x by {
          s0.AppendAt(s1, i);
        }
      }
    }
  }

  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
  // boogie:
  // axiom (forall s: Seq, v: Box, x: Box ::
  //   { Seq#Contains(Seq#Build(s, v), x) }
  //   Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));
  lemma {:extract_pattern Contains(Build(s, v), x)} BuildContains(s: Seq, v: Box, x: Box)
    ensures Contains(Build(s, v), x) <==> v == x || Contains(s, x)
  {
    var valList := Cons(v, Nil);
    var b := s.Append(valList);
    assert b == Build(s, v);

    assert Ping: v == x ==> Contains(valList, x) by {
      assert Index(valList, 0) == v;
    }
    assert Pong: Contains(valList, x) ==> v == x by {
      if Contains(valList, x) {
        var i :| 0 <= i < valList.Length() && Index(valList, i) == x;
        assert valList.Length() == 1;
      }
    }

    calc {
      Contains(b, x);
      { AppendContains(s, valList, x); }
      Contains(s, x) || Contains(valList, x);
      { reveal Ping, Pong; }
      v == x || Contains(s, x);
    }
  }

  // boogie:
  // axiom (forall s: Seq, n: int, x: Box ::
  //   { Seq#Contains(Seq#Take(s, n), x) }
  //   Seq#Contains(Seq#Take(s, n), x) <==>
  //     (exists i: int :: { Seq#Index(s, i) }
  //       0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
  lemma {:extract_pattern Contains(Take(s, n), x)} TakeContains(s: Seq, n: int, x: Box)
    ensures Contains(Take(s, n), x) <==>
            exists i {:extract_pattern Index(s, i)} :: 0 <= i < n && i < Length(s) && Index(s, i) == x
  {
    if
    case n < 0 =>
      calc {
        Contains(Take(s, n), x);
        { assert Take(s, n) == Empty(); }
        Contains(Empty(), x);
        false;
        exists i :: 0 <= i < n && i < Length(s) && Index(s, i) == x;
      }

    case 0 <= n <= s.Length() =>
      var (prefix, suffix) := s.Split(n);
      var t := s.Take(n);
      assert t == prefix;
      assert t.Length() == n by {
        s.LengthTakeDrop(n);
      }
      assert L: forall i :: 0 <= i < Length(t) ==> Index(t, i) == Index(s, i) by {
        forall i | 0 <= i < Length(t)
          ensures Index(t, i) == Index(s, i)
        {
          prefix.AppendAt(suffix, i);
        }
      }

      calc {
        Contains(t, x);
        exists i :: 0 <= i < Length(t) && Index(t, i) == x;
        { reveal L; }
        exists i :: 0 <= i < n && i < Length(s) && Index(s, i) == x;
      }

    case s.Length() < n =>
      calc {
        Contains(Take(s, n), x);
        Contains(s, x);
        exists i :: 0 <= i < Length(s) && Index(s, i) == x;
        { assert Length(s) < n; }
        exists i :: 0 <= i < n && i < Length(s) && Index(s, i) == x;
      }
  }

  // boogie:
  // axiom (forall s: Seq, n: int, x: Box ::
  //   { Seq#Contains(Seq#Drop(s, n), x) }
  //   Seq#Contains(Seq#Drop(s, n), x) <==>
  //     (exists i: int :: { Seq#Index(s, i) }
  //       0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
  lemma {:extract_pattern Contains(Drop(s, n), x)} DropContains(s: Seq, n: int, x: Box)
    ensures Contains(Drop(s, n), x) <==>
            exists i {:extract_pattern Index(s, i)} :: 0 <= n <= i < Length(s) && Index(s, i) == x
  {
    if 0 <= n <= s.Length() {
      var (prefix, suffix) := s.Split(n);
      var t := s.Take(n);
      assert t == prefix;
      assert t.Length() == n by {
        s.LengthTakeDrop(n);
      }
      assert L: forall i :: 0 <= i < Length(suffix) ==> Index(suffix, i) == Index(s, n + i) by {
        forall i | 0 <= i < Length(suffix) {
          calc {
            Index(s, n + i);
            { prefix.LengthAppend(suffix); }
            s.At(n + i);
            { prefix.AppendAt(suffix, n + i); }
            suffix.At(i);
            Index(suffix, i);
          }
        }
      }

      if Contains(Drop(s, n), x) {
        var j :| 0 <= j < Length(suffix) && Index(suffix, j) == x;
        var i := n + j;
        assert 0 <= n <= i < Length(s) by {
          prefix.LengthAppend(suffix);
        }
        assert Index(s, i) == x by {
          reveal L;
        }
      }

      if i :| 0 <= n <= i < Length(s) && Index(s, i) == x {
        var j := i - n;
        assert 0 <= j < Length(suffix) by {
          prefix.LengthAppend(suffix);
        }
        assert Index(suffix, j) == x by {
          reveal L;
        }
      }

    } else {
      calc {
        Contains(Drop(s, n), x);
        Contains(Empty(), x);
        false;
        exists i :: 0 <= n <= i < Length(s) && Index(s, i) == x;
      }
    }
  }

  // boogie: function Seq#Equal(Seq, Seq): bool;
  predicate {:extract_boogie_name "Seq#Equal"} Equal(s0: Seq, s1: Seq) {
    s0 == s1
  }

  // boogie:
  // axiom (forall s0: Seq, s1: Seq :: { Seq#Equal(s0,s1) }
  //   Seq#Equal(s0,s1) <==>
  //     Seq#Length(s0) == Seq#Length(s1) &&
  //     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
  //         0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
  lemma {:extract_pattern Equal(s0, s1)} AboutEqual(s0: Seq, s1: Seq)
    ensures Equal(s0, s1) <==>
            && Length(s0) == Length(s1)
            && forall j {:extract_pattern Index(s0, j)} {:extract_pattern Index(s1, j)} ::
                 0 <= j < Length(s0) ==> Index(s0, j) == Index(s1, j)
  {
    if Length(s0) == Length(s1) && forall j :: 0 <= j < Length(s0) ==> Index(s0, j) == Index(s1, j) {
      assert forall s, i :: 0 <= i < Length(s) ==> Index(s, i) == s.At(i);
      DatatypeEquality(s0, s1);
    }
  }

  lemma DatatypeEquality(s0: Seq, s1: Seq)
    requires s0.Length() == s1.Length()
    requires forall j :: 0 <= j < s0.Length() ==> s0.At(j) == s1.At(j)
    ensures s0 == s1
  {
    if s0.Length() != 0 {
      assert s0.head == s1.head by {
        assert s0.head == s0.At(0) && s1.head == s1.At(0);
      }
      var t0, t1 := s0.tail, s1.tail;
      assert t0.Length() == t1.Length();
      assert forall i :: 0 <= i < t0.Length() ==> t0.At(i) == s0.At(i + 1);
      assert forall i :: 0 <= i < t0.Length() ==> t0.At(i) == t1.At(i);
    }
  }

  // extensionality axiom for sequences
  // boogie:
  // axiom (forall a: Seq, b: Seq :: { Seq#Equal(a,b) }
  //   Seq#Equal(a,b) ==> a == b);
  lemma {:extract_pattern Equal(a, b)} Extensionality(a: Seq, b: Seq)
    requires Equal(a, b)
    ensures a == b
  {
  }

  // boogie: function Seq#SameUntil(Seq, Seq, int): bool;
  predicate {:extract_boogie_name "Seq#SameUntil"} SameUntil(s0: Seq, s1: Seq, n: int) {
    forall j :: 0 <= j < n ==> Index(s0, j) == Index(s1, j)
  }

  // boogie:
  // axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#SameUntil(s0,s1,n) }
  //   Seq#SameUntil(s0,s1,n) <==>
  //     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
  //         0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
  lemma {:extract_pattern SameUntil(s0, s1, n)} AboutSameUntil(s0: Seq, s1: Seq, n: int)
    ensures SameUntil(s0, s1, n) <==>
            forall j {:extract_pattern Index(s0, j)} {:extract_pattern Index(s1, j)} ::
              0 <= j < n ==> Index(s0, j) == Index(s1, j)
  {
  }

  // boogie: function Seq#Take(s: Seq, howMany: int): Seq;
  function {:extract_boogie_name "Seq#Take"} Take(s: Seq, howMany: int): Seq {
    if howMany < 0 then
      Empty()
    else if howMany <= s.Length() then
      s.Take(howMany)
    else
      s
  }

  // boogie:
  // axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Take(s,n)) }
  //   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);
  lemma {:extract_pattern Length(Take(s, n))} LengthTake(s: Seq, n: int)
    requires 0 <= n <= Length(s)
    ensures Length(Take(s, n)) == n
  {
    s.LengthTakeDrop(n);
  }

  // boogie:
  // axiom (forall s: Seq, n: int, j: int ::
  //   {:weight 25}
  //   { Seq#Index(Seq#Take(s,n), j) }
  //   { Seq#Index(s, j), Seq#Take(s,n) }
  //   0 <= j && j < n && j < Seq#Length(s) ==>
  //     Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
  lemma {:extract_attribute "weight", 25} {:extract_pattern Index(Take(s, n), j)} {:extract_pattern Index(s, j), Take(s, n)}
    IndexTake(s: Seq, n: int, j: int)
    requires 0 <= j < n && j < Length(s)
    ensures Index(Take(s, n), j) == Index(s, j)
  {
    if j != 0 && n <= s.Length() {
      IndexTake(s.tail, n - 1, j - 1);
    }
  }

  // boogie: function Seq#Drop(s: Seq, howMany: int): Seq;
  function {:extract_boogie_name "Seq#Drop"} Drop(s: Seq, howMany: int): Seq {
    if 0 <= howMany <= s.Length() then
      s.Drop(howMany)
    else
      Empty()
  }

  // boogie:
  // axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  //   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);
  lemma {:extract_pattern Length(Drop(s, n))} LengthDrop(s: Seq, n: int)
    requires 0 <= n <= Length(s)
    ensures Length(Drop(s, n)) == Length(s) - n
  {
    s.LengthTakeDrop(n);
  }

  // boogie:
  // axiom (forall s: Seq, n: int, j: int ::
  //   {:weight 25}
  //   { Seq#Index(Seq#Drop(s,n), j) }
  //   0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
  //     Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
  lemma {:extract_attribute "weight", 25} {:extract_pattern Index(Drop(s, n), j)} IndexDrop0(s: Seq, n: int, j: int)
    requires 0 <= n && 0 <= j < Length(s) - n
    ensures Index(Drop(s, n), j) == Index(s, j + n)
  {
    IndexDrop1(s, n, j + n);
  }

  // boogie:
  // axiom (forall s: Seq, n: int, k: int ::
  //   {:weight 25}
  //   { Seq#Index(s, k), Seq#Drop(s,n) }
  //   0 <= n && n <= k && k < Seq#Length(s) ==>
  //     Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));
  lemma {:extract_attribute "weight", 25} {:extract_pattern Index(s, k), Drop(s, n)} IndexDrop1(s: Seq, n: int, k: int)
    requires 0 <= n <= k < Length(s)
    ensures Index(Drop(s, n), k - n) == Index(s, k)
  {
    if n != 0 {
      IndexDrop1(s.tail, n - 1, k - 1);
    }
  }

  // boogie:
  // axiom (forall s, t: Seq, n: int ::
  //   { Seq#Take(Seq#Append(s, t), n) }
  //   { Seq#Drop(Seq#Append(s, t), n) }
  //   n == Seq#Length(s)
  //   ==>
  //   Seq#Take(Seq#Append(s, t), n) == s &&
  //   Seq#Drop(Seq#Append(s, t), n) == t);
  lemma {:extract_pattern Take(Append(s, t), n)} {:extract_pattern Drop(Append(s, t), n)} AppendTakeDrop(s: Seq, t: Seq, n: int)
    requires n == Length(s)
    ensures Take(Append(s, t), n) == s
    ensures Drop(Append(s, t), n) == t
  {
    var a := Append(s, t);
    assert 0 <= n <= Length(a) by {
      s.LengthAppend(t);
    }
    s.AppendTake(t);
    s.AppendDrop(t);
  }

  // Commutativity of Take and Drop with Update.

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box, n: int ::
  //         { Seq#Take(Seq#Update(s, i, v), n) }
  //         0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
  lemma {:extract_pattern Take(Update(s, i, v), n)} TakeUpdate0(s: Seq, i: int, v: Box, n: int)
    requires 0 <= i < n <= Length(s)
    ensures Take(Update(s, i, v), n) == Update(Take(s, n), i, v)
    decreases i
  {
    if i != 0 {
      TakeUpdate0(s.tail, i - 1,  v, n - 1);
    }
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box, n: int ::
  //         { Seq#Take(Seq#Update(s, i, v), n) }
  //         n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
  lemma {:extract_pattern Take(Update(s, i, v), n)} TakeUpdate1(s: Seq, i: int, v: Box, n: int)
    requires n <= i < Length(s)
    ensures Take(Update(s, i, v), n) == Take(s, n)
  {
    if 0 <= n && i != 0 {
      TakeUpdate1(s.tail, i - 1, v, n - 1);
    }
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box, n: int ::
  //         { Seq#Drop(Seq#Update(s, i, v), n) }
  //         0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
  lemma {:extract_pattern Drop(Update(s, i, v), n)} DropUpdate0(s: Seq, i: int, v: Box, n: int)
    requires 0 <= n <= i < Length(s)
    ensures Drop(Update(s, i, v), n) == Update(Drop(s, n), i - n, v)
  {
    if n != 0 {
      DropUpdate0(s.tail, i - 1, v, n - 1);
    }
  }

  // boogie:
  // axiom (forall s: Seq, i: int, v: Box, n: int ::
  //         { Seq#Drop(Seq#Update(s, i, v), n) }
  //         0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
  lemma {:extract_pattern Drop(Update(s, i, v), n)} DropUpdate1(s: Seq, i: int, v: Box, n: int)
    requires 0 <= i < n <= Length(s)
    ensures Drop(Update(s, i, v), n) == Drop(s, n)
  {
    if i != 0 {
      DropUpdate1(s.tail, i - 1, v, n - 1);
    }
  }

  // Drop commutes with build

  // boogie:
  // axiom (forall s: Seq, v: Box, n: int ::
  //         { Seq#Drop(Seq#Build(s, v), n) }
  //         0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );
  lemma {:extract_pattern Drop(Build(s, v), n)} DropBuild(s: Seq, v: Box, n: int)
    requires 0 <= n <= Length(s)
    ensures Drop(Build(s, v), n) == Build(Drop(s, n), v)
  {
    if n != 0 {
      calc {
        Drop(Build(s, v), n);
        Drop(Cons(s.head, Build(s.tail, v)), n);
        Drop(Build(s.tail, v), n - 1);
        { DropBuild(s.tail, v, n - 1); }
        Build(Drop(s.tail, n - 1), v);
        Build(Drop(s, n), v);
      }
    }
  }

  // Additional axioms about common things

  // boogie:
  // axiom (forall s: Seq, n: int :: { Seq#Drop(s, n) }
  //         n == 0 ==> Seq#Drop(s, n) == s);
  lemma {:extract_pattern Drop(s, n)} DropNothing(s: Seq, n: int)
    requires n == 0
    ensures Drop(s, n) == s
  {
  }

  // boogie:
  // axiom (forall s: Seq, n: int :: { Seq#Take(s, n) }
  //         n == 0 ==> Seq#Take(s, n) == Seq#Empty());
  lemma {: extract_pattern Take(s, n)} TakeNothing(s: Seq, n: int)
    requires n == 0
    ensures Take(s, n) == Empty()
  {
  }

  // boogie:
  // axiom (forall s: Seq, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
  //         0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
  //         Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));
  lemma {:extract_pattern Drop(Drop(s, m), n)} DropDrop(s: Seq, m: int, n: int)
    requires 0 <= m && 0 <= n && m + n <= Length(s)
    ensures Drop(Drop(s, m), n) == Drop(s, m + n)
  {
    if m != 0 {
      DropDrop(s.tail, m - 1, n);
    }
  }

}
