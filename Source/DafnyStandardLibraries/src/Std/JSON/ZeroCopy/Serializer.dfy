/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Implements low-level (zero-copy) serialization (JSON syntax trees to utf-8 bytes).
 Proves that the serializer is sound and complete w.r.t. the functional specification
 defined in `ConcreteSyntax.Spec.dfy`.
 */
module Std.JSON.ZeroCopy.Serializer {
  import ConcreteSyntax.Spec
  import ConcreteSyntax.SpecProperties
  import opened BoundedInts
  import opened Wrappers
  import opened Seq = Collections.Seq
  import opened Errors
  import opened Grammar
  import opened Utils.Views.Writers
  import opened Vs = Utils.Views.Core

  method Serialize(js: JSON) returns (rbs: SerializationResult<array<byte>>)
    ensures rbs.Success? ==> fresh(rbs.value)
    ensures rbs.Success? ==> rbs.value[..] == Spec.JSON(js)
  {
    var writer := Text(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    var bs := writer.ToArray();
    return Success(bs);
  }

  method SerializeTo(js: JSON, dest: array<byte>) returns (len: SerializationResult<uint32>)
    modifies dest
    ensures len.Success? ==> len.value as int <= dest.Length
    ensures len.Success? ==> dest[..len.value] == Spec.JSON(js)
    ensures len.Success? ==> dest[len.value..] == old(dest[len.value..])
    ensures len.Failure? ==> unchanged(dest)
  {
    var writer := Text(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    :- Need(writer.length as int <= dest.Length, OutOfMemory);
    writer.CopyTo(dest);
    return Success(writer.length);
  }

  function Text(js: JSON) : (wr: Writer)
    ensures wr.Bytes() == Spec.JSON(js)
  {
    JSON(js)
  }

  function JSON(js: JSON, writer: Writer := Writer.Empty) : (wr: Writer)
    ensures wr.Bytes() == writer.Bytes() + Spec.JSON(js)
  {
    Seq.LemmaConcatIsAssociative2(writer.Bytes(),js.before.Bytes(), Spec.Value(js.t), js.after.Bytes());
    writer
    .Append(js.before)
    .Then((wr: Writer) => Value(js.t, wr))
    .Append(js.after)
  }

  @IsolateAssertions
  function Value(v: Grammar.Value, writer: Writer) : (wr: Writer)
    decreases v, 4
    ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
  {
    match v
    case Null(n) =>
      var wr := writer.Append(n);
      wr
    case Bool(b) =>
      var wr := writer.Append(b);
      wr
    case String(str) =>
      var wr := String(str, writer);
      calc {
        wr.Bytes();
        { assert wr == String(v.str, writer); }
        writer.Bytes() + Spec.String(v.str);
        { assert v.String?; assert v.String? ==> Spec.Value(v) == Spec.String(v.str); }
        writer.Bytes() + Spec.Value(v);
      }
      wr
    case Number(num) =>
      var wr := Number(num, writer);
      calc {
        wr.Bytes();
        { assert wr == Number(v.num, writer); }
        writer.Bytes() + Spec.Number(v.num);
        { assert v.Number?; assert v.Number? ==> Spec.Value(v) == Spec.Number(v.num); }
        writer.Bytes() + Spec.Value(v);
      }
      wr
    case Object(obj) =>
      var wr := Object(obj, writer);
      calc {
        wr.Bytes();
        { assert wr == Object(v.obj, writer); }
        writer.Bytes() + Spec.Object(v.obj);
        { assert v.Object?; assert v.Object? ==> Spec.Value(v) == Spec.Object(v.obj); }
        writer.Bytes() + Spec.Value(v);
      }
      wr
    case Array(arr) =>
      var wr := Array(arr, writer);
      calc {
        wr.Bytes();
        { assert wr == Array(v.arr, writer); }
        writer.Bytes() + Spec.Array(v.arr);
        { assert v.Array?; assert v.Array? ==> Spec.Value(v) == Spec.Array(v.arr); }
        writer.Bytes() + Spec.Value(v);
      }
      wr
  }

  function String(str: jstring, writer: Writer) : (wr: Writer)
    decreases str, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.String(str)
  {
    hide *;
    reveal Writer.Append, Spec.String, Spec.View;
    writer
    .Append(str.lq)
    .Append(str.contents)
    .Append(str.rq)
  }

  @IsolateAssertions
  lemma NumberHelper1(num: jnumber, writer: Writer)
    ensures
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then
                                    writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes()
                                  else
                                    writer.Append(num.minus).Append(num.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes()
                                ) else (
                                         if num.frac.NonEmpty? then
                                           writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes()
                                         else
                                           writer.Append(num.minus).Append(num.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes()
                                       )
  {
    if num.exp.NonEmpty? {
      if num.frac.NonEmpty? {
        assert writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes();
      } else {
        assert writer.Append(num.minus).Append(num.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes();
      }
    } else {
      if num.frac.NonEmpty? {
        assert writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes();
      } else {
        assert writer.Append(num.minus).Append(num.num).Bytes() == writer.Bytes() + num.minus.Bytes() + num.num.Bytes();
      }
    }
  }

  @IsolateAssertions
  lemma NumberHelper2a(num: jnumber, writer: Writer)
    ensures Spec.Number(num) == num.minus.Bytes() + num.num.Bytes() + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp)
  {}

  @IsolateAssertions
  @ResourceLimit("10e6")
  lemma NumberHelper2(num: jnumber, writer: Writer)
    ensures
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then writer.Bytes() + Spec.Number(num) == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes() else writer.Bytes() + Spec.Number(num) == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes()
                                ) else (
                                         if num.frac.NonEmpty? then writer.Bytes() + Spec.Number(num) == writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() else writer.Bytes() + Spec.Number(num) == writer.Bytes() + num.minus.Bytes() + num.num.Bytes()
                                       )
  {
    if num.exp.NonEmpty? {
      if num.frac.NonEmpty? {
        calc {
          writer.Bytes() + Spec.Number(num);
          { NumberHelper2a(num, writer); }
          writer.Bytes() + (num.minus.Bytes() + num.num.Bytes() + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          { assert Spec.Maybe(num.frac, Spec.Frac) == Spec.Frac(num.frac.t); assert Spec.Maybe(num.exp, Spec.Exp) == Spec.Exp(num.exp.t); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (Spec.Frac(num.frac.t) + Spec.Exp(num.exp.t));
          { assert Spec.Frac(num.frac.t) == num.frac.t.period.Bytes() + num.frac.t.num.Bytes(); assert Spec.Exp(num.exp.t) == num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes(); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + ((num.frac.t.period.Bytes() + num.frac.t.num.Bytes()) + (num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes()));
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes();
        }
      } else {
        calc {
          writer.Bytes() + Spec.Number(num);
          { NumberHelper2a(num, writer); }
          writer.Bytes() + (num.minus.Bytes() + num.num.Bytes() + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          { assert Spec.Maybe(num.frac, Spec.Frac) == []; assert Spec.Maybe(num.exp, Spec.Exp) == Spec.Exp(num.exp.t); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + ([] + Spec.Exp(num.exp.t));
          { assert [] + Spec.Exp(num.exp.t) == Spec.Exp(num.exp.t); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + Spec.Exp(num.exp.t);
          { assert Spec.Exp(num.exp.t) == num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes(); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes());
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes();
        }
      }
    } else {
      if num.frac.NonEmpty? {
        calc {
          writer.Bytes() + Spec.Number(num);
          { NumberHelper2a(num, writer); }
          writer.Bytes() + (num.minus.Bytes() + num.num.Bytes() + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          { assert Spec.Maybe(num.exp, Spec.Exp) == []; assert Spec.Maybe(num.frac, Spec.Frac) == Spec.Frac(num.frac.t); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + (Spec.Frac(num.frac.t) + []);
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + Spec.Frac(num.frac.t);
          { assert Spec.Frac(num.frac.t) == num.frac.t.period.Bytes() + num.frac.t.num.Bytes(); }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes();
        }
      } else {
        calc {
          writer.Bytes() + Spec.Number(num);
          { NumberHelper2a(num, writer); }
          writer.Bytes() + (num.minus.Bytes() + num.num.Bytes() + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp));
          { assert Spec.Maybe(num.frac, Spec.Frac) == []; assert Spec.Maybe(num.exp, Spec.Exp) == []; }
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + [] + [];
          writer.Bytes() + num.minus.Bytes() + num.num.Bytes();
        }
      }
    }
  }

  @IsolateAssertions
  function Number(num: jnumber, writer: Writer) : (wr: Writer)
    decreases num, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Number(num)
  {
    var wr1 := writer.Append(num.minus).Append(num.num);
    var wr2 := if num.frac.NonEmpty? then
                 wr1.Append(num.frac.t.period).Append(num.frac.t.num)
               else wr1;
    var wr3 := if num.exp.NonEmpty? then
                 wr2.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num)
               else wr2;
    var wr := wr3;

    calc {
      wr.Bytes();
      { assert wr == wr3; }
      wr3.Bytes();
      { assert wr3 == if num.exp.NonEmpty? then wr2.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num) else wr2; }
      if num.exp.NonEmpty? then wr2.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() else wr2.Bytes();
      { assert wr2 == if num.frac.NonEmpty? then wr1.Append(num.frac.t.period).Append(num.frac.t.num) else wr1; }
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then wr1.Append(num.frac.t.period).Append(num.frac.t.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() else wr1.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes()
                                ) else (
                                         if num.frac.NonEmpty? then wr1.Append(num.frac.t.period).Append(num.frac.t.num).Bytes() else wr1.Bytes()
                                       );
      { assert wr1 == writer.Append(num.minus).Append(num.num); }
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes() else writer.Append(num.minus).Append(num.num).Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num).Bytes()
                                ) else (
                                         if num.frac.NonEmpty? then writer.Append(num.minus).Append(num.num).Append(num.frac.t.period).Append(num.frac.t.num).Bytes() else writer.Append(num.minus).Append(num.num).Bytes()
                                       );
      { NumberHelper1(num, writer); }
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes() else writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.exp.t.e.Bytes() + num.exp.t.sign.Bytes() + num.exp.t.num.Bytes()
                                ) else (
                                         if num.frac.NonEmpty? then writer.Bytes() + num.minus.Bytes() + num.num.Bytes() + num.frac.t.period.Bytes() + num.frac.t.num.Bytes() else writer.Bytes() + num.minus.Bytes() + num.num.Bytes()
                                       );
      { NumberHelper2(num, writer); }
      if num.exp.NonEmpty? then (
                                  if num.frac.NonEmpty? then writer.Bytes() + Spec.Number(num) else writer.Bytes() + Spec.Number(num)
                                ) else (
                                         if num.frac.NonEmpty? then writer.Bytes() + Spec.Number(num) else writer.Bytes() + Spec.Number(num)
                                       );
      writer.Bytes() + Spec.Number(num);
    }
    wr
  }

  // DISCUSS: Can't be opaque, due to the lambda
  @IsolateAssertions
  function StructuralView(st: Structural<View>, writer: Writer) : (wr: Writer)
    ensures wr.Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
  {
    hide *;
    reveal Writer.Append, Spec.Structural, Spec.View;
    writer.Append(st.before).Append(st.t).Append(st.after)
  }

  lemma StructuralViewEns(st: Structural<View>, writer: Writer)
    ensures StructuralView(st, writer).Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
  {}

  // FIXME refactor below to merge
  lemma BracketedToObject(obj: jobject)
    ensures Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj)
  {
    var rMember := (d: jmember) requires d < obj => Spec.Member(d);
    assert Spec.Bracketed(obj, Spec.Member) == Spec.Bracketed(obj, rMember) by {
      // We call ``ConcatBytes`` with ``Spec.Member``, whereas the spec calls it
      // with ``(d: jmember) requires d in obj.data => Spec.Member(d)``.  That's
      // why we need an explicit cast, which is performed by the lemma below.
      assert SpecProperties.Bracketed_Morphism_Requires(obj, Spec.Member, rMember);
      SpecProperties.Bracketed_Morphism(obj, Spec.Member, rMember);
    }
    calc {
      Spec.Bracketed(obj, Spec.Member);
      Spec.Bracketed(obj, rMember);
      Spec.Object(obj);
    }
  }

  function Object(obj: jobject, writer: Writer) : (wr: Writer)
    decreases obj, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Object(obj)
  {
    var wr := StructuralView(obj.l, writer);
    StructuralViewEns(obj.l, writer);
    var wr := Members(obj, wr);
    var wr := StructuralView(obj.r, wr);
    Seq.LemmaConcatIsAssociative2(writer.Bytes(), Spec.Structural<View>(obj.l, Spec.View), Spec.ConcatBytes(obj.data, Spec.Member), Spec.Structural<View>(obj.r, Spec.View));

    assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(obj, Spec.Member) by {
      hide *;
    }
    assert Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj) by { BracketedToObject(obj); }
    wr
  }

  lemma BracketedToArray(arr: jarray)
    ensures Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr)
  {
    var rItem := (d: jitem) requires d < arr => Spec.Item(d);
    assert Spec.Bracketed(arr, Spec.Item) == Spec.Bracketed(arr, rItem) by {
      assert SpecProperties.Bracketed_Morphism_Requires(arr, Spec.Item, rItem);
      SpecProperties.Bracketed_Morphism(arr, Spec.Item, rItem);
    }
    calc {
      Spec.Bracketed(arr, Spec.Item);
      Spec.Bracketed(arr, rItem);
      Spec.Array(arr);
    }
  }

  function Array(arr: jarray, writer: Writer) : (wr: Writer)
    decreases arr, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Array(arr)
  {
    var wr := StructuralView(arr.l, writer);
    StructuralViewEns(arr.l, writer);
    var wr := Items(arr, wr);
    var wr := StructuralView(arr.r, wr);
    Seq.LemmaConcatIsAssociative2(writer.Bytes(), Spec.Structural<View>(arr.l, Spec.View), Spec.ConcatBytes(arr.data, Spec.Item), Spec.Structural<View>(arr.r, Spec.View));

    assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(arr, Spec.Item);
    assert Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr) by { BracketedToArray(arr); }
    wr
  }

  function Members(obj: jobject, writer: Writer) : (wr: Writer)
    decreases obj, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
  {
    MembersSpec(obj, obj.data, writer)
  } by method {
    assume {:axiom} false; // BUG(https://github.com/dafny-lang/dafny/issues/2180)
    wr := MembersImpl(obj, writer);
  }

  function Items(arr: jarray, writer: Writer) : (wr: Writer)
    decreases arr, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
  {
    ItemsSpec(arr, arr.data, writer)
  } by method {
    assume {:axiom} false; // BUG(https://github.com/dafny-lang/dafny/issues/2180)
    wr := ItemsImpl(arr, writer);
  }

  ghost function MembersSpec(obj: jobject, members: seq<jmember>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |members| :: members[j] < obj
    decreases obj, 1, members
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Members.
    if members == [] then writer
    else
      var butLast, last := members[..|members|-1], members[|members|-1];
      assert members == butLast + [last];
      var wr := MembersSpec(obj, butLast, writer);
      var wr := Member(obj, last, wr);
      assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Member) + Spec.ConcatBytes([last], Spec.Member)) by {
        Seq.LemmaConcatIsAssociative(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Member), Spec.ConcatBytes([last], Spec.Member));
      }
      SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Member);
      wr
  } // No by method block here, because the loop invariant in the method version
  // needs to call MembersSpec and the termination checker gets confused by
  // that.  Instead, see Members above. // DISCUSS

  // DISCUSS: Is there a way to avoid passing the ghost `v` around while
  // maintaining the termination argument?  Maybe the lambda for elements will be enough?
  ghost predicate SequenceSpecRequiresHelper<T>(v: Value, items: seq<T>,
                                                spec: T -> bytes, impl: (Value, T, Writer) --> Writer,
                                                writer: Writer, item: T, wr: Writer)
    requires item in items
  {
    && impl.requires(v, item, wr)
    && impl(v, item, wr).Bytes() == wr.Bytes() + spec(item)
  }

  ghost predicate SequenceSpecRequires<T>(v: Value, items: seq<T>,
                                          spec: T -> bytes, impl: (Value, T, Writer) --> Writer,
                                          writer: Writer) {
    forall item, wr: Writer | item in items :: SequenceSpecRequiresHelper(v, items, spec, impl, writer, item, wr)
  }


  @IsolateAssertions
  ghost function SequenceSpec<T>(v: Value, items: seq<T>,
                                 spec: T -> bytes, impl: (Value, T, Writer) --> Writer,
                                 writer: Writer)
    : (wr: Writer)
    requires SequenceSpecRequires(v, items, spec, impl, writer)
    decreases v, 1, items
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      assert SequenceSpecRequires(v, items[..|items|-1], spec, impl, writer) by {
        assert forall item, wr: Writer {:trigger SequenceSpecRequiresHelper(v, items[..|items|-1], spec, impl, writer, item, wr)} | item in items[..|items|-1] :: SequenceSpecRequiresHelper(v, items[..|items|-1], spec, impl, writer, item, wr) by {
          forall item, wr: Writer {:trigger SequenceSpecRequiresHelper(v, items[..|items|-1], spec, impl, writer, item, wr)} | item in items[..|items|-1] ensures SequenceSpecRequiresHelper(v, items[..|items|-1], spec, impl, writer, item, wr) {
            assert item in items;
            assert SequenceSpecRequiresHelper(v, items, spec, impl, writer, item, wr);
          }
        }
      }
      var writer' := SequenceSpec(v, items[..|items|-1], spec, impl, writer);
      assert impl.requires(v, items[|items|-1], writer') by {
        assert SequenceSpecRequiresHelper(v, items, spec, impl, writer, items[|items|-1], writer') by {
          assert SequenceSpecRequires(v, items, spec, impl, writer);
          assert items[|items|-1] in items;
        }
      }
      var wr := impl(v, items[|items|-1], writer');
      assert wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec) by {
        calc {
          wr.Bytes();
          { assert wr == impl(v, items[|items|-1], writer'); }
          impl(v, items[|items|-1], writer').Bytes();
          { assert SequenceSpecRequires(v, items, spec, impl, writer); assert items[|items|-1] in items; assert SequenceSpecRequiresHelper(v, items, spec, impl, writer, items[|items|-1], writer'); }
          writer'.Bytes() + spec(items[|items|-1]);
          { assert writer' == SequenceSpec(v, items[..|items|-1], spec, impl, writer); }
          writer.Bytes() + Spec.ConcatBytes(items[..|items|-1], spec) + spec(items[|items|-1]);
          { assert spec(items[|items|-1]) == Spec.ConcatBytes([items[|items|-1]], spec); }
          writer.Bytes() + Spec.ConcatBytes(items[..|items|-1], spec) + Spec.ConcatBytes([items[|items|-1]], spec);
          { SpecProperties.ConcatBytes_Linear(items[..|items|-1], [items[|items|-1]], spec); }
          writer.Bytes() + Spec.ConcatBytes(items[..|items|-1] + [items[|items|-1]], spec);
          { assert items == items[..|items|-1] + [items[|items|-1]]; }
          writer.Bytes() + Spec.ConcatBytes(items, spec);
        }
      }
      wr
  } // No by method block here, because the loop invariant in the method version
  // needs to call `SequenceSpec` and the termination checker gets confused by
  // that.  Instead, see `Sequence`Items above. // DISCUSS


  ghost function ItemsSpec(arr: jarray, items: seq<jitem>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |items| :: items[j] < arr
    decreases arr, 1, items
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      var butLast, last := items[..|items|-1], items[|items|-1];
      assert items == butLast + [last];
      var wr := ItemsSpec(arr, butLast, writer);
      var wr := Item(arr, last, wr);
      assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Item) + Spec.ConcatBytes([last], Spec.Item)) by {
        Seq.LemmaConcatIsAssociative(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Item), Spec.ConcatBytes([last], Spec.Item));
      }
      SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Item);
      wr
  } // No by method block here, because the loop invariant in the method version
  // needs to call ItemsSpec and the termination checker gets confused by
  // that.  Instead, see Items above. // DISCUSS

  @IsolateAssertions
  method MembersImpl(obj: jobject, writer: Writer) returns (wr: Writer)
    decreases obj, 1
    ensures wr == MembersSpec(obj, obj.data, writer)
  {
    wr := writer;
    var members := obj.data;
    assert wr == MembersSpec(obj, members[..0], writer);
    for i := 0 to |members| // FIXME uint32
      invariant wr == MembersSpec(obj, members[..i], writer)
    {
      assert members[..i+1][..i] == members[..i] by {
        Seq.TakeLess(members, i, i + 1);
      }
      wr := Member(obj, members[i], wr);
    }
    assert members[..|members|] == members;
    assert wr == MembersSpec(obj, members, writer);
  }

  @IsolateAssertions
  method ItemsImpl(arr: jarray, writer: Writer) returns (wr: Writer)
    decreases arr, 1
    ensures wr == ItemsSpec(arr, arr.data, writer)
  {
    wr := writer;
    var items := arr.data;
    assert wr == ItemsSpec(arr, items[..0], writer);
    for i := 0 to |items| // FIXME uint32
      invariant wr == ItemsSpec(arr, items[..i], writer)
    {
      assert items[..i+1][..i] == items[..i] by {
        AboutList(items, i, i+1);
      }
      wr := Item(arr, items[i], wr);
    }
    assert items[..|items|] == items;
  }

  lemma AboutList<T>(xs: seq<T>, i: nat, j: nat)
    requires i < j <= |xs|
    ensures xs[..j][..i] == xs[..i]
  {}

  function Member(ghost obj: jobject, m: jmember, writer: Writer) : (wr: Writer)
    requires m < obj
    decreases obj, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
  {
    var wr := String(m.t.k, writer);
    var wr := StructuralView(m.t.colon, wr);
    var wr := Value(m.t.v, wr);
    assert wr.Bytes() == writer.Bytes() + (Spec.String(m.t.k) + Spec.Structural<View>(m.t.colon, Spec.View) + Spec.Value(m.t.v)) by {
      Seq.LemmaConcatIsAssociative2( writer.Bytes(), Spec.String(m.t.k), Spec.Structural<View>(m.t.colon, Spec.View), Spec.Value(m.t.v));
    }
    var wr := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
    assert wr.Bytes() == writer.Bytes() + Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix) by {
      if m.suffix.Empty? {
        EmptySequenceIsRightIdentity(Spec.KeyValue(m.t));
        Seq.LemmaConcatIsAssociative(writer.Bytes(), Spec.KeyValue(m.t), []);
      }
      else {
        assert Spec.StructuralView(m.suffix.t) == Spec.CommaSuffix(m.suffix);
      }
    }
    assert wr.Bytes() == writer.Bytes() + (Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix)) by {
      Seq.LemmaConcatIsAssociative(writer.Bytes(), Spec.KeyValue(m.t), Spec.CommaSuffix(m.suffix));
    }
    wr
  }

  function Item(ghost arr: jarray, m: jitem, writer: Writer) : (wr: Writer)
    requires m < arr
    decreases arr, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
  {
    var wr := Value(m.t, writer);
    var wr := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
    assert wr.Bytes() == writer.Bytes() + (Spec.Value(m.t) + Spec.CommaSuffix(m.suffix)) by {
      Seq.LemmaConcatIsAssociative(writer.Bytes(), Spec.Value(m.t), Spec.CommaSuffix(m.suffix));
    }
    wr
  }
}
