
const $$Language$Dafny: bool
uses {
axiom $$Language$Dafny;
}

type Ty;

type Bv0 = int;

const unique TBool: Ty
uses {
axiom Tag(TBool) == TagBool;
}

const unique TChar: Ty
uses {
axiom Tag(TChar) == TagChar;
}

const unique TInt: Ty
uses {
axiom Tag(TInt) == TagInt;
}

const unique TField: Ty
uses {
axiom Tag(TField) == TagField;
}

const unique TReal: Ty
uses {
axiom Tag(TReal) == TagReal;
}

const unique TORDINAL: Ty
uses {
axiom Tag(TORDINAL) == TagORDINAL;
}

revealed function TBitvector(int) : Ty;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

revealed function TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

revealed function TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

revealed function TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

revealed function TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

revealed function TMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

revealed function TIMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

revealed function Inv0_TBitvector(Ty) : int;

revealed function Inv0_TSet(Ty) : Ty;

revealed function Inv0_TISet(Ty) : Ty;

revealed function Inv0_TSeq(Ty) : Ty;

revealed function Inv0_TMultiSet(Ty) : Ty;

revealed function Inv0_TMap(Ty) : Ty;

revealed function Inv1_TMap(Ty) : Ty;

revealed function Inv0_TIMap(Ty) : Ty;

revealed function Inv1_TIMap(Ty) : Ty;

type TyTag;

revealed function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagField: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

type TyTagFamily;

revealed function TagFamily(Ty) : TyTagFamily;

revealed function {:identity} Lit<T>(x: T) : T
uses {
axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);
}

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

revealed function {:identity} LitInt(x: int) : int
uses {
axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);
}

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

revealed function {:identity} LitReal(x: real) : real
uses {
axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);
}

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

revealed function {:inline} char#IsChar(n: int) : bool
{
  (0 <= n && n < 55296) || (57344 <= n && n < 1114112)
}

type char;

revealed function char#FromInt(int) : char;

axiom (forall n: int :: 
  { char#FromInt(n) } 
  char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);

revealed function char#ToInt(char) : int;

axiom (forall ch: char :: 
  { char#ToInt(ch) } 
  char#FromInt(char#ToInt(ch)) == ch && char#IsChar(char#ToInt(ch)));

revealed function char#Plus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Plus(a, b) } 
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

revealed function char#Minus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Minus(a, b) } 
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

type ref;

const null: ref;

const locals: ref;

type FieldFamily;

const unique object_field: FieldFamily;

revealed function field_depth(f: Field) : int;

revealed function field_family(f: Field) : FieldFamily;

revealed function local_field(ff: FieldFamily, depth: int) : Field
uses {
axiom (forall ff: FieldFamily, depth: int :: 
  {:trigger local_field(ff, depth)} 
  field_depth(local_field(ff, depth)) == depth
     && field_family(local_field(ff, depth)) == ff);
}

type Box;

const $ArbitraryBoxValue: Box;

revealed function $Box<T>(T) : Box;

revealed function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: {:weight 3} { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall<T> x: Box :: { $Unbox(x): T } $Box($Unbox(x): T) == x);

revealed function $IsBox(Box, Ty) : bool;

revealed function $IsAllocBox(Box, Ty, Heap) : bool;

axiom (forall bx: Box :: 
  { $IsBox(bx, TInt) } 
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

axiom (forall bx: Box :: 
  { $IsBox(bx, TReal) } 
  $IsBox(bx, TReal)
     ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBool) } 
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box :: 
  { $IsBox(bx, TChar) } 
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(0)) } 
  $IsBox(bx, TBitvector(0))
     ==> $Box($Unbox(bx): Bv0) == bx && $Is($Unbox(bx): Bv0, TBitvector(0)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set) == bx && $Is($Unbox(bx): Set, TSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TISet(t)) } 
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet) == bx && $Is($Unbox(bx): ISet, TISet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TMultiSet(t)) } 
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet) == bx && $Is($Unbox(bx): MultiSet, TMultiSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSeq(t)) } 
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq) == bx && $Is($Unbox(bx): Seq, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TMap(s, t)) } 
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map) == bx && $Is($Unbox(bx): Map, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TIMap(s, t)) } 
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap) == bx && $Is($Unbox(bx): IMap, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap :: 
  { $IsAllocBox($Box(v), t, h) } 
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

revealed function $Is<T>(T, Ty) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: Field :: { $Is(v, TField) } $Is(v, TField));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Set, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0))
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: ISet, t0: Ty :: 
  { $Is(v, TISet(t0)) } 
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq, t0: Ty :: 
  { $Is(v, TSeq(t0)) } 
  $Is(v, TSeq(t0))
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     ==> $Is(Map#Domain(v), TSet(t0))
       && $Is(Map#Values(v), TSet(t1))
       && $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     ==> $Is(IMap#Domain(v), TISet(t0))
       && $Is(IMap#Values(v), TISet(t1))
       && $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

revealed function $IsAlloc<T>(T, Ty, Heap) : bool;

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL :: 
  { $IsAlloc(v, TORDINAL, h) } 
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Bv0, h: Heap :: 
  { $IsAlloc(v, TBitvector(0), h) } 
  $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TISet(t0), h) } 
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TMultiSet(t0), h) } 
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSeq(t0), h) } 
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TMap(t0, t1), h) } 
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TIMap(t0, t1), h) } 
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

revealed function $AlwaysAllocated(Ty) : bool;

axiom (forall ty: Ty :: 
  { $AlwaysAllocated(ty) } 
  $AlwaysAllocated(ty)
     ==> (forall h: Heap, v: Box :: 
      { $IsAllocBox(v, ty, h) } 
      $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));

revealed function $OlderTag(Heap) : bool;

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

revealed function Tclass._System.object?() : Ty
uses {
// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?
   && TagFamily(Tclass._System.object?()) == tytagFamily$object;
}

revealed function Tclass._System.Tuple2(Ty, Ty) : Ty;

revealed function dtype(ref) : Ty;

revealed function TypeTuple(a: ClassName, b: ClassName) : ClassName;

revealed function TypeTupleCar(ClassName) : ClassName;

revealed function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName :: 
  { TypeTuple(a, b) } 
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

type HandleType;

revealed function SetRef_to_SetBox(s: [ref]bool) : Set;

axiom (forall s: [ref]bool, bx: Box :: 
  { Set#IsMember(SetRef_to_SetBox(s), bx) } 
  Set#IsMember(SetRef_to_SetBox(s), bx) == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool :: 
  { SetRef_to_SetBox(s) } 
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

revealed function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

type DatatypeType;

type DtCtorId;

revealed function DatatypeCtorId(DatatypeType) : DtCtorId;

revealed function DtRank(DatatypeType) : int;

revealed function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

revealed function ORD#IsNat(ORDINAL) : bool;

revealed function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

revealed function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

revealed function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

revealed function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int :: 
  { ORD#FromNat(n) } 
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL :: 
  { ORD#Offset(o) } { ORD#IsNat(o) } 
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

revealed function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p) } 
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p)))
     && (ORD#Less(o, p) && ORD#IsNat(p) ==> ORD#IsNat(o)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, o) } 
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) } 
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

revealed function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#LessThanLimit(o, p) } 
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

revealed function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

revealed function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

type LayerType;

const $LZ: LayerType;

revealed function $LS(LayerType) : LayerType;

revealed function AsFuelBottom(LayerType) : LayerType;

revealed function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, ly) } 
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, $LS(ly)) } 
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

type Field;

revealed function FDim(Field) : int
uses {
axiom FDim(alloc) == 0;
}

revealed function IndexField(int) : Field;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

revealed function IndexField_Inverse(Field) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

axiom (forall f: Field :: 
  { IndexField_Inverse(f) } 
  IndexField(IndexField_Inverse(f)) == f);

revealed function MultiIndexField(Field, int) : Field;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

revealed function MultiIndexField_Inverse0(Field) : Field;

revealed function MultiIndexField_Inverse1(Field) : int;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

revealed function DeclType(Field) : ClassName;

type NameFamily;

revealed function DeclName(Field) : NameFamily
uses {
axiom DeclName(alloc) == allocName;
}

revealed function FieldOfDecl(ClassName, NameFamily) : Field;

axiom (forall cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field } 
  DeclType(FieldOfDecl(cl, nm): Field) == cl
     && DeclName(FieldOfDecl(cl, nm): Field) == nm);

revealed function _System.field.IsGhost(Field) : bool
uses {
axiom _System.field.IsGhost(alloc);
}

axiom (forall h: Heap, k: Heap :: 
  { $HeapSuccGhost(h, k) } 
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall o: ref, f: Field :: 
        { read(k, o, f) } 
        !_System.field.IsGhost(f) ==> read(h, o, f) == read(k, o, f)));

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty :: 
  { $HeapSucc(h, k), $IsAlloc(v, t, h) } 
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty :: 
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) } 
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field;

const unique allocName: NameFamily;

revealed function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: { _System.array.Length(o) } 0 <= _System.array.Length(o));

revealed function Int(x: real) : int
uses {
axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));
}

revealed function Real(x: int) : real
uses {
axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));
}

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

revealed function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref][Field]Box;

revealed function {:inline} read(H: Heap, r: ref, f: Field) : Box
{
  H[r][f]
}

revealed function {:inline} update(H: Heap, r: ref, f: Field, v: Box) : Heap
{
  H[r := H[r][f := v]]
}

revealed function $IsGoodHeap(Heap) : bool;

revealed function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap
uses {
axiom $IsGoodHeap($OneHeap);
}

revealed function $HeapSucc(Heap, Heap) : bool;

axiom (forall h: Heap, r: ref, f: Field, x: Box :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: 
      { read(k, o, alloc) } 
      $Unbox(read(h, o, alloc)) ==> $Unbox(read(k, o, alloc))));

revealed function $HeapSuccGhost(Heap, Heap) : bool;

type ReferrersHeap = [ref]Set;

revealed function {:inline} readReferrers(H: ReferrersHeap, r: ref) : Set
{
  H[r]
}

revealed function {:inline} updateReferrers(H: ReferrersHeap, r: ref, v: Set) : ReferrersHeap
{
  H[r := v]
}

var $ReferrersHeap: ReferrersHeap;

const $OneReferrersHeap: ReferrersHeap;

procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap, $ReferrersHeap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      $o == this || Set#IsMember(rds, $Box($o)) || Set#IsMember(nw, $Box($o))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap, $ReferrersHeap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      Set#IsMember(rds, $Box($o)) && !Set#IsMember(modi, $Box($o)) && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap, $ReferrersHeap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || Set#IsMember(modi, $Box($o))
         || Set#IsMember(nw, $Box($o)));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field) returns (s: Set);
  ensures (forall bx: Box :: 
    { Set#IsMember(s, bx) } 
    Set#IsMember(s, bx)
       <==> Set#IsMember($Unbox(read(newHeap, this, NW)): Set, bx)
         || (
          $Unbox(bx) != null
           && !$Unbox(read(prevHeap, $Unbox(bx): ref, alloc))
           && $Unbox(read(newHeap, $Unbox(bx): ref, alloc))));



type Set;

revealed function Set#Card(s: Set) : int;

axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));

revealed function Set#Empty() : Set;

revealed function Set#IsMember(s: Set, o: Box) : bool;

axiom (forall o: Box :: 
  { Set#IsMember(Set#Empty(), o) } 
  !Set#IsMember(Set#Empty(), o));

axiom (forall s: Set :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0
       ==> (exists x: Box :: { Set#IsMember(s, x) } Set#IsMember(s, x))));

revealed function Set#UnionOne(s: Set, o: Box) : Set;

axiom (forall a: Set, x: Box, o: Box :: 
  { Set#IsMember(Set#UnionOne(a, x), o) } 
  Set#IsMember(Set#UnionOne(a, x), o) <==> o == x || Set#IsMember(a, o));

axiom (forall a: Set, x: Box :: 
  { Set#UnionOne(a, x) } 
  Set#IsMember(Set#UnionOne(a, x), x));

axiom (forall a: Set, x: Box, y: Box :: 
  { Set#UnionOne(a, x), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#UnionOne(a, x), y));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  !Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

revealed function Set#Union(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Union(a, b), o) } 
  Set#IsMember(Set#Union(a, b), o) <==> Set#IsMember(a, o) || Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, b) } 
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

revealed function Set#Intersection(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Intersection(a, b), o) } 
  Set#IsMember(Set#Intersection(a, b), o)
     <==> Set#IsMember(a, o) && Set#IsMember(b, o));

axiom (forall a: Set, b: Set :: 
  { Set#Union(Set#Union(a, b), b) } 
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, Set#Union(a, b)) } 
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(Set#Intersection(a, b), b) } 
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(a, Set#Intersection(a, b)) } 
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

revealed function Set#Difference(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Difference(a, b), o) } 
  Set#IsMember(Set#Difference(a, b), o)
     <==> Set#IsMember(a, o) && !Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Difference(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> !Set#IsMember(Set#Difference(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

revealed function Set#Subset(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) ==> Set#IsMember(b, o)));

revealed function Set#Equal(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Equal(a, b) } 
  Set#Equal(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) <==> Set#IsMember(b, o)));

axiom (forall a: Set, b: Set :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

revealed function Set#Disjoint(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      !Set#IsMember(a, o) || !Set#IsMember(b, o)));

revealed function Set#FromBoogieMap([Box]bool) : Set;

axiom (forall m: [Box]bool, bx: Box :: 
  { Set#IsMember(Set#FromBoogieMap(m), bx) } 
  Set#IsMember(Set#FromBoogieMap(m), bx) == m[bx]);

type ISet = [Box]bool;

revealed function ISet#Empty() : ISet;

axiom (forall o: Box :: { ISet#Empty()[o] } !ISet#Empty()[o]);

revealed function ISet#FromSet(Set) : ISet;

axiom (forall s: Set, bx: Box :: 
  { ISet#FromSet(s)[bx] } 
  ISet#FromSet(s)[bx] == Set#IsMember(s, bx));

revealed function ISet#UnionOne(ISet, Box) : ISet;

axiom (forall a: ISet, x: Box, o: Box :: 
  { ISet#UnionOne(a, x)[o] } 
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall a: ISet, x: Box :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall a: ISet, x: Box, y: Box :: 
  { ISet#UnionOne(a, x), a[y] } 
  a[y] ==> ISet#UnionOne(a, x)[y]);

revealed function ISet#Union(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Union(a, b)[o] } 
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), a[y] } 
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), b[y] } 
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, b) } 
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

revealed function ISet#Intersection(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Intersection(a, b)[o] } 
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(ISet#Union(a, b), b) } 
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, ISet#Union(a, b)) } 
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(ISet#Intersection(a, b), b) } 
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(a, ISet#Intersection(a, b)) } 
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

revealed function ISet#Difference(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Difference(a, b)[o] } 
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Difference(a, b), b[y] } 
  b[y] ==> !ISet#Difference(a, b)[y]);

revealed function ISet#Subset(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Subset(a, b) } 
  ISet#Subset(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] ==> b[o]));

revealed function ISet#Equal(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall a: ISet, b: ISet :: { ISet#Equal(a, b) } ISet#Equal(a, b) ==> a == b);

revealed function ISet#Disjoint(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Disjoint(a, b) } 
  ISet#Disjoint(a, b) <==> (forall o: Box :: { a[o] } { b[o] } !a[o] || !b[o]));

revealed function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int :: 
  { Math#min(a, b) } 
  Math#min(a, b) == a || Math#min(a, b) == b);

revealed function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet;

revealed function MultiSet#Multiplicity(m: MultiSet, o: Box) : int;

revealed function MultiSet#UpdateMultiplicity(m: MultiSet, o: Box, n: int) : MultiSet;

axiom (forall m: MultiSet, o: Box, n: int, p: Box :: 
  { MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) } 
  0 <= n
     ==> (o == p ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) == n)
       && (o != p
         ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p)
           == MultiSet#Multiplicity(m, p)));

revealed function $IsGoodMultiSet(ms: MultiSet) : bool;

axiom (forall ms: MultiSet :: 
  { $IsGoodMultiSet(ms) } 
  $IsGoodMultiSet(ms)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(ms, bx) } 
      0 <= MultiSet#Multiplicity(ms, bx)
         && MultiSet#Multiplicity(ms, bx) <= MultiSet#Card(ms)));

revealed function MultiSet#Card(m: MultiSet) : int;

axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall s: MultiSet, x: Box, n: int :: 
  { MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n)) } 
  0 <= n
     ==> MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n))
       == MultiSet#Card(s) - MultiSet#Multiplicity(s, x) + n);

revealed function MultiSet#Empty() : MultiSet;

axiom (forall o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Empty(), o) } 
  MultiSet#Multiplicity(MultiSet#Empty(), o) == 0);

axiom (forall s: MultiSet :: 
  { MultiSet#Card(s) } 
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0
       ==> (exists x: Box :: 
        { MultiSet#Multiplicity(s, x) } 
        0 < MultiSet#Multiplicity(s, x))));

revealed function MultiSet#Singleton(o: Box) : MultiSet;

axiom (forall r: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Singleton(r), o) } 
  (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 1 <==> r == o)
     && (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 0 <==> r != o));

axiom (forall r: Box :: 
  { MultiSet#Singleton(r) } 
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

revealed function MultiSet#UnionOne(m: MultiSet, o: Box) : MultiSet;

axiom (forall a: MultiSet, x: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o) } 
  0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o)
     <==> o == x || 0 < MultiSet#Multiplicity(a, o));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#UnionOne(a, x) } 
  MultiSet#Multiplicity(MultiSet#UnionOne(a, x), x)
     == MultiSet#Multiplicity(a, x) + 1);

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  0 < MultiSet#Multiplicity(a, y)
     ==> 0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  x != y
     ==> MultiSet#Multiplicity(a, y) == MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#Card(MultiSet#UnionOne(a, x)) } 
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

revealed function MultiSet#Union(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Union(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Union(a, b), o)
     == MultiSet#Multiplicity(a, o) + MultiSet#Multiplicity(b, o));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Union(a, b)) } 
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

revealed function MultiSet#Intersection(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Intersection(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Intersection(a, b), o)
     == Math#min(MultiSet#Multiplicity(a, o), MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) } 
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) } 
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

revealed function MultiSet#Difference(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Difference(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Difference(a, b), o)
     == Math#clip(MultiSet#Multiplicity(a, o) - MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet, y: Box :: 
  { MultiSet#Difference(a, b), MultiSet#Multiplicity(b, y), MultiSet#Multiplicity(a, y) } 
  MultiSet#Multiplicity(a, y) <= MultiSet#Multiplicity(b, y)
     ==> MultiSet#Multiplicity(MultiSet#Difference(a, b), y) == 0);

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Difference(a, b)) } 
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

revealed function MultiSet#Subset(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Subset(a, b) } 
  MultiSet#Subset(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) <= MultiSet#Multiplicity(b, o)));

revealed function MultiSet#Equal(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) ==> a == b);

revealed function MultiSet#Disjoint(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Disjoint(a, b) } 
  MultiSet#Disjoint(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == 0 || MultiSet#Multiplicity(b, o) == 0));

revealed function MultiSet#FromSet(s: Set) : MultiSet;

axiom (forall s: Set, a: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSet(s), a) } 
  (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 0 <==> !Set#IsMember(s, a))
     && (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 1 <==> Set#IsMember(s, a)));

axiom (forall s: Set :: 
  { MultiSet#Card(MultiSet#FromSet(s)) } 
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

revealed function MultiSet#FromSeq(s: Seq) : MultiSet
uses {
axiom MultiSet#FromSeq(Seq#Empty()) == MultiSet#Empty();
}

axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall s: Seq :: 
  { MultiSet#Card(MultiSet#FromSeq(s)) } 
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall s: Seq, v: Box :: 
  { MultiSet#FromSeq(Seq#Build(s, v)) } 
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall a: Seq, b: Seq :: 
  { MultiSet#FromSeq(Seq#Append(a, b)) } 
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall s: Seq, i: int, v: Box, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x) } 
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x)
       == MultiSet#Multiplicity(MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), 
          MultiSet#Singleton(v)), 
        x));

axiom (forall s: Seq, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(s), x) } 
  (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#Multiplicity(MultiSet#FromSeq(s), x));

type Seq;

revealed function Seq#Length(s: Seq) : int;

axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));

revealed function Seq#Empty() : Seq
uses {
axiom Seq#Length(Seq#Empty()) == 0;
}

axiom (forall s: Seq :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

revealed function Seq#Build(s: Seq, val: Box) : Seq;

revealed function Seq#Build_inv0(s: Seq) : Seq;

revealed function Seq#Build_inv1(s: Seq) : Box;

axiom (forall s: Seq, val: Box :: 
  { Seq#Build(s, val) } 
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall s: Seq, v: Box :: 
  { Seq#Build(s, v) } 
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Index(Seq#Build(s, v), i) } 
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Length(Seq#Append(s0, s1)) } 
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

revealed function Seq#Index(s: Seq, i: int) : Box;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#Index(Seq#Append(s0, s1), n) } 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

revealed function Seq#Update(s: Seq, i: int, val: Box) : Seq;

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Length(Seq#Update(s, i, v)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Index(Seq#Update(s, i, v), n) } 
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

revealed function Seq#Append(s0: Seq, s1: Seq) : Seq;

revealed function Seq#Contains(s: Seq, val: Box) : bool;

axiom (forall s: Seq, x: Box :: 
  { Seq#Contains(s, x) } 
  Seq#Contains(s, x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall x: Box :: 
  { Seq#Contains(Seq#Empty(), x) } 
  !Seq#Contains(Seq#Empty(), x));

axiom (forall s0: Seq, s1: Seq, x: Box :: 
  { Seq#Contains(Seq#Append(s0, s1), x) } 
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall s: Seq, v: Box, x: Box :: 
  { Seq#Contains(Seq#Build(s, v), x) } 
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Take(s, n), x) } 
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Drop(s, n), x) } 
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

revealed function Seq#Equal(s0: Seq, s1: Seq) : bool;

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Equal(s0, s1) } 
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int :: 
        { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall a: Seq, b: Seq :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

revealed function Seq#SameUntil(s0: Seq, s1: Seq, n: int) : bool;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#SameUntil(s0, s1, n) } 
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int :: 
      { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

revealed function Seq#Take(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Take(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) } 
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

revealed function Seq#Drop(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Drop(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Drop(s, n), j) } 
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall s: Seq, n: int, k: int :: 
  {:weight 11} { Seq#Index(s, k), Seq#Drop(s, n) } 
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall s: Seq, t: Seq, n: int :: 
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) } 
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall s: Seq, v: Box, n: int :: 
  { Seq#Drop(Seq#Build(s, v), n) } 
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

axiom (forall s: Seq, n: int :: { Seq#Drop(s, n) } n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall s: Seq, n: int :: 
  { Seq#Take(s, n) } 
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall s: Seq, m: int, n: int :: 
  { Seq#Drop(Seq#Drop(s, m), n) } 
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

axiom (forall s: Seq, bx: Box, t: Ty :: 
  { $Is(Seq#Build(s, bx), TSeq(t)) } 
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

revealed function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType :: 
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq) } 
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int :: 
  { Seq#Index(Seq#Create(ty, heap, len, init), i) } 
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, ty, heap, init, $Box(i)));

revealed function Seq#FromArray(h: Heap, a: ref) : Seq;

axiom (forall h: Heap, a: ref :: 
  { Seq#Length(Seq#FromArray(h, a)) } 
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref :: 
  { Seq#FromArray(h, a) } 
  (forall i: int :: 
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq, i) } 
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref :: 
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) } 
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref :: 
  { Seq#FromArray(update(h, a, IndexField(i), v), a) } 
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall h: Heap, a: ref, n0: int, n1: int :: 
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) } 
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field)));

revealed function Seq#Rank(Seq) : int;

axiom (forall s: Seq, i: int :: 
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) } 
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Drop(s, i)) } 
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Take(s, i)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int, j: int :: 
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) } 
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

type Map;

revealed function Map#Domain(Map) : Set;

revealed function Map#Elements(Map) : [Box]Box;

revealed function Map#Card(Map) : int;

axiom (forall m: Map :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall m: Map :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall m: Map :: 
  { Map#Domain(m) } 
  m == Map#Empty() || (exists k: Box :: Set#IsMember(Map#Domain(m), k)));

axiom (forall m: Map :: 
  { Map#Values(m) } 
  m == Map#Empty() || (exists v: Box :: Set#IsMember(Map#Values(m), v)));

axiom (forall m: Map :: 
  { Map#Items(m) } 
  m == Map#Empty()
     || (exists k: Box, v: Box :: 
      Set#IsMember(Map#Items(m), $Box(#_System._tuple#2._#Make2(k, v)))));

axiom (forall m: Map :: 
  { Set#Card(Map#Domain(m)) } { Map#Card(m) } 
  Set#Card(Map#Domain(m)) == Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Values(m)) } { Map#Card(m) } 
  Set#Card(Map#Values(m)) <= Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Items(m)) } { Map#Card(m) } 
  Set#Card(Map#Items(m)) == Map#Card(m));

revealed function Map#Values(Map) : Set;

axiom (forall m: Map, v: Box :: 
  { Set#IsMember(Map#Values(m), v) } 
  Set#IsMember(Map#Values(m), v)
     == (exists u: Box :: 
      { Set#IsMember(Map#Domain(m), u) } { Map#Elements(m)[u] } 
      Set#IsMember(Map#Domain(m), u) && v == Map#Elements(m)[u]));

revealed function Map#Items(Map) : Set;

revealed function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

revealed function _System.Tuple2._0(DatatypeType) : Box;

revealed function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map, item: Box :: 
  { Set#IsMember(Map#Items(m), item) } 
  Set#IsMember(Map#Items(m), item)
     <==> Set#IsMember(Map#Domain(m), _System.Tuple2._0($Unbox(item)))
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function Map#Empty() : Map;

axiom (forall u: Box :: 
  { Set#IsMember(Map#Domain(Map#Empty(): Map), u) } 
  !Set#IsMember(Map#Domain(Map#Empty(): Map), u));

revealed function Map#Glue(Set, [Box]Box, Ty) : Map;

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Domain(Map#Glue(a, b, t)) } 
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Elements(Map#Glue(a, b, t)) } 
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall a: Set, b: [Box]Box, t0: Ty, t1: Ty :: 
  { Map#Glue(a, b, TMap(t0, t1)) } 
  (forall bx: Box :: Set#IsMember(a, bx) ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

revealed function Map#Build(Map, Box, Box) : Map;

axiom (forall m: Map, u: Box, u': Box, v: Box :: 
  { Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') } 
    { Map#Elements(Map#Build(m, u, v))[u'] } 
  (u' == u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
           == Set#IsMember(Map#Domain(m), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  Set#IsMember(Map#Domain(m), u) ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  !Set#IsMember(Map#Domain(m), u)
     ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

revealed function Map#Merge(Map, Map) : Map;

axiom (forall m: Map, n: Map :: 
  { Map#Domain(Map#Merge(m, n)) } 
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

axiom (forall m: Map, n: Map, u: Box :: 
  { Map#Elements(Map#Merge(m, n))[u] } 
  Set#IsMember(Map#Domain(Map#Merge(m, n)), u)
     ==> (!Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u])
       && (Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

revealed function Map#Subtract(Map, Set) : Map;

axiom (forall m: Map, s: Set :: 
  { Map#Domain(Map#Subtract(m, s)) } 
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

axiom (forall m: Map, s: Set, u: Box :: 
  { Map#Elements(Map#Subtract(m, s))[u] } 
  Set#IsMember(Map#Domain(Map#Subtract(m, s)), u)
     ==> Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

revealed function Map#Equal(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m')
     <==> (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) == Set#IsMember(Map#Domain(m'), u))
       && (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall m: Map, m': Map :: { Map#Equal(m, m') } Map#Equal(m, m') ==> m == m');

revealed function Map#Disjoint(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Disjoint(m, m') } 
  Map#Disjoint(m, m')
     <==> (forall o: Box :: 
      { Set#IsMember(Map#Domain(m), o) } { Set#IsMember(Map#Domain(m'), o) } 
      !Set#IsMember(Map#Domain(m), o) || !Set#IsMember(Map#Domain(m'), o)));

type IMap;

revealed function IMap#Domain(IMap) : ISet;

revealed function IMap#Elements(IMap) : [Box]Box;

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() || (exists k: Box :: IMap#Domain(m)[k]));

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() || (exists v: Box :: IMap#Values(m)[v]));

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty()
     || (exists k: Box, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

revealed function IMap#Values(IMap) : ISet;

axiom (forall m: IMap, v: Box :: 
  { IMap#Values(m)[v] } 
  IMap#Values(m)[v]
     == (exists u: Box :: 
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] } 
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

revealed function IMap#Items(IMap) : ISet;

axiom (forall m: IMap, item: Box :: 
  { IMap#Items(m)[item] } 
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function IMap#Empty() : IMap;

axiom (forall u: Box :: 
  { IMap#Domain(IMap#Empty(): IMap)[u] } 
  !IMap#Domain(IMap#Empty(): IMap)[u]);

revealed function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Domain(IMap#Glue(a, b, t)) } 
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Elements(IMap#Glue(a, b, t)) } 
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall a: [Box]bool, b: [Box]Box, t0: Ty, t1: Ty :: 
  { IMap#Glue(a, b, TIMap(t0, t1)) } 
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(IMap#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

revealed function IMap#Build(IMap, Box, Box) : IMap;

axiom (forall m: IMap, u: Box, u': Box, v: Box :: 
  { IMap#Domain(IMap#Build(m, u, v))[u'] } 
    { IMap#Elements(IMap#Build(m, u, v))[u'] } 
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

revealed function IMap#Equal(IMap, IMap) : bool;

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m')
     <==> (forall u: Box :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: Box :: 
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m') ==> m == m');

revealed function IMap#Merge(IMap, IMap) : IMap;

axiom (forall m: IMap, n: IMap :: 
  { IMap#Domain(IMap#Merge(m, n)) } 
  IMap#Domain(IMap#Merge(m, n)) == ISet#Union(IMap#Domain(m), IMap#Domain(n)));

axiom (forall m: IMap, n: IMap, u: Box :: 
  { IMap#Elements(IMap#Merge(m, n))[u] } 
  IMap#Domain(IMap#Merge(m, n))[u]
     ==> (!IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u])
       && (IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

revealed function IMap#Subtract(IMap, Set) : IMap;

axiom (forall m: IMap, s: Set :: 
  { IMap#Domain(IMap#Subtract(m, s)) } 
  IMap#Domain(IMap#Subtract(m, s))
     == ISet#Difference(IMap#Domain(m), ISet#FromSet(s)));

axiom (forall m: IMap, s: Set, u: Box :: 
  { IMap#Elements(IMap#Subtract(m, s))[u] } 
  IMap#Domain(IMap#Subtract(m, s))[u]
     ==> IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

revealed function INTERNAL_add_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_add_boogie(x, y): int } 
  INTERNAL_add_boogie(x, y): int == x + y);
}

revealed function INTERNAL_sub_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_sub_boogie(x, y): int } 
  INTERNAL_sub_boogie(x, y): int == x - y);
}

revealed function INTERNAL_mul_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mul_boogie(x, y): int } 
  INTERNAL_mul_boogie(x, y): int == x * y);
}

revealed function INTERNAL_div_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_div_boogie(x, y): int } 
  INTERNAL_div_boogie(x, y): int == x div y);
}

revealed function INTERNAL_mod_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mod_boogie(x, y): int } 
  INTERNAL_mod_boogie(x, y): int == x mod y);
}

revealed function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool } 
  INTERNAL_lt_boogie(x, y): bool == (x < y));
}

revealed function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool } 
  INTERNAL_le_boogie(x, y): bool == (x <= y));
}

revealed function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool } 
  INTERNAL_gt_boogie(x, y): bool == (x > y));
}

revealed function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool } 
  INTERNAL_ge_boogie(x, y): bool == (x >= y));
}

revealed function Mul(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);
}

revealed function Div(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Div(x, y): int } Div(x, y): int == x div y);
}

revealed function Mod(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mod(x, y): int } Mod(x, y): int == x mod y);
}

revealed function Add(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Add(x, y): int } Add(x, y): int == x + y);
}

revealed function Sub(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Sub(x, y): int } Sub(x, y): int == x - y);
}

function Tclass._System.nat() : Ty
uses {
// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat
   && TagFamily(Tclass._System.nat()) == tytagFamily$nat;
}

const unique Tagclass._System.nat: TyTag;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.nat()) } 
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// $Is axiom for subset type _System.nat
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// $IsAlloc axiom for subset type _System.nat
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._System.nat(), $h) } 
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// $Is axiom for trait object
axiom (forall $o: ref :: 
  { $Is($o, Tclass._System.object?()) } 
  $Is($o, Tclass._System.object?()));

// $IsAlloc axiom for trait object
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.object?(), $h) } 
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

function implements$_System.object(ty: Ty) : bool;

function Tclass._System.object() : Ty
uses {
// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object
   && TagFamily(Tclass._System.object()) == tytagFamily$object;
}

const unique Tagclass._System.object: TyTag;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object()) } 
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// $Is axiom for non-null type _System.object
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } { $Is(c#0, Tclass._System.object?()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// $IsAlloc axiom for non-null type _System.object
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.object(), $h) } 
  $IsAlloc(c#0, Tclass._System.object(), $h)
     <==> $IsAlloc(c#0, Tclass._System.object?(), $h));

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

const unique Tagclass._System.array?: TyTag;

// Tclass._System.array? Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tag(Tclass._System.array?(_System.array$arg)) == Tagclass._System.array?
     && TagFamily(Tclass._System.array?(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array?_0(Ty) : Ty;

// Tclass._System.array? injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tclass._System.array?_0(Tclass._System.array?(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array?
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array?(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array?(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array?(_System.array$arg)));

// array.: Type axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), _System.array$arg));

// array.: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), _System.array$arg, $h));

// $Is axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(_System.array$arg)) } 
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

// $IsAlloc axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h) } 
  $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

// array.Length: Type axiom
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { _System.array.Length($o), Tclass._System.array?(_System.array$arg) } 
  $o != null && dtype($o) == Tclass._System.array?(_System.array$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array.Length($o), $Unbox(read($h, $o, alloc)): bool, Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array
     && TagFamily(Tclass._System.array(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array_0(Ty) : Ty;

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// $Is axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array(_System.array$arg)) } 
    { $Is(c#0, Tclass._System.array?(_System.array$arg)) } 
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// $IsAlloc axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array?(_System.array$arg), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1
     && TagFamily(Tclass._System.___hFunc1(#$T0, #$R)) == tytagFamily$_#Func1);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set;

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box, 
    bx: Box :: 
  { Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx) } 
  Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx)
     == Set#IsMember(rd[heap, bx0], bx));

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1 
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Reads1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Requires1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t1) } { $IsBox(bx, u1) } 
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box :: 
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) } 
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref :: 
            { Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r)) } 
            r != null && Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r))
               ==> $Unbox(read(h, r, alloc)): bool))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == Tagclass._System.___hPartialFunc1
     && TagFamily(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == tytagFamily$_#PartialFunc1);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// $Is axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set)));

// $IsAlloc axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1
     && TagFamily(Tclass._System.___hTotalFunc1(#$T0, #$R)) == tytagFamily$_#TotalFunc1);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $Is axioms for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && 
      (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && ((forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
         ==> (forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)))
     ==> $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc0(Ty) : Ty;

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0
     && TagFamily(Tclass._System.___hFunc0(#$R)) == tytagFamily$_#Func0);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Apply0(t0, heap, Handle0(h, r, rd)) } 
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Requires0(t0, heap, Handle0(h, r, rd)) } 
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set, bx: Box :: 
  { Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx) } 
  Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx)
     == Set#IsMember(rd[heap], bx));

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0 
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) } 
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) } 
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap :: 
      { Apply0(t0, h, f) } 
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t0) } { $IsBox(bx, u0) } 
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref :: 
          { Set#IsMember(Reads0(t0, h, f), $Box(r)) } 
          r != null && Set#IsMember(Reads0(t0, h, f), $Box(r))
             ==> $Unbox(read(h, r, alloc)): bool)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==> 
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0
     && TagFamily(Tclass._System.___hPartialFunc0(#$R)) == tytagFamily$_#PartialFunc0);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// $Is axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set));

// $IsAlloc axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0
     && TagFamily(Tclass._System.___hTotalFunc0(#$R)) == tytagFamily$_#TotalFunc0);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// $Is axioms for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && 
      Requires0#canCall(#$R, $OneHeap, f#0)
       && Requires0(#$R, $OneHeap, f#0));

axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && (Requires0#canCall(#$R, $OneHeap, f#0) ==> Requires0(#$R, $OneHeap, f#0))
     ==> $Is(f#0, Tclass._System.___hTotalFunc0(#$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

const unique ##_System._tuple#2._#Make2: DtCtorId
uses {
// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#0#0#0, a#0#1#0))
     == ##_System._tuple#2._#Make2);
}

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#1#0#0, a#1#1#0)));

const unique Tagclass._System.Tuple2: TyTag;

// Tclass._System.Tuple2 Tag
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tag(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == Tagclass._System.Tuple2
     && TagFamily(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == tytagFamily$_tuple#2);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 0
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T0);

function Tclass._System.Tuple2_1(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T1);

// Box/unbox axiom for Tclass._System.Tuple2
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)));

// Constructor $Is
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#2#0#0: Box, a#2#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#2#0#0, _System._tuple#2$T0) && $IsBox(a#2#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#2#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#2#1#0, _System._tuple#2$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T0: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T1: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T1: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T0: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h));

// Constructor literal
axiom (forall a#3#0#0: Box, a#3#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0))
     == Lit(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0)));

// Constructor injectivity
axiom (forall a#4#0#0: Box, a#4#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#4#0#0, a#4#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#4#0#0, a#4#1#0)) == a#4#0#0);

// Inductive rank
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)) } 
  BoxRank(a#5#0#0) < DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)));

// Constructor injectivity
axiom (forall a#6#0#0: Box, a#6#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: Box, a#7#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)) } 
  BoxRank(a#7#1#0) < DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)));

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple2(d) } 
  $IsA#_System.Tuple2(d) ==> _System.Tuple2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d), $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> _System.Tuple2.___hMake2_q(d));

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#2._#Make2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b)
     <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
       && _System.Tuple2._1(a) == _System.Tuple2._1(b));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());
// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());
}

const unique ##_System._tuple#0._#Make0: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
}

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.Tuple0() : Ty
uses {
// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0
   && TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;
}

const unique Tagclass._System.Tuple0: TyTag;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple0()) } 
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Datatype $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(d, Tclass._System.Tuple0(), $h) } 
  $IsGoodHeap($h) && $Is(d, Tclass._System.Tuple0())
     ==> $IsAlloc(d, Tclass._System.Tuple0(), $h));

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple0(d) } 
  $IsA#_System.Tuple0(d) ==> _System.Tuple0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d), $Is(d, Tclass._System.Tuple0()) } 
  $Is(d, Tclass._System.Tuple0()) ==> _System.Tuple0.___hMake0_q(d));

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#0._#Make0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

const unique class._module.__default: ClassName;

procedure {:verboseName "ReferrersLocal (well-formedness)"} CheckWellFormed$$_module.__default.ReferrersLocal(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ReferrersLocal (call)"} Call$$_module.__default.ReferrersLocal(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ReferrersLocal (correctness)"} Impl$$_module.__default.ReferrersLocal(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.SimpleObject?() : Ty
uses {
// Tclass._module.SimpleObject? Tag
axiom Tag(Tclass._module.SimpleObject?()) == Tagclass._module.SimpleObject?
   && TagFamily(Tclass._module.SimpleObject?()) == tytagFamily$SimpleObject;
}

const unique Tagclass._module.SimpleObject?: TyTag;

// Box/unbox axiom for Tclass._module.SimpleObject?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SimpleObject?()) } 
  $IsBox(bx, Tclass._module.SimpleObject?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SimpleObject?()));

const unique _module.__default.ReferrersLocal.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersLocal.t, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ReferrersLocal.t, depth)));

const unique _module.__default.ReferrersLocal.alias__t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersLocal.alias__t, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ReferrersLocal.alias__t, depth)));

const unique _module.__default.ReferrersLocal.u: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersLocal.u, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ReferrersLocal.u, depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ReferrersLocal (correctness)"} Impl$$_module.__default.ReferrersLocal(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var t#0: ref
     where $Is(t#0, Tclass._module.SimpleObject?())
       && $IsAlloc(t#0, Tclass._module.SimpleObject?(), $Heap);
  var $nw: ref;
  var alias_t#0: ref
     where $Is(alias_t#0, Tclass._module.SimpleObject?())
       && $IsAlloc(alias_t#0, Tclass._module.SimpleObject?(), $Heap);
  var $Heap_at_0: Heap;
  var $ReferrersHeap_at_0: ReferrersHeap;
  var newtype$check#0: ref;
  var u#0: ref
     where $Is(u#0, Tclass._System.array(Tclass._module.SimpleObject?()))
       && $IsAlloc(u#0, Tclass._System.array(Tclass._module.SimpleObject?()), $Heap);
  var $lambdaHeap#0: Heap;
  var $lambdaReferrersHeap#0: ReferrersHeap;
  var i#0: int;
  var $_Frame#l0: [ref,Field]bool;
  var lambdaResult#0: ref;
  var newtype$check#1: ref;

    // AddMethodImpl: ReferrersLocal, Impl$$_module.__default.ReferrersLocal
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(10,24): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(11,9)
    assume true;
    if (t#0 != null)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#Difference(readReferrers($ReferrersHeap, t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))))));
    }

    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._module.SimpleObject?());
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    t#0 := $nw;
    if (t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth))))));
    }

    assume {:captureState "referrers.dfy(11,27)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(12,3)
    assume true;
    assert {:id "id1"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(13,15)
    assume true;
    if (alias_t#0 != null)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, alias_t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_t#0, 
          Set#Difference(readReferrers($ReferrersHeap, alias_t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth)))))));
    }

    assume true;
    alias_t#0 := t#0;
    if (alias_t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, alias_t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, alias_t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth))))));
    }

    assume {:captureState "referrers.dfy(13,18)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(14,3)
    assume true;
    assert {:id "id3"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth))))));
    $Heap_at_0 := $Heap;
    $ReferrersHeap_at_0 := $ReferrersHeap;

  after_0:
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(16,5)
    assume true;
    if (t#0 != null)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#Difference(readReferrers($ReferrersHeap, t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))))));
    }

    newtype$check#0 := null;
    assume true;
    t#0 := null;
    if (t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth))))));
    }

    assume {:captureState "referrers.dfy(16,11)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(17,3)
    assume true;
    assert {:id "id5"} Set#Equal(readReferrers($ReferrersHeap, alias_t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(18,3)
    assume true;
    assert {:id "id6"} Set#Equal(readReferrers($ReferrersHeap_at_0, alias_t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocal.alias__t, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(21,9)
    assume true;
    if (u#0 != null)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, u#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.u, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          u#0, 
          Set#Difference(readReferrers($ReferrersHeap, u#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.u, depth)))))));
    }

    assert {:id "id7"} 0 <= LitInt(1);
    // Begin Comprehension WF check
    if (*)
    {
        havoc $lambdaHeap#0;
        assume $IsGoodHeap($lambdaHeap#0);
        assume $Heap == $lambdaHeap#0 || $HeapSucc($Heap, $lambdaHeap#0);
        havoc i#0;
        if (true)
        {
            $_Frame#l0 := (lambda $o: ref, $f: Field :: 
              $o != null && $Unbox(read($lambdaHeap#0, $o, alloc)): bool ==> false);
            newtype$check#1 := null;
            assume true;
            assume {:id "id8"} lambdaResult#0 == null;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, Tclass._module.SimpleObject?());
        }

        assume false;
    }

    // End Comprehension WF check
    assume true;
    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._System.array?(Tclass._module.SimpleObject?()));
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    assume _System.array.Length($nw) == LitInt(1);
    assert {:id "id9"} {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(1)
         ==> Requires1(TInt, 
          Tclass._module.SimpleObject?(), 
          $Heap, 
          Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                Handle1((lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $Box(null)), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $IsBox($l#1#i#0, TInt)), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                    SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0)));
    assume (forall arrayinit#0#i0#0: int :: 
      { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(1)
         ==> Requires1(TInt, 
            Tclass._module.SimpleObject?(), 
            $Heap, 
            Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
                  Handle1((lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: $Box(null)), 
                    (lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: $IsBox($l#2#i#0, TInt)), 
                    (lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: 
                      SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
                $LS($LZ))), 
            $Box(arrayinit#0#i0#0))
           && $Unbox(read($Heap, $nw, IndexField(arrayinit#0#i0#0))): ref
             == $Unbox(Apply1(TInt, 
                Tclass._module.SimpleObject?(), 
                $Heap, 
                Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                      Handle1((lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $Box(null)), 
                        (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $IsBox($l#1#i#0, TInt)), 
                        (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                          SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
                    $LS($LZ))), 
                $Box(arrayinit#0#i0#0))): ref);
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    u#0 := $nw;
    if (u#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, u#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.u, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          u#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, u#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.u, depth))))));
    }

    assume {:captureState "referrers.dfy(21,42)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(22,3)
    assume true;
    assert {:id "id11"} Set#Equal(readReferrers($ReferrersHeap, u#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersLocal.u, depth))))));
}



function Tclass._module.SimpleObject() : Ty
uses {
// Tclass._module.SimpleObject Tag
axiom Tag(Tclass._module.SimpleObject()) == Tagclass._module.SimpleObject
   && TagFamily(Tclass._module.SimpleObject()) == tytagFamily$SimpleObject;
}

const unique Tagclass._module.SimpleObject: TyTag;

// Box/unbox axiom for Tclass._module.SimpleObject
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SimpleObject()) } 
  $IsBox(bx, Tclass._module.SimpleObject())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SimpleObject()));

const unique _module.__default.ReferrersMethodCall.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersMethodCall.t, depth) } 
  _System.field.IsGhost(local_field(_module.__default.ReferrersMethodCall.t, depth)));

procedure {:verboseName "ReferrersMethodCall (well-formedness)"} CheckWellFormed$$_module.__default.ReferrersMethodCall(depth: int, 
    t#0: ref
       where $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap));
  free requires Set#IsMember(readReferrers($ReferrersHeap, t#0), 
    $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersMethodCall.t, depth)))));
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ReferrersMethodCall (call)"} Call$$_module.__default.ReferrersMethodCall(depth: int, 
    t#0: ref
       where $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap));
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ReferrersMethodCall (correctness)"} Impl$$_module.__default.ReferrersMethodCall(depth: int, 
    t#0: ref
       where $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap))
   returns ($_reverifyPost: bool);
  free requires Set#IsMember(readReferrers($ReferrersHeap, t#0), 
      $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersMethodCall.t, depth)))));
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ReferrersMethodCall (correctness)"} Impl$$_module.__default.ReferrersMethodCall(depth: int, t#0: ref) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;

    // AddMethodImpl: ReferrersMethodCall, Impl$$_module.__default.ReferrersMethodCall
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(26,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(27,3)
    assume true;
    assert {:id "id12"} Set#IsMember(readReferrers($ReferrersHeap, t#0), 
      $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersMethodCall.t, depth)))));
}



const unique _module.__default.EnsuresReferrersUnchanged.t2: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.EnsuresReferrersUnchanged.t2, depth) } 
  _System.field.IsGhost(local_field(_module.__default.EnsuresReferrersUnchanged.t2, depth)));

procedure {:verboseName "EnsuresReferrersUnchanged (well-formedness)"} CheckWellFormed$$_module.__default.EnsuresReferrersUnchanged(depth: int, 
    t2#0: ref
       where $Is(t2#0, Tclass._module.SimpleObject())
         && $IsAlloc(t2#0, Tclass._module.SimpleObject(), $Heap));
  free requires Set#IsMember(readReferrers($ReferrersHeap, t2#0), 
    $Box(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t2, depth)))));
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "EnsuresReferrersUnchanged (call)"} Call$$_module.__default.EnsuresReferrersUnchanged(depth: int, 
    t2#0: ref
       where $Is(t2#0, Tclass._module.SimpleObject())
         && $IsAlloc(t2#0, Tclass._module.SimpleObject(), $Heap));
  modifies $Heap, $ReferrersHeap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id14"} Set#Equal(readReferrers(old($ReferrersHeap), t2#0), readReferrers($ReferrersHeap, t2#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "EnsuresReferrersUnchanged (correctness)"} Impl$$_module.__default.EnsuresReferrersUnchanged(depth: int, 
    t2#0: ref
       where $Is(t2#0, Tclass._module.SimpleObject())
         && $IsAlloc(t2#0, Tclass._module.SimpleObject(), $Heap))
   returns ($_reverifyPost: bool);
  free requires Set#IsMember(readReferrers($ReferrersHeap, t2#0), 
    $Box(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t2, depth)))));
  modifies $Heap, $ReferrersHeap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id15"} Set#Equal(readReferrers(old($ReferrersHeap), t2#0), readReferrers($ReferrersHeap, t2#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique _module.__default.EnsuresReferrersUnchanged.t__local: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "EnsuresReferrersUnchanged (correctness)"} Impl$$_module.__default.EnsuresReferrersUnchanged(depth: int, t2#0: ref) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t_local#0: bool;
  var t_local#0: ref
     where defass#t_local#0
       ==> $Is(t_local#0, Tclass._module.SimpleObject())
         && $IsAlloc(t_local#0, Tclass._module.SimpleObject(), $Heap);

    // AddMethodImpl: EnsuresReferrersUnchanged, Impl$$_module.__default.EnsuresReferrersUnchanged
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(34,0): initial state"} true;
    $_reverifyPost := false;
    defass#t_local#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(35,15)
    assume true;
    if (t_local#0 != null && defass#t_local#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t_local#0),
          $Box(#_System._tuple#2._#Make2($Box(locals),
              $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t_local#0, 
          Set#Difference(readReferrers($ReferrersHeap, t_local#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth)))))));
    }

    assume true;
    t_local#0 := t2#0;
    if (t_local#0 != null)
    {
      assume !Set#IsMember(readReferrers($ReferrersHeap, t_local#0),
        $Box(#_System._tuple#2._#Make2($Box(locals),
          $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth)))));
      $ReferrersHeap := updateReferrers($ReferrersHeap,
        t_local#0,
        Set#UnionOne(readReferrers($ReferrersHeap, t_local#0),
          $Box(#_System._tuple#2._#Make2($Box(locals),
          $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth))))));
    }
    
    defass#t_local#0 := true;
    assume {:captureState "referrers.dfy(35,19)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(36,3)
    assert {:id "id17"} defass#t_local#0;
    assume true;
    assert {:id "id18"} Set#Equal(readReferrers(old($ReferrersHeap), t2#0), 
      readReferrers(old($ReferrersHeap), t_local#0));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(37,3)
    assume true;
    assert {:id "id19"} Set#Equal(readReferrers($ReferrersHeap, t2#0), 
      Set#Union(readReferrers(old($ReferrersHeap), t2#0), 
        Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth)))))));
    // ----- return statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(38,3)
    $ReferrersHeap := updateReferrers($ReferrersHeap, t_local#0, Set#Difference(readReferrers($ReferrersHeap, t_local#0),
      Set#UnionOne(Set#Empty(),
      $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth))))
    )));
    assert Set#Equal(readReferrers(old($ReferrersHeap), t2#0), readReferrers($ReferrersHeap, t2#0));
    return;
}



procedure {:verboseName "CallReferrersMethodCall (well-formedness)"} CheckWellFormed$$_module.__default.CallReferrersMethodCall(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "CallReferrersMethodCall (call)"} Call$$_module.__default.CallReferrersMethodCall(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "CallReferrersMethodCall (correctness)"} Impl$$_module.__default.CallReferrersMethodCall(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique _module.__default.CallReferrersMethodCall.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.CallReferrersMethodCall.t, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.CallReferrersMethodCall.t, depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "CallReferrersMethodCall (correctness)"} Impl$$_module.__default.CallReferrersMethodCall(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap);
  var $nw: ref;
  var t2##0: ref;

    // AddMethodImpl: CallReferrersMethodCall, Impl$$_module.__default.CallReferrersMethodCall
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(41,33): initial state"} true;
    $_reverifyPost := false;
    defass#t#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(42,9)
    assume true;
    if (t#0 != null && defass#t#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#Difference(readReferrers($ReferrersHeap, t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth)))))));
    }

    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._module.SimpleObject?());
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    t#0 := $nw;
    if (t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth))))));
    }

    defass#t#0 := true;
    assume {:captureState "referrers.dfy(42,27)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(43,3)
    assert {:id "id21"} defass#t#0;
    assume true;
    assert {:id "id22"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth))))));
    // ----- call statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(44,28)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id23"} defass#t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    t2##0 := t#0;
    call {:id "id24"} Call$$_module.__default.EnsuresReferrersUnchanged(depth + 1, t2##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "referrers.dfy(44,30)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(45,3)
    assert {:id "id25"} defass#t#0;
    assume true;
    assert {:id "id26"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.CallReferrersMethodCall.t, depth))))));
}



procedure {:verboseName "GhostReferrersLocals (well-formedness)"} CheckWellFormed$$_module.__default.GhostReferrersLocals(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "GhostReferrersLocals (call)"} Call$$_module.__default.GhostReferrersLocals(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSuccGhost(old($Heap), $Heap);



procedure {:verboseName "GhostReferrersLocals (correctness)"} Impl$$_module.__default.GhostReferrersLocals(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSuccGhost(old($Heap), $Heap);



const unique _module.__default.GhostReferrersLocals.alias__tracked: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth) } 
  _System.field.IsGhost(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth)));

const unique _module.__default.GhostReferrersLocals.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.GhostReferrersLocals.t, depth) } 
  _System.field.IsGhost(local_field(_module.__default.GhostReferrersLocals.t, depth)));

const unique _module.__default.GhostReferrersLocals.alias__untracked: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth) } 
  _System.field.IsGhost(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "GhostReferrersLocals (correctness)"} Impl$$_module.__default.GhostReferrersLocals(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap);
  var $nw: ref;
  var defass#alias_untracked#0: bool;
  var alias_untracked#0: ref
     where defass#alias_untracked#0
       ==> $Is(alias_untracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_untracked#0, Tclass._module.SimpleObject(), $Heap);
  var defass#alias_tracked#0: bool;
  var alias_tracked#0: ref
     where defass#alias_tracked#0
       ==> $Is(alias_tracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_tracked#0, Tclass._module.SimpleObject(), $Heap);

    // AddMethodImpl: GhostReferrersLocals, Impl$$_module.__default.GhostReferrersLocals
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(50,36): initial state"} true;
    $_reverifyPost := false;
    defass#t#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(51,15)
    assume true;
    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._module.SimpleObject?());
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    t#0 := $nw;
    defass#t#0 := true;
    assume {:captureState "referrers.dfy(51,33)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(52,3)
    assert {:id "id28"} defass#t#0;
    assume true;
    assert {:id "id29"} Set#Equal(readReferrers($ReferrersHeap, t#0), Set#Empty(): Set);
    defass#alias_untracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(53,29)
    assume true;
    assert {:id "id30"} defass#t#0;
    assume true;
    alias_untracked#0 := t#0;
    defass#alias_untracked#0 := true;
    assume {:captureState "referrers.dfy(53,32)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(54,3)
    assert {:id "id32"} defass#t#0;
    assume true;
    assert {:id "id33"} Set#Equal(readReferrers($ReferrersHeap, t#0), Set#Empty(): Set);
    defass#alias_tracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(55,39)
    assume true;
    if (alias_tracked#0 != null && defass#alias_tracked#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#Difference(readReferrers($ReferrersHeap, alias_tracked#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth)))))));
    }

    assert {:id "id34"} defass#t#0;
    assume true;
    alias_tracked#0 := t#0;
    if (alias_tracked#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, alias_tracked#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))))));
    }

    defass#alias_tracked#0 := true;
    assume {:captureState "referrers.dfy(55,42)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(56,3)
    assert {:id "id36"} defass#t#0;
    assume true;
    assert {:id "id37"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set,
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(58,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.GhostReferrersLocals.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.GhostReferrersLocals.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.GhostReferrersLocals.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.GhostReferrersLocals.t, depth))));
    assert {:id "id38"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.GhostReferrersLocals.t, depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(59,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth))));
    assert {:id "id39"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.GhostReferrersLocals.alias__untracked, depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(60,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))));
    assert {:id "id40"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.GhostReferrersLocals.alias__tracked, depth))))): Field);
}



procedure {:verboseName "ReferrersLocalWithGhostAliases (well-formedness)"} CheckWellFormed$$_module.__default.ReferrersLocalWithGhostAliases(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ReferrersLocalWithGhostAliases (call)"} Call$$_module.__default.ReferrersLocalWithGhostAliases(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ReferrersLocalWithGhostAliases (correctness)"} Impl$$_module.__default.ReferrersLocalWithGhostAliases(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique _module.__default.ReferrersLocalWithGhostAliases.t: FieldFamily;

axiom (forall depth: int ::
  { local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth) }
  !_System.field.IsGhost(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth)));

const unique _module.__default.ReferrersLocalWithGhostAliases.alias__tracked: FieldFamily;

axiom (forall depth: int ::
    { local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth) }
    _System.field.IsGhost(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth)));

const unique _module.__default.ReferrersLocalWithGhostAliases.alias__untracked: FieldFamily;

axiom (forall depth: int ::
    { local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth) }
    _System.field.IsGhost(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ReferrersLocalWithGhostAliases (correctness)"} Impl$$_module.__default.ReferrersLocalWithGhostAliases(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap);
  var $nw: ref;
  var defass#alias_untracked#0: bool;
  var alias_untracked#0: ref
     where defass#alias_untracked#0
       ==> $Is(alias_untracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_untracked#0, Tclass._module.SimpleObject(), $Heap);
  var defass#alias_tracked#0: bool;
  var alias_tracked#0: ref
     where defass#alias_tracked#0
       ==> $Is(alias_tracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_tracked#0, Tclass._module.SimpleObject(), $Heap);

    // AddMethodImpl: ReferrersLocalWithGhostAliases, Impl$$_module.__default.ReferrersLocalWithGhostAliases
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(63,40): initial state"} true;
    $_reverifyPost := false;
    defass#t#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(64,9)
    assume true;
    if (t#0 != null && defass#t#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#Difference(readReferrers($ReferrersHeap, t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth)))))));
    }

    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._module.SimpleObject?());
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    t#0 := $nw;
    if (t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))))));
    }
  
    defass#t#0 := true;
    assume {:captureState "referrers.dfy(64,27)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(65,3)
    assert {:id "id42"} defass#t#0;
    assume true;
    assert {:id "id43"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))))));
    defass#alias_untracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(66,29)
    assume true;
    assert {:id "id44"} defass#t#0;
    assume true;
    alias_untracked#0 := t#0;
    defass#alias_untracked#0 := true;
    assume {:captureState "referrers.dfy(66,32)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(67,3)
    assert {:id "id46"} defass#t#0;
    assume true;
    assert {:id "id47"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))))));
    defass#alias_tracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(68,39)
    assume true;
    if (alias_tracked#0 != null && defass#alias_tracked#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#Difference(readReferrers($ReferrersHeap, alias_tracked#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth)))))));
    }

    assert {:id "id48"} defass#t#0;
    assume true;
    alias_tracked#0 := t#0;
    if (alias_tracked#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, alias_tracked#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))))));
    }

    defass#alias_tracked#0 := true;
    assume {:captureState "referrers.dfy(68,42)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(69,3)
    assert {:id "id50"} defass#t#0;
    assume true;
    assert {:id "id51"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(71,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))));
    assert {:id "id52"} !_System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.t, depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(72,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth))));
    assert {:id "id53"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__untracked, depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(73,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))));
    assert {:id "id54"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersLocalWithGhostAliases.alias__tracked, depth))))): Field);
}



procedure {:verboseName "ReferrersOnGhostConstructedInstanceInCompiledContext (well-formedness)"} CheckWellFormed$$_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ReferrersOnGhostConstructedInstanceInCompiledContext (call)"} Call$$_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ReferrersOnGhostConstructedInstanceInCompiledContext (correctness)"} Impl$$_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique _module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
      depth) } 
  _System.field.IsGhost(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
      depth)));

const unique _module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth) } 
  _System.field.IsGhost(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth)));

const unique _module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
      depth) } 
  _System.field.IsGhost(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
      depth)));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ReferrersOnGhostConstructedInstanceInCompiledContext (correctness)"} Impl$$_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.SimpleObject())
         && $IsAlloc(t#0, Tclass._module.SimpleObject(), $Heap);
  var $nw: ref;
  var defass#alias_untracked#0: bool;
  var alias_untracked#0: ref
     where defass#alias_untracked#0
       ==> $Is(alias_untracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_untracked#0, Tclass._module.SimpleObject(), $Heap);
  var defass#alias_tracked#0: bool;
  var alias_tracked#0: ref
     where defass#alias_tracked#0
       ==> $Is(alias_tracked#0, Tclass._module.SimpleObject())
         && $IsAlloc(alias_tracked#0, Tclass._module.SimpleObject(), $Heap);

    // AddMethodImpl: ReferrersOnGhostConstructedInstanceInCompiledContext, Impl$$_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(77,62): initial state"} true;
    $_reverifyPost := false;
    defass#t#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(78,15)
    assume true;
    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._module.SimpleObject?());
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    $Heap := update($Heap, $nw, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    t#0 := $nw;
    defass#t#0 := true;
    assume {:captureState "referrers.dfy(78,33)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(79,3)
    assert {:id "id56"} defass#t#0;
    assume true;
    assert {:id "id57"} Set#Equal(readReferrers($ReferrersHeap, t#0), Set#Empty(): Set);
    defass#alias_untracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(80,29)
    assume true;
    assert {:id "id58"} defass#t#0;
    assume true;
    alias_untracked#0 := t#0;
    defass#alias_untracked#0 := true;
    assume {:captureState "referrers.dfy(80,32)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(81,3)
    assert {:id "id60"} defass#t#0;
    assume true;
    assert {:id "id61"} Set#Equal(readReferrers($ReferrersHeap, t#0), Set#Empty(): Set);
    defass#alias_tracked#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(82,39)
    assume true;
    if (alias_tracked#0 != null && defass#alias_tracked#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                  depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#Difference(readReferrers($ReferrersHeap, alias_tracked#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), 
                  $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                      depth)))))));
    }

    assert {:id "id62"} defass#t#0;
    assume true;
    alias_tracked#0 := t#0;
    if (alias_tracked#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, alias_tracked#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), 
              $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                  depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          alias_tracked#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, alias_tracked#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), 
                $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                    depth))))));
    }

    defass#alias_tracked#0 := true;
    assume {:captureState "referrers.dfy(82,42)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(83,3)
    assert {:id "id64"} defass#t#0;
    assume true;
    assert {:id "id65"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                depth))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(85,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth))));
    assert {:id "id66"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.t, depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(86,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
            depth))));
    assert {:id "id67"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__untracked, 
                depth))))): Field);
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(87,3)
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
            depth))));
    assume _System.Tuple2.___hMake2_q(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
            depth))));
    assert {:id "id68"} _System.field.IsGhost($Unbox(_System.Tuple2._1(#_System._tuple#2._#Make2($Box(locals), 
            $Box(local_field(_module.__default.ReferrersOnGhostConstructedInstanceInCompiledContext.alias__tracked, 
                depth))))): Field);
}



procedure {:verboseName "CouldFree (well-formedness)"} CheckWellFormed$$_module.__default.CouldFree(t#0: ref
       where $Is(t#0, Tclass._System.object())
         && $IsAlloc(t#0, Tclass._System.object(), $Heap), 
    compiledMemRef#0: DatatypeType
       where $Is(compiledMemRef#0, Tclass._System.Tuple2(Tclass._System.object(), TField))
         && $IsAlloc(compiledMemRef#0, Tclass._System.Tuple2(Tclass._System.object(), TField), $Heap)
         && $IsA#_System.Tuple2(compiledMemRef#0));
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "CouldFree (call)"} Call$$_module.__default.CouldFree(t#0: ref
       where $Is(t#0, Tclass._System.object())
         && $IsAlloc(t#0, Tclass._System.object(), $Heap), 
    compiledMemRef#0: DatatypeType
       where $Is(compiledMemRef#0, Tclass._System.Tuple2(Tclass._System.object(), TField))
         && $IsAlloc(compiledMemRef#0, Tclass._System.Tuple2(Tclass._System.object(), TField), $Heap)
         && $IsA#_System.Tuple2(compiledMemRef#0));
  // user-defined preconditions
  free requires {:always_assume} (forall r#1: DatatypeType :: 
    { _System.Tuple2._1(r#1) } 
      { Set#IsMember(readReferrers($ReferrersHeap, t#0), $Box(r#1)) } 
    $Is(r#1, Tclass._System.Tuple2(Tclass._System.object(), TField))
       ==> 
      Set#IsMember(readReferrers($ReferrersHeap, t#0), $Box(r#1))
       ==> _System.Tuple2.___hMake2_q(r#1)
         && (!_System.field.IsGhost($Unbox(_System.Tuple2._1(r#1)): Field)
           ==> $IsA#_System.Tuple2(r#1) && $IsA#_System.Tuple2(compiledMemRef#0)));
  requires {:id "id75"} (forall r#1: DatatypeType :: 
    { _System.Tuple2._1(r#1) } 
      { Set#IsMember(readReferrers($ReferrersHeap, t#0), $Box(r#1)) } 
    $Is(r#1, Tclass._System.Tuple2(Tclass._System.object(), TField))
         && Set#IsMember(readReferrers($ReferrersHeap, t#0), $Box(r#1))
       ==> 
      !_System.field.IsGhost($Unbox(_System.Tuple2._1(r#1)): Field)
       ==> _System.Tuple2#Equal(r#1, compiledMemRef#0));
  modifies $Heap, $ReferrersHeap;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures old($ReferrersHeap) == $ReferrersHeap;



procedure {:verboseName "ObjectFields (well-formedness)"} CheckWellFormed$$_module.__default.ObjectFields(depth: int);
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ObjectFields (call)"} Call$$_module.__default.ObjectFields(depth: int);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ObjectFields (correctness)"} Impl$$_module.__default.ObjectFields(depth: int) returns ($_reverifyPost: bool);
  modifies $Heap, $ReferrersHeap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.ChainingObject() : Ty
uses {
// Tclass._module.ChainingObject Tag
axiom Tag(Tclass._module.ChainingObject()) == Tagclass._module.ChainingObject
   && TagFamily(Tclass._module.ChainingObject()) == tytagFamily$ChainingObject;
}

const unique Tagclass._module.ChainingObject: TyTag;

// Box/unbox axiom for Tclass._module.ChainingObject
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ChainingObject()) } 
  $IsBox(bx, Tclass._module.ChainingObject())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ChainingObject()));

const unique _module.__default.ObjectFields.t: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ObjectFields.t, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ObjectFields.t, depth)));

const unique _module.__default.ObjectFields.u: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ObjectFields.u, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ObjectFields.u, depth)));

const unique _module.__default.ObjectFields.a: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.__default.ObjectFields.a, depth) } 
  !_System.field.IsGhost(local_field(_module.__default.ObjectFields.a, depth)));

const unique _module.ChainingObject.__ctor.this: FieldFamily;

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ObjectFields (correctness)"} Impl$$_module.__default.ObjectFields(depth: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#t#0: bool;
  var t#0: ref
     where defass#t#0
       ==> $Is(t#0, Tclass._module.ChainingObject())
         && $IsAlloc(t#0, Tclass._module.ChainingObject(), $Heap);
  var $nw: ref;
  var chained_test##0: ref;
  var newtype$check#0: ref;
  var $rhs#0: ref;
  var $rhs#1: ref;
  var $rhs#2: ref;
  var newtype$check#1: ref;
  var $rhs#3: ref;
  var newtype$check#2: ref;
  var $rhs#4: ref;
  var $rhs#5: ref;
  var newtype$check#3: ref;
  var $rhs#6: ref;
  var t##0: ref;
  var compiledMemRef##0: DatatypeType;
  var defass#u#0: bool;
  var u#0: ref
     where defass#u#0
       ==> $Is(u#0, Tclass._module.ChainingObject())
         && $IsAlloc(u#0, Tclass._module.ChainingObject(), $Heap);
  var chained_test##1: ref;
  var $rhs#7: ref;
  var $rhs#8: ref;
  var $Heap_at_0: Heap;
  var $ReferrersHeap_at_0: ReferrersHeap;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(Tclass._module.ChainingObject()))
       && $IsAlloc(a#0, Tclass._System.array(Tclass._module.ChainingObject()), $Heap);
  var $lambdaHeap#0: Heap;
  var $lambdaReferrersHeap#0: ReferrersHeap;
  var i#0: int;
  var $_Frame#l0: [ref,Field]bool;
  var lambdaResult#0: ref;
  var $oldRhs#0: ref;
  var $AllocationReferrersHeap#0: ReferrersHeap;
  var r#0: DatatypeType;

    // AddMethodImpl: ObjectFields, Impl$$_module.__default.ObjectFields
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(115,22): initial state"} true;
    $_reverifyPost := false;
    defass#t#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(116,9)
    assume true;
    if (t#0 != null && defass#t#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#Difference(readReferrers($ReferrersHeap, t#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth)))))));
    }

    // ----- init call statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(116,12)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#0 := null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    chained_test##0 := null;
    $AllocationReferrersHeap#0 := $ReferrersHeap;
    call {:id "id76"} $nw := Call$$_module.ChainingObject.__ctor(depth + 1, chained_test##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "referrers.dfy(116,35)"} true;
    assume readReferrers($AllocationReferrersHeap#0, $nw) == Set#Empty();
    t#0 := $nw;
    if (t#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, t#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          t#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, t#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))));
    }

    defass#t#0 := true;
    assume {:captureState "referrers.dfy(116,35)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(117,3)
    assert {:id "id78"} defass#t#0;
    assume true;
    assert {:id "id79"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(118,7)
    assert {:id "id80"} defass#t#0;
    assert {:id "id81"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id82"} $_ModifiesFrame[t#0, _module.ChainingObject.x];
    assert {:id "id83"} defass#t#0;
    assume true;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.x)): ref;
    $rhs#0 := t#0;
    $Heap := update($Heap, t#0, _module.ChainingObject.x, $Box($rhs#0));
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x))))
      ));
    }
    if ($rhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#0, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#0),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x)))
      ));
    }

    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(118,10)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(119,3)
    assert {:id "id86"} defass#t#0;
    assert {:id "id87"} defass#t#0;
    assume true;
    assert {:id "id88"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x)))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(120,7)
    assert {:id "id89"} defass#t#0;
    assert {:id "id90"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id91"} $_ModifiesFrame[t#0, _module.ChainingObject.y];
    assert {:id "id92"} defass#t#0;
    assume true;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.y)): ref;
    $rhs#1 := t#0;
    $Heap := update($Heap, t#0, _module.ChainingObject.y, $Box($rhs#1));
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y))))
      ));
    }
    if ($rhs#1 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#1, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#1),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y)))
      ));
    }
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(120,10)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(121,3)
    assert {:id "id95"} defass#t#0;
    assert {:id "id96"} defass#t#0;
    assert {:id "id97"} defass#t#0;
    assume true;
    assert {:id "id98"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
          $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x)))), 
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y)))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(122,7)
    assert {:id "id99"} defass#t#0;
    assert {:id "id100"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id101"} $_ModifiesFrame[t#0, _module.ChainingObject.x];
    newtype$check#1 := null;
    assume true;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.x)): ref;
    $rhs#2 := null;
    $Heap := update($Heap, t#0, _module.ChainingObject.x, $Box($rhs#2));
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x))))
      ));
    }
    if ($rhs#2 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#2, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#2),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.x)))
      ));
    }
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(122,13)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(123,3)
    assert {:id "id104"} defass#t#0;
    assert {:id "id105"} defass#t#0;
    assume true;
    assert {:id "id106"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y)))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(124,7)
    assert {:id "id107"} defass#t#0;
    assert {:id "id108"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id109"} $_ModifiesFrame[t#0, _module.ChainingObject.y];
    newtype$check#2 := null;
    assume true;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.y)): ref;
    $rhs#3 := null;
    $Heap := update($Heap, t#0, _module.ChainingObject.y, $Box($rhs#3));
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y))))
      ));
    }
    if ($rhs#3 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#3, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#3),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.y)))
      ));
    }
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(124,13)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(125,3)
    assert {:id "id112"} defass#t#0;
    assume true;
    assert {:id "id113"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(126,14)
    assert {:id "id114"} defass#t#0;
    assert {:id "id115"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id116"} $_ModifiesFrame[t#0, _module.ChainingObject.tracking];
    assert {:id "id117"} defass#t#0;
    assume true;
    $rhs#4 := t#0;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.tracking)): ref;
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.tracking))))
      ));
    }
    if ($rhs#4 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#4, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#4),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.tracking)))
      ));
    }
    $Heap := update($Heap, t#0, _module.ChainingObject.tracking, $Box($rhs#4));
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(126,17)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(127,3)
    assert {:id "id120"} defass#t#0;
    assert {:id "id121"} defass#t#0;
    assume true;
    assert {:id "id122"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.tracking)))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(128,14)
    assert {:id "id123"} defass#t#0;
    assert {:id "id124"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id125"} $_ModifiesFrame[t#0, _module.ChainingObject.tracking];
    newtype$check#3 := null;
    assume true;
    $rhs#5 := null;
    $oldRhs#0 := $Unbox(read($Heap, t#0, _module.ChainingObject.tracking)) :ref;
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.tracking))))
      ));
    }
    if ($rhs#5 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#5, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#5),
        $Box(#_System._tuple#2._#Make2($Box(t#0), $Box(_module.ChainingObject.tracking)))
      ));
    }
    $Heap := update($Heap, t#0, _module.ChainingObject.tracking, $Box($rhs#5));
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(128,20)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(129,3)
    assert {:id "id128"} defass#t#0;
    assume true;
    assert {:id "id129"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(130,17)
    assert {:id "id130"} defass#t#0;
    assert {:id "id131"} t#0 != null;
    assume true;
    assume true;
    assert {:id "id132"} $_ModifiesFrame[t#0, _module.ChainingObject.nontracking];
    assert {:id "id133"} defass#t#0;
    assume true;
    $rhs#6 := t#0;
    $Heap := update($Heap, t#0, _module.ChainingObject.nontracking, $Box($rhs#6));
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(130,20)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(131,3)
    assert {:id "id136"} defass#t#0;
    assume true;
    assert {:id "id137"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))));
    // ----- call statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(132,12)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id138"} defass#t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    compiledMemRef##0 := #_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth)));
    call {:id "id139"} Call$$_module.__default.CouldFree(t##0, compiledMemRef##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "referrers.dfy(132,24)"} true;
    defass#u#0 := false;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(134,9)
    assume true;
    if (u#0 != null && defass#u#0)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, u#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          u#0, 
          Set#Difference(readReferrers($ReferrersHeap, u#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth)))))));
    }

    // ----- init call statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(134,12)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id140"} defass#t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    chained_test##1 := t#0;
    $AllocationReferrersHeap#0 := $ReferrersHeap;
    call {:id "id141"} $nw := Call$$_module.ChainingObject.__ctor(depth + 1, chained_test##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "referrers.dfy(134,32)"} true;
    assume readReferrers($AllocationReferrersHeap#0, $nw) == Set#Empty();
    assert readReferrers($ReferrersHeap, $nw) == Set#Empty();
    u#0 := $nw;
    if (u#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, u#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          u#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, u#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth))))));
    }

    defass#u#0 := true;
    assume {:captureState "referrers.dfy(134,32)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(135,3)
    assert {:id "id143"} defass#u#0;
    assume true;
    assert {:id "id144"} Set#Equal(readReferrers($ReferrersHeap, u#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(136,3)
    assert {:id "id145"} defass#t#0;
    assert {:id "id146"} defass#u#0;
    assume true;
    assert {:id "id147"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.tail)))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(137,7)
    assert {:id "id148"} defass#u#0;
    assert {:id "id149"} u#0 != null;
    assume true;
    assume true;
    assert {:id "id150"} $_ModifiesFrame[u#0, _module.ChainingObject.x];
    assert {:id "id151"} defass#t#0;
    assume true;
    $rhs#7 := t#0;
    $oldRhs#0 := $Unbox(read($Heap, u#0, _module.ChainingObject.x)): ref;
    if ($rhs#7 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#7, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#7),
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x)))
      ));
    }
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0),
        Set#UnionOne(Set#Empty(): Set, $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x))))
      ));
    }
    $Heap := update($Heap, u#0, _module.ChainingObject.x, $Box($rhs#7));
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(137,10)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(138,3)
    assert {:id "id154"} defass#t#0;
    assert {:id "id155"} defass#u#0;
    assert {:id "id156"} defass#u#0;
    assume true;
    assert {:id "id157"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
          $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.tail)))), 
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x)))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(139,3)
    assert {:id "id158"} defass#u#0;
    assume true;
    assert {:id "id159"} Set#Equal(readReferrers($ReferrersHeap, u#0), 
      Set#UnionOne(Set#Empty(): Set, 
        $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth))))));
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(140,7)
    assert {:id "id160"} defass#u#0;
    assert {:id "id161"} u#0 != null;
    assume true;
    assume true;
    assert {:id "id162"} $_ModifiesFrame[u#0, _module.ChainingObject.x];
    assert {:id "id163"} defass#u#0;
    assume true;
    $rhs#8 := u#0;
    $oldRhs#0 := $Unbox(read($Heap, u#0, _module.ChainingObject.x)): ref;
    if ($rhs#8 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $rhs#8, Set#UnionOne(readReferrers($ReferrersHeap, $rhs#8),
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x)))
      ));
    }
    if ($oldRhs#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, $oldRhs#0, Set#Difference(readReferrers($ReferrersHeap, $oldRhs#0),
        Set#UnionOne(Set#Empty(): Set, $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x))))
      ));
    }
    $Heap := update($Heap, u#0, _module.ChainingObject.x, $Box($rhs#8));
    assume $IsGoodHeap($Heap);
    assume {:captureState "referrers.dfy(140,10)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(141,3)
    assert {:id "id166"} defass#t#0;
    assert {:id "id167"} defass#u#0;
    assume true;
    assert {:id "id168"} Set#Equal(readReferrers($ReferrersHeap, t#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.t, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.tail)))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(142,3)
    assert {:id "id169"} defass#u#0;
    assert {:id "id170"} defass#u#0;
    assume true;
    assert {:id "id171"} Set#Equal(readReferrers($ReferrersHeap, u#0), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.u, depth))))), 
        $Box(#_System._tuple#2._#Make2($Box(u#0), $Box(_module.ChainingObject.x)))));
    $Heap_at_0 := $Heap;
    $ReferrersHeap_at_0 := $ReferrersHeap;

  after_0:
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(146,9)
    assume true;
    if (a#0 != null)
    {
        assume Set#IsMember(readReferrers($ReferrersHeap, a#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.a, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          a#0, 
          Set#Difference(readReferrers($ReferrersHeap, a#0), 
            Set#UnionOne(Set#Empty(): Set, 
              $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.a, depth)))))));
    }

    assert {:id "id172"} 0 <= LitInt(3);
    // Begin Comprehension WF check
    if (*)
    {
        havoc $lambdaHeap#0;
        assume $IsGoodHeap($lambdaHeap#0);
        assume $Heap == $lambdaHeap#0 || $HeapSucc($Heap, $lambdaHeap#0);
        havoc i#0;
        if (true)
        {
            $_Frame#l0 := (lambda $o: ref, $f: Field :: 
              $o != null && $Unbox(read($lambdaHeap#0, $o, alloc)): bool ==> false);
            if (i#0 == LitInt(0))
            {
                assert {:id "id173"} defass#t#0;
                assume true;
                assume {:id "id174"} lambdaResult#0 == t#0;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, Tclass._module.ChainingObject());
            }
            else
            {
                assert {:id "id175"} defass#u#0;
                assume true;
                assume {:id "id176"} lambdaResult#0 == u#0;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, Tclass._module.ChainingObject());
            }
        }

        assume false;
    }

    // End Comprehension WF check
    assume true;
    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._System.array?(Tclass._module.ChainingObject()));
    assume !$Unbox(read($Heap, $nw, alloc)): bool;
    assume readReferrers($ReferrersHeap, $nw) == Set#Empty(): Set;
    assume _System.array.Length($nw) == LitInt(3);
    assert {:id "id177"} {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(3)
         ==> Requires1(TInt, 
          Tclass._module.ChainingObject(), 
          $Heap, 
          Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                Handle1((lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                    $Box((if $Unbox($l#1#i#0): int == LitInt(0) then t#0 else u#0))), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $IsBox($l#1#i#0, TInt)), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                    SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0)));
    assume (forall arrayinit#0#i0#0: int :: 
      { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(3)
         ==> Requires1(TInt, 
            Tclass._module.ChainingObject(), 
            $Heap, 
            Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
                  Handle1((lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: 
                      $Box((if $Unbox($l#2#i#0): int == LitInt(0) then t#0 else u#0))), 
                    (lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: $IsBox($l#2#i#0, TInt)), 
                    (lambda $l#2#heap#0: Heap, $l#2#i#0: Box :: 
                      SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
                $LS($LZ))), 
            $Box(arrayinit#0#i0#0))
           && $Unbox(read($Heap, $nw, IndexField(arrayinit#0#i0#0))): ref
             == $Unbox(Apply1(TInt, 
                Tclass._module.ChainingObject(), 
                $Heap, 
                Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                      Handle1((lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                          $Box((if $Unbox($l#1#i#0): int == LitInt(0) then t#0 else u#0))), 
                        (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: $IsBox($l#1#i#0, TInt)), 
                        (lambda $l#1#heap#0: Heap, $l#1#i#0: Box :: 
                          SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
                    $LS($LZ))), 
                $Box(arrayinit#0#i0#0))): ref);
    $Heap := update($Heap, $nw, alloc, $Box(true));
    havoc $ReferrersHeap;
    assume (forall $o: ref ::
      { readReferrers($ReferrersHeap, $o) }
      (forall i: int :: 
        0 <= i && i < LitInt(3) ==> $o != $Unbox(read($Heap, $nw, IndexField(i))): ref)
      ==> 
      readReferrers($ReferrersHeap, $o) == readReferrers($ReferrersHeap_at_0, $o));

    // For all objects in the array, the referrers before is a subset of the referrers after
    assume (forall i: int ::
      { read($Heap, $nw, IndexField(i)) }
      0 <= i && i < LitInt(3)
      ==> 
      Set#Subset(
        readReferrers($ReferrersHeap_at_0, $Unbox(read($Heap, $nw, IndexField(i))): ref),
        readReferrers($ReferrersHeap, $Unbox(read($Heap, $nw, IndexField(i))): ref)
      )
    );

    // For all objects in the array at index i, the difference of its referrers after minus referrers before contains (nw, i)
    assume (forall i: int ::
      { read($Heap, $nw, IndexField(i)) }
      { #_System._tuple#2._#Make2($Box($nw), $Box(IndexField(i))) }
      0 <= i && i < LitInt(3)
      ==> 
      Set#IsMember(
        Set#Difference(
          readReferrers($ReferrersHeap, $Unbox(read($Heap, $nw, IndexField(i))): ref),
          readReferrers($ReferrersHeap_at_0, $Unbox(read($Heap, $nw, IndexField(i))): ref)
        ),
        $Box(#_System._tuple#2._#Make2($Box($nw), $Box(IndexField(i))))
      )
    );
    // Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), $Box(r#1))
    // $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref == t#0;
    assume (forall i: int, $r: Box ::
      { Set#IsMember(
          Set#Difference(
            readReferrers($ReferrersHeap, $Unbox(read($Heap, $nw, IndexField(i))): ref),
            readReferrers($ReferrersHeap_at_0, $Unbox(read($Heap, $nw, IndexField(i))): ref)
          ),
          $r
        )
      }
      0 <= i && i < LitInt(3) &&
      Set#IsMember(
        Set#Difference(
          readReferrers($ReferrersHeap, $Unbox(read($Heap, $nw, IndexField(i))): ref),
          readReferrers($ReferrersHeap_at_0, $Unbox(read($Heap, $nw, IndexField(i))): ref)
        ),
        $r
      )
      ==>
      $Unbox(_System.Tuple2._0($Unbox($r): DatatypeType)): ref == $nw
      && 0 <= IndexField_Inverse($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field)
      && IndexField_Inverse($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field) < LitInt(3)
      && read($Heap, $nw, IndexField(IndexField_Inverse($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field)))
         == read($Heap, $nw, IndexField(i))
    );
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    if (a#0 != null)
    {
        assume !Set#IsMember(readReferrers($ReferrersHeap, a#0), 
          $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.a, depth)))));
        $ReferrersHeap := updateReferrers($ReferrersHeap, 
          a#0, 
          Set#UnionOne(readReferrers($ReferrersHeap, a#0), 
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ObjectFields.a, depth))))));
    }

    assume {:captureState "referrers.dfy(146,62)"} true;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(147,3)
    assert {:id "id179"} a#0 != null;
    assert {:id "id180"} {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert {:id "id181"} defass#t#0;
    assume true;
    assert {:id "id182"} $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref == t#0;
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(148,3)
    assert {:id "id183"} a#0 != null;
    assert {:id "id184"} {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert {:id "id185"} defass#t#0;
    assert {:id "id186"} defass#t#0;
    assume true;
    assert {:id "id187"} Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(0))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(149,3)
    assert {:id "id188"} a#0 != null;
    assert {:id "id189"} {:subsumption 0} 0 <= LitInt(1) && LitInt(1) < _System.array.Length(a#0);
    assert {:id "id190"} defass#t#0;
    assert {:id "id191"} defass#t#0;
    assume true;
    assert {:id "id192"} !Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(1))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(150,3)
    assert {:id "id193"} a#0 != null;
    assert {:id "id194"} {:subsumption 0} 0 <= LitInt(2) && LitInt(2) < _System.array.Length(a#0);
    assert {:id "id195"} defass#t#0;
    assert {:id "id196"} defass#t#0;
    assume true;
    assert {:id "id197"} !Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(2))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(151,3)
    assert {:id "id198"} a#0 != null;
    assert {:id "id199"} {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert {:id "id200"} defass#u#0;
    assert {:id "id201"} defass#u#0;
    assume true;
    assert {:id "id202"} !Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, u#0), readReferrers($ReferrersHeap_at_0, u#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(0))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(152,3)
    assert {:id "id203"} a#0 != null;
    assert {:id "id204"} {:subsumption 0} 0 <= LitInt(1) && LitInt(1) < _System.array.Length(a#0);
    assert {:id "id205"} defass#u#0;
    assert {:id "id206"} defass#u#0;
    assume true;
    assert {:id "id207"} Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, u#0), readReferrers($ReferrersHeap_at_0, u#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(1))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(153,3)
    assert {:id "id208"} a#0 != null;
    assert {:id "id209"} {:subsumption 0} 0 <= LitInt(2) && LitInt(2) < _System.array.Length(a#0);
    assert {:id "id210"} defass#u#0;
    assert {:id "id211"} defass#u#0;
    assume true;
    assert {:id "id212"} Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, u#0), readReferrers($ReferrersHeap_at_0, u#0)), 
      $Box(#_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(2))))));
    // ----- assert statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(154,3)
    // Begin Comprehension WF check
    havoc r#0;
    if ($Is(r#0, Tclass._System.Tuple2(Tclass._System.object(), TField))
       && $IsAlloc(r#0, Tclass._System.Tuple2(Tclass._System.object(), TField), $Heap))
    {
        assert {:id "id213"} defass#t#0;
        assert {:id "id214"} defass#t#0;
        if (Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#0)))
        {
            assert {:id "id215"} a#0 != null;
            assert {:id "id216"} {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
        }
    }

    // End Comprehension WF check
    assume (forall r#1: DatatypeType :: 
      { Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#1)) } 
      $Is(r#1, Tclass._System.Tuple2(Tclass._System.object(), TField))
         ==> 
        Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#1))
         ==> $IsA#_System.Tuple2(r#1));
    assume (forall r#1: DatatypeType :: 
      { Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#1)) } 
      $Is(r#1, Tclass._System.Tuple2(Tclass._System.object(), TField))
         ==> 
        Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#1))
         ==> $IsA#_System.Tuple2(r#1));
    assert {:id "id217"} (forall r#1: DatatypeType :: 
      { Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
          $Box(r#1)) } 
      $Is(r#1, Tclass._System.Tuple2(Tclass._System.object(), TField))
            && Set#IsMember(Set#Difference(readReferrers($ReferrersHeap, t#0), readReferrers($ReferrersHeap_at_0, t#0)), 
            $Box(r#1))
          ==> _System.Tuple2#Equal(r#1, #_System._tuple#2._#Make2($Box(a#0), $Box(IndexField(LitInt(0))))));
  }



const unique class._module.SimpleObject?: ClassName;

// $Is axiom for class SimpleObject
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.SimpleObject?()) } 
  $Is($o, Tclass._module.SimpleObject?())
     <==> $o == null || dtype($o) == Tclass._module.SimpleObject?());

// $IsAlloc axiom for class SimpleObject
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.SimpleObject?(), $h) } 
  $IsAlloc($o, Tclass._module.SimpleObject?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

// $Is axiom for non-null type _module.SimpleObject
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.SimpleObject()) } 
    { $Is(c#0, Tclass._module.SimpleObject?()) } 
  $Is(c#0, Tclass._module.SimpleObject())
     <==> $Is(c#0, Tclass._module.SimpleObject?()) && c#0 != null);

// $IsAlloc axiom for non-null type _module.SimpleObject
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.SimpleObject(), $h) } 
  $IsAlloc(c#0, Tclass._module.SimpleObject(), $h)
     <==> $IsAlloc(c#0, Tclass._module.SimpleObject?(), $h));

const unique class._module.ChainingObject?: ClassName;

function Tclass._module.ChainingObject?() : Ty
uses {
// Tclass._module.ChainingObject? Tag
axiom Tag(Tclass._module.ChainingObject?()) == Tagclass._module.ChainingObject?
   && TagFamily(Tclass._module.ChainingObject?()) == tytagFamily$ChainingObject;
}

const unique Tagclass._module.ChainingObject?: TyTag;

// Box/unbox axiom for Tclass._module.ChainingObject?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ChainingObject?()) } 
  $IsBox(bx, Tclass._module.ChainingObject?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ChainingObject?()));

// $Is axiom for class ChainingObject
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.ChainingObject?()) } 
  $Is($o, Tclass._module.ChainingObject?())
     <==> $o == null || dtype($o) == Tclass._module.ChainingObject?());

// $IsAlloc axiom for class ChainingObject
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.ChainingObject?(), $h) } 
  $IsAlloc($o, Tclass._module.ChainingObject?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

const unique _module.ChainingObject.x: Field
uses {
axiom FDim(_module.ChainingObject.x) == 0
   && FieldOfDecl(class._module.ChainingObject?, field$x) == _module.ChainingObject.x
   && !_System.field.IsGhost(_module.ChainingObject.x)
   && field_family(_module.ChainingObject.x) == object_field;
}

// ChainingObject.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.x)): ref } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ChainingObject?()
     ==> $Is($Unbox(read($h, $o, _module.ChainingObject.x)): ref, 
      Tclass._module.ChainingObject?()));

// ChainingObject.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.x)): ref } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ChainingObject?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.ChainingObject.x)): ref, 
      Tclass._module.ChainingObject?(), 
      $h));

const unique _module.ChainingObject.y: Field
uses {
axiom FDim(_module.ChainingObject.y) == 0
   && FieldOfDecl(class._module.ChainingObject?, field$y) == _module.ChainingObject.y
   && !_System.field.IsGhost(_module.ChainingObject.y)
   && field_family(_module.ChainingObject.y) == object_field;
}

// ChainingObject.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.y)): ref } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ChainingObject?()
     ==> $Is($Unbox(read($h, $o, _module.ChainingObject.y)): ref, 
      Tclass._module.ChainingObject?()));

// ChainingObject.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.y)): ref } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ChainingObject?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.ChainingObject.y)): ref, 
      Tclass._module.ChainingObject?(), 
      $h));

const unique _module.ChainingObject.nontracking: Field
uses {
axiom FDim(_module.ChainingObject.nontracking) == 0
   && FieldOfDecl(class._module.ChainingObject?, field$nontracking)
     == _module.ChainingObject.nontracking
   && _System.field.IsGhost(_module.ChainingObject.nontracking)
   && field_family(_module.ChainingObject.nontracking) == object_field;
}

// ChainingObject.nontracking: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.nontracking)): ref } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ChainingObject?()
     ==> $Is($Unbox(read($h, $o, _module.ChainingObject.nontracking)): ref, 
      Tclass._module.ChainingObject?()));

// ChainingObject.nontracking: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.nontracking)): ref } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ChainingObject?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.ChainingObject.nontracking)): ref, 
      Tclass._module.ChainingObject?(), 
      $h));

const unique _module.ChainingObject.tracking: Field
uses {
axiom FDim(_module.ChainingObject.tracking) == 0
   && FieldOfDecl(class._module.ChainingObject?, field$tracking)
     == _module.ChainingObject.tracking
   && _System.field.IsGhost(_module.ChainingObject.tracking)
   && field_family(_module.ChainingObject.tracking) == object_field;
}

// ChainingObject.tracking: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.tracking)): ref } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ChainingObject?()
     ==> $Is($Unbox(read($h, $o, _module.ChainingObject.tracking)): ref, 
      Tclass._module.ChainingObject?()));

// ChainingObject.tracking: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.ChainingObject.tracking)): ref } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ChainingObject?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.ChainingObject.tracking)): ref, 
      Tclass._module.ChainingObject?(), 
      $h));

function _module.ChainingObject.tail(this: ref) : ref;

const unique _module.ChainingObject.tail: Field
uses {
axiom FDim(_module.ChainingObject.tail) == 0
   && FieldOfDecl(class._module.ChainingObject?, field$tail)
     == _module.ChainingObject.tail
   && !_System.field.IsGhost(_module.ChainingObject.tail)
   && field_family(_module.ChainingObject.tail) == object_field;
}

// ChainingObject.tail: Type axiom
axiom (forall $o: ref :: 
  { _module.ChainingObject.tail($o) } 
  $o != null && dtype($o) == Tclass._module.ChainingObject?()
     ==> $Is(_module.ChainingObject.tail($o), Tclass._module.ChainingObject?()));

// ChainingObject.tail: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.ChainingObject.tail($o), $Unbox(read($h, $o, alloc)): bool } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ChainingObject?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc(_module.ChainingObject.tail($o), Tclass._module.ChainingObject?(), $h));

const unique _module.ChainingObject.__ctor.chained__test: FieldFamily;

axiom (forall depth: int :: 
  { local_field(_module.ChainingObject.__ctor.chained__test, depth) } 
  _System.field.IsGhost(local_field(_module.ChainingObject.__ctor.chained__test, depth)));

procedure {:verboseName "ChainingObject._ctor (well-formedness)"} CheckWellFormed$$_module.ChainingObject.__ctor(depth: int, 
    chained_test#0: ref
       where $Is(chained_test#0, Tclass._module.ChainingObject?())
         && $IsAlloc(chained_test#0, Tclass._module.ChainingObject?(), $Heap))
   returns (this: ref);
  free requires Set#IsMember(readReferrers($ReferrersHeap, chained_test#0), 
    $Box(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.ChainingObject.__ctor.chained__test, depth)))));
  modifies $Heap, $ReferrersHeap;



procedure {:verboseName "ChainingObject._ctor (call)"} Call$$_module.ChainingObject.__ctor(depth: int, 
    chained_test#0: ref
       where $Is(chained_test#0, Tclass._module.ChainingObject?())
         && $IsAlloc(chained_test#0, Tclass._module.ChainingObject?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ChainingObject())
         && $IsAlloc(this, Tclass._module.ChainingObject(), $Heap));
  modifies $Heap, $ReferrersHeap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id227"} $Unbox(read($Heap, this, _module.ChainingObject.x)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.y)): ref;
  ensures {:id "id228"} $Unbox(read($Heap, this, _module.ChainingObject.y)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.nontracking)): ref;
  ensures {:id "id229"} $Unbox(read($Heap, this, _module.ChainingObject.nontracking)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.tracking)): ref;
  ensures {:id "id230"} $Unbox(read($Heap, this, _module.ChainingObject.tracking)): ref == null;
  free ensures {:always_assume} true;
  ensures {:id "id231"} _module.ChainingObject.tail(this) == chained_test#0;
  free ensures {:always_assume} true;
  ensures {:id "id232"} chained_test#0 != null
     ==> Set#Equal(readReferrers($ReferrersHeap, chained_test#0), 
      Set#Union(readReferrers(old($ReferrersHeap), chained_test#0), 
        Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(this), $Box(_module.ChainingObject.tail))))));
  free ensures {:always_assume} true;
  ensures {:id "id233"} (forall o#1: ref :: 
    { readReferrers(old($ReferrersHeap), o#1) } 
      { readReferrers($ReferrersHeap, o#1) } 
    $Is(o#1, Tclass._System.object())
         && $IsAlloc(o#1, Tclass._System.object(), $Heap)
         && o#1 != chained_test#0
       ==> Set#Equal(readReferrers($ReferrersHeap, o#1), readReferrers(old($ReferrersHeap), o#1)));
  // constructor allocates the object
  ensures !$Unbox(read(old($Heap), this, alloc)): bool;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "ChainingObject._ctor (correctness)"} Impl$$_module.ChainingObject.__ctor(depth: int, 
    chained_test#0: ref
       where $Is(chained_test#0, Tclass._module.ChainingObject?())
         && $IsAlloc(chained_test#0, Tclass._module.ChainingObject?(), $Heap))
   returns (this: ref, $_reverifyPost: bool);
  free requires Set#IsMember(readReferrers($ReferrersHeap, chained_test#0), 
    $Box(#_System._tuple#2._#Make2($Box(locals), 
        $Box(local_field(_module.ChainingObject.__ctor.chained__test, depth)))));
  modifies $Heap, $ReferrersHeap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id234"} $Unbox(read($Heap, this, _module.ChainingObject.x)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.y)): ref;
  ensures {:id "id235"} $Unbox(read($Heap, this, _module.ChainingObject.y)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.nontracking)): ref;
  ensures {:id "id236"} $Unbox(read($Heap, this, _module.ChainingObject.nontracking)): ref
     == $Unbox(read($Heap, this, _module.ChainingObject.tracking)): ref;
  ensures {:id "id237"} $Unbox(read($Heap, this, _module.ChainingObject.tracking)): ref == null;
  free ensures {:always_assume} true;
  ensures {:id "id238"} _module.ChainingObject.tail(this) == chained_test#0;
  free ensures {:always_assume} true;
  ensures {:id "id239"} chained_test#0 != null
     ==> Set#Equal(readReferrers($ReferrersHeap, chained_test#0), 
      Set#Union(readReferrers(old($ReferrersHeap), chained_test#0), 
        Set#UnionOne(Set#Empty(): Set, 
          $Box(#_System._tuple#2._#Make2($Box(this), $Box(_module.ChainingObject.tail))))));
  free ensures {:always_assume} true;
  ensures {:id "id240"} (forall o#1: ref :: 
    { readReferrers(old($ReferrersHeap), o#1) } 
      { readReferrers($ReferrersHeap, o#1) } 
    $Is(o#1, Tclass._System.object())
         && $IsAlloc(o#1, Tclass._System.object(), $Heap)
         && o#1 != chained_test#0
       ==> Set#Equal(readReferrers($ReferrersHeap, o#1), readReferrers(old($ReferrersHeap), o#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ChainingObject._ctor (correctness)"} Impl$$_module.ChainingObject.__ctor(depth: int, chained_test#0: ref) returns (this: ref, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var this.x: ref;
  var this.y: ref;
  var this.nontracking: ref;
  var this.tracking: ref;
  var this.tail: ref;
  var newtype$check#2: ref;
  var newtype$check#3: ref;
  var newtype$check#4: ref;
  var newtype$check#5: ref;
  assume readReferrers($ReferrersHeap, this) == Set#Empty();
  $ReferrersHeap := updateReferrers($ReferrersHeap, this, Set#UnionOne(readReferrers($ReferrersHeap, this),
    $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.ChainingObject.__ctor.this, depth))))
  ));

    // AddMethodImpl: _ctor, Impl$$_module.ChainingObject.__ctor
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "referrers.dfy(102,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(102,3)
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(103,7)
    assume true;
    assume true;
    newtype$check#2 := null;
    assume true;
    this.x := null;
    assume {:captureState "referrers.dfy(103,13)"} true;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(104,7)
    assume true;
    assume true;
    newtype$check#3 := null;
    assume true;
    this.y := null;
    assume {:captureState "referrers.dfy(104,13)"} true;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(105,14)
    assume true;
    assume true;
    newtype$check#4 := null;
    assume true;
    this.tracking := null;
    assume {:captureState "referrers.dfy(105,20)"} true;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(106,17)
    assume true;
    assume true;
    newtype$check#5 := null;
    assume true;
    this.nontracking := null;
    assume {:captureState "referrers.dfy(106,23)"} true;
    // ----- assignment statement ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(107,10)
    assume true;
    assume true;
    assume true;
    this.tail := chained_test#0;
    if (chained_test#0 != null) {
      $ReferrersHeap := updateReferrers($ReferrersHeap, chained_test#0, Set#UnionOne(readReferrers($ReferrersHeap, chained_test#0),
        $Box(#_System._tuple#2._#Make2($Box(this), $Box(_module.ChainingObject.tail)))
      ));
    }
    assume {:captureState "referrers.dfy(107,24)"} true;
    // ----- new; ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(102,3)
    assume this != null && $Is(this, Tclass._module.ChainingObject?());
    assume !$Unbox(read($Heap, this, alloc)): bool;
    assume $Unbox(read($Heap, this, _module.ChainingObject.x)): ref == this.x;
    assume $Unbox(read($Heap, this, _module.ChainingObject.y)): ref == this.y;
    assume $Unbox(read($Heap, this, _module.ChainingObject.nontracking)): ref
       == this.nontracking;
    assume $Unbox(read($Heap, this, _module.ChainingObject.tracking)): ref == this.tracking;
    assume _module.ChainingObject.tail(this) == this.tail;
    $Heap := update($Heap, this, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- C:\Users\mimayere\Documents\dafny\Source\IntegrationTests\TestFiles\LitTests\LitTest\referrers\referrers.dfy(102,3)
    
    $ReferrersHeap := updateReferrers($ReferrersHeap, this, Set#Difference(readReferrers($ReferrersHeap, this),
      Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.ChainingObject.__ctor.this, depth)))))));
}



// $Is axiom for non-null type _module.ChainingObject
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.ChainingObject()) } 
    { $Is(c#0, Tclass._module.ChainingObject?()) } 
  $Is(c#0, Tclass._module.ChainingObject())
     <==> $Is(c#0, Tclass._module.ChainingObject?()) && c#0 != null);

// $IsAlloc axiom for non-null type _module.ChainingObject
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.ChainingObject(), $h) } 
  $IsAlloc(c#0, Tclass._module.ChainingObject(), $h)
     <==> $IsAlloc(c#0, Tclass._module.ChainingObject?(), $h));

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$SimpleObject: TyTagFamily;

const unique tytagFamily$ChainingObject: TyTagFamily;

const unique field$x: NameFamily;

const unique field$y: NameFamily;

const unique field$tracking: NameFamily;

const unique field$nontracking: NameFamily;

const unique field$tail: NameFamily;
