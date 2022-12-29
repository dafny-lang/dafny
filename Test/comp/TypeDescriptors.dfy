// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Method<G(0)>(s: string, g: G) {
  var zero: G;
  print s, ": ", g, " ", zero, "\n";
}

method MethodX<G(0)>(s: string, g: G) {  // don't print g
  var zero: G;
  print s, ": ", zero, "\n";
}

method Get<G(0)>(g: G) returns (zero: G) {
}

method MethodChar(s: string, ch: char) {
  var zero := Get(ch);
  print s, ": ", PrCh(ch), " ", PrCh(zero), "\n";
}

function method PrCh(ch: char): string {
  if ch == '\0' then "'\\0'"
  else if ch == 'D' then "'D'"
  else if ch == 'r' then "'r'"
  else "'(other char)'"
}

method Main() {
  // primitive types
  Method("int", 8);
  Method("bool", true);
  MethodChar("char", 'r');
  Method("real", 1.618);
  var ord: ORDINAL;  // note, ORDINAL cannot be passed as type parameter
  print "ORDINAL: ", ord, "\n";
  Method("bv0", 0 as bv0);
  Method("bv21", 121 as bv21);
  Method("bv32", 132 as bv32);
  Method("bv191", 191 as bv191);

  // collections
  Method("set<int>", {7});
  Method("multiset<int>", multiset{7, 7});
  Method("seq<int>", [7]);
  Method("map<int, int>", map[2 := 7]);

  // subset types
  Method("pos", 3 as pos);

  // newtypes
  Method("Hundred", 6 as Hundred); // nativeType, no witness
  Method("HundredOdd", 13 as HundredOdd); // nativeType, with witness
  Method("JustOdd", 131 as JustOdd); // just witness

  // tuples
  Method("()", ());
  Method("(int, real)", (2, 3.2));
  Method("(int, pos)", (2, 3 as pos));

  // datatypes
  Method("AtomicShells<bool>", Atom(true));
  Method("AtomicShells<AtomicShells<int>>", Atom(Atom(3)));
  Method("AtomicShells<AtomicShells<pos>>", Atom(Atom(3 as pos)));
  var u: Class := new Class<int, int>;
  Method("Record<int, Class<int, int>, Class<real, real>>", Record<int, Class?<int, int>, Class<real, real>>.SimpleRecord(5, u));

  // codatatypes
  print "Stream<int>: ", Up(0), "\n";
  // THIS COULD BE SUPPORTED: Method("Stream<int>", Up(0));

  // type parameters
  TypeParameterViaMember("int", 15);
  var cc := new TypeParameterViaClass("int", 16);
  cc.ItIsTime();
  var dd := TypeParameterViaDatatype<set<int>>.TPVD;
  dd.CallMethod({14});

  var obj: object? := new object;
  MethodX("object?", obj);

  var uh: Class? := new Class<pos, Stream<nat>>;
  var vh: Trait? := uh;
  MethodX("Class?<pos, Stream<nat>>", uh);
  MethodX("Trait?<seq<pos>>", vh);

  var arr: array?<bool> := new bool[25];
  var mat: array2?<bool> := new bool[25, 20];
  MethodX("array?<bool>", arr);
  MethodX("array2?<bool>", mat);

  // arrow types
  // THIS COULD BE SUPPORTED: MethodX("int -> bool", IntBoolFunction);
  MethodX("int --> bool", IntBoolFunctionPartial);
  MethodX("array?<int> ~> bool", IntBoolFunctionReads);
}

method TypeParameterViaMember<A(0)>(s: string, a: A) {
  Method("A=" + s, a);
}

class TypeParameterViaClass<B(0)> {
  var s: string
  var b: B
  constructor (s: string, b: B) {
    this.s, this.b := s, b;
  }
  method ItIsTime() {
    Method("B=" + s, b);
  }
}

datatype TypeParameterViaDatatype<B(0)> = TPVD {
  method CallMethod(b: B) {
    Method("datatype.B=", b);
  }
}

type pos = x | 1 <= x witness 1

newtype Hundred = x | 0 <= x < 100
newtype HundredOdd = x | 0 <= x < 100 && x % 2 == 1 witness 19
newtype JustOdd = x | x % 2 == 1 witness 5

datatype AtomicShells<A> = Atom(a: A) | Shell(inner: AtomicShells<A>)
datatype Record<Compiled(0), Ghost, Unused> =
  | SimpleRecord(Compiled, ghost Ghost)
  | ComplicatedAlternative(Record<Compiled, Ghost, Unused>)

codatatype Stream<B> = More(B, Stream<B>)
function method Up(x: int): Stream<int> {
  More(x, Up(x + 1))
}

trait Trait<T> { }
class Class<A, B> extends Trait<seq<A>> { }

function method IntBoolFunction(x: int): bool
{ x % 2 == 0 }
function method IntBoolFunctionPartial(x: int): bool
  requires x < 67
{ x % 2 == 0 }
function method IntBoolFunctionReads(a: array?<int>): bool
  requires a != null
  reads a
{ true }
