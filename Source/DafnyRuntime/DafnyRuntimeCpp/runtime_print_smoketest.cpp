// Standalone smoke test for the c++ target's runtime printers.
//
//   c++ -std=c++17 -I. runtime_print_smoketest.cpp -o /tmp/rt_smoke && /tmp/rt_smoke
//
// It exercises the collection/tuple print rewrites (dafny_print_to, set/map/seq
// braces + separators, tuple parentheses via index_sequence) and the scalar
// get_default specializations that previously failed to link.
#include <sstream>
#include <cassert>
#include <string>
#include <cstdio>

#include "DafnyRuntime.h"

template <typename T>
static std::string to_s(const T& v) {
  std::ostringstream os;
  os << v;
  return os.str();
}

// Mimic the datatype operator<< the code generator now emits (EmitDatatypePrintOperator).
// The generated body calls dafny_print_to(out, field) — this proves that helper
// exists in the base runtime and that `Typename.Ctor(fields)` printing compiles.
// Stand-in for `datatype Color = Blue(x: int, ok: bool)`.
struct Color { int x; bool ok; };
inline std::ostream& operator<<(std::ostream& out, const Color& d) {
  (void)d;
  out << "Color.Blue";
  out << "(";
  dafny_print_to(out, d.x);
  out << ", ";
  dafny_print_to(out, d.ok);
  out << ")";
  return out;
}

int main() {
  // Sequence: [1, 2, 3]
  DafnySequence<int> seq = DafnySequence<int>::Create({1, 2, 3});
  assert(to_s(seq) == "[1, 2, 3]");

  // Seq of bool prints true/false, not 1/0.
  DafnySequence<bool> bs = DafnySequence<bool>::Create({true, false});
  assert(to_s(bs) == "[true, false]");

  // Set: {a, b} with braces + separator (order is unspecified, so check shape).
  DafnySet<int> s = DafnySet<int>::Create({7});
  assert(to_s(s) == "{7}");

  // Map: map[k := v]
  DafnyMap<int, int> m = DafnyMap<int, int>::Create({{1, 10}});
  assert(to_s(m) == "map[1 := 10]");

  // Map-literal duplicate key: LAST value wins.
  DafnyMap<int, int> dup = DafnyMap<int, int>::Create({{1, 10}, {1, 20}});
  assert(to_s(dup) == "map[1 := 20]");

  // Tuple: (a, b, c) via parentheses.
  Tuple<int, bool, int> t(1, true, 3);
  assert(to_s(t) == "(1, true, 3)");

  // Scalar get_default specializations must link (regression: tuple of char).
  Tuple<bool, char> tc;
  (void)tc;
  assert(get_default<long>::call() == 0);
  assert(get_default<short>::call() == 0);

  // 8-bit newtype carriers print as numbers, not raw bytes.
  { std::ostringstream os; dafny_print_to<uint8_t>(os, (uint8_t)255); assert(os.str() == "255"); }

  // Generated datatype operator<< shape: `Typename.Ctor(f0, f1)`.
  Color c{3, true};
  assert(to_s(c) == "Color.Blue(3, true)");
  // A datatype nested in a collection prints via dafny_print_to too.
  DafnySequence<Color> cs = DafnySequence<Color>::Create({Color{1, false}});
  assert(to_s(cs) == "[Color.Blue(1, false)]");

  std::printf("runtime_print_smoketest: OK\n");
  return 0;
}
