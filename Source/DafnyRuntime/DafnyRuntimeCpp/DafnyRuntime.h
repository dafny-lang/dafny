// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#pragma once

#include <iostream>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>
#include <memory>
#include <unordered_set>
#include <unordered_map>
#include <cstring>
#include <cstdint>
#include <variant>
#include <exception>

// ===========================================================================
//  ARBITRARY-PRECISION INTEGER / EXACT REAL BACKEND (the "bignum seam")
// ===========================================================================
//
// With `--bignum=boost` the C++ backend supports Dafny's unbounded `int`
// and exact `real`, which C++ has no built-in type for (unlike C#/Java/Go/Rust/
// Python, whose standard libraries provide a big integer). The only two realistic
// options are a third-party big-integer library or a hand-written one; this uses
// Boost.Multiprecision cpp_int:
//   - header-only (no library to link), so it builds identically on
//     gcc / clang / MSVC (the common Windows/Visual C++ toolchain);
//   - Boost Software License (permissive, MIT-compatible): a compiled Dafny
//     program carries no copyleft / relink obligation onto its end users.
// The user provides Boost (via -I / DAFNY_CPP_BOOST_PREFIX), the same way the JS
// target expects bignumber.js — Dafny does not fetch or bundle it.
// (GMP was considered as an alternative but not used: it is LGPL, pushing relink
// obligations onto users who ship binaries, and has no official MSVC build.)
//
// The generated code and the rest of this runtime only ever mention `DafnyBigInt`,
// `DafnyReal`, and the free helper functions below — the concrete library type
// is confined to this seam.
//
// The ENTIRE bignum block below (this seam, DafnyReal, the multiplicity/print
// helpers and the get_default specializations) is compiled only when
// DAFNY_BIGNUM is defined, which the C++ backend passes under `--bignum=<impl>`.
// Without the flag the `c++` target never sets it, so it needs no Boost headers
// and keeps compiling exactly as before.
//
// DafnyBigInt uses Boost.Multiprecision cpp_int (header-only). Boost is under the
// Boost Software License 1.0 (permissive, MIT-compatible); its headers carry their
// own copyright notices. See https://www.boost.org/LICENSE_1_0.txt .
// ===========================================================================
#ifdef DAFNY_BIGNUM

// ---- bignum library seam --------------------------------------------------
// -DDAFNY_BIGNUM_<impl> selects the big-integer library. Each branch must define
// `DafnyBigInt` and the four primitive helpers (dafny_sign, dafny_int_str,
// dafny_abs, dafny_gcd). Everything else in this header (dafny_to_long/ulong/
// from_native, DafnyReal, DafnyMultiset, printing) is written against those, so a
// new backend is just another branch here plus a new case in CppBackend.cs.
#if defined(DAFNY_BIGNUM_BOOST)
#include <boost/multiprecision/cpp_int.hpp>
using DafnyBigInt = boost::multiprecision::cpp_int;
static inline int         dafny_sign(const DafnyBigInt& x) { return x.sign(); }
static inline std::string dafny_int_str(const DafnyBigInt& x) { return x.str(); }
static inline DafnyBigInt dafny_abs(const DafnyBigInt& x) { return boost::multiprecision::abs(x); }
static inline DafnyBigInt dafny_gcd(const DafnyBigInt& a, const DafnyBigInt& b) {
  return boost::multiprecision::gcd(a, b);
}
#else
#error "DAFNY_BIGNUM is set but no bignum backend was selected (expected -DDAFNY_BIGNUM_BOOST)."
#endif
// ---- end seam; the rest is backend-agnostic -------------------------------

// Narrow to a native machine integer (the generated code uses these when a Dafny
// int flows into a native-typed slot: a char, a collection index, ...).
static inline long          dafny_to_long(const DafnyBigInt& x) { return x.convert_to<long>(); }
static inline unsigned long dafny_to_ulong(const DafnyBigInt& x) { return x.convert_to<unsigned long>(); }

// Build a DafnyBigInt from ANY native integer, widening (never narrowing). Needed
// for native->int conversions (e.g. `b as int` where b is a bv64/uint64): routes
// every native integer through a form that keeps all 64 bits regardless of whether
// `long` is 64-bit (LP64) or 32-bit (LLP64/Windows). `#include <string>` and
// <type_traits> are already pulled in at the top of the header.
template <typename N>
static inline DafnyBigInt dafny_from_native(N v) {
  static_assert(std::is_integral<N>::value, "dafny_from_native expects a native integer");
  if (sizeof(N) <= sizeof(long)) {
    // Fits a (signed/unsigned) long the ctors accept directly.
    if (std::is_signed<N>::value) { return DafnyBigInt((long)v); }
    return DafnyBigInt((unsigned long)v);
  }
  // 64-bit on LLP64 (Windows) or any type wider than long: go through a decimal
  // string so no bits are lost and no ambiguous ctor is selected.
  return DafnyBigInt(std::to_string(v));
}

// Note: for values that don't fit, Boost convert_to<> throws std::range_error
// (including a negative value through the unsigned form). The generated code only
// calls these at sites Dafny typing keeps in range and non-negative (collection
// indices, slice bounds, char conversions, multiset multiplicities), so on a
// verified program neither the truncation nor the throw is reachable.

// ---------------------------------------------------------------------------
// Reals (Dafny `real`) as an UNREDUCED rational num/den, mirroring C#'s
// Dafny.BigRational.
//
// A Dafny `real` is an EXACT rational, not a float. We represent it as two
// DafnyBigInt (num, den) with the invariant `1 <= den` (or num == 0). CRUCIALLY
// we do NOT keep it reduced: C#'s BigRational multiplies/divides WITHOUT
// reducing (`*` = num*num / den*den), so 1.5/0.5 is stored as 150/50, not 3/1.
// Its ToString then pads the decimal to the trailing-zero count implied by the
// unreduced denominator's 2/5 factors ("3.00", not "3.0"). A canonical rational
// (Boost cpp_rational, always reduced) would instead print
// "3.0" and diverge from every other Dafny backend, which is why we keep our own
// unreduced num/den pair here rather than using a library rational type.
// ---------------------------------------------------------------------------
class DafnyReal {
 public:
  DafnyBigInt num, den;   // invariant: den >= 1 (or num == 0)

  DafnyReal() : num(0), den(1) {}
  DafnyReal(const DafnyBigInt& n, const DafnyBigInt& d) : num(n), den(d) {}
  // From an unbounded integer: n/1.
  explicit DafnyReal(const DafnyBigInt& n) : num(n), den(1) {}
  explicit DafnyReal(long n) : num(n), den(1) {}
  // From a numerator/denominator decimal-string pair, e.g. "15","10" for 1.5.
  // The frontend hands us the literal's exact num/den; keep them UNREDUCED so
  // the printed precision matches C#.
  DafnyReal(const char* n, const char* d) : num(DafnyBigInt(n)), den(DafnyBigInt(d)) {}

  // C#'s BigRational.Normalize: reduce the two denominators by their gcd first,
  // so the common denominator is a.den * (b.den/gcd), NOT the raw product. This
  // is what makes 0.5+0.5 print "1.0" (den 10, not 100) and 0.75-0.25 print
  // "0.50" (den 100, not 10000). If either operand is 0, the other's num/den is
  // used as-is. Fills aa, bb, dd such that the values are aa/dd and bb/dd.
  static void Normalize(const DafnyReal& a, const DafnyReal& b,
                        DafnyBigInt& aa, DafnyBigInt& bb, DafnyBigInt& dd) {
    if (dafny_sign(a.num) == 0) {
      aa = a.num; bb = b.num; dd = b.den;
    } else if (dafny_sign(b.num) == 0) {
      aa = a.num; dd = a.den; bb = b.num;
    } else {
      DafnyBigInt g = dafny_gcd(a.den, b.den);
      DafnyBigInt xx = a.den / g;
      DafnyBigInt yy = b.den / g;
      aa = a.num * yy;
      bb = b.num * xx;
      dd = a.den * yy;
    }
  }

  DafnyReal operator+(const DafnyReal& b) const {
    DafnyBigInt aa, bb, dd; Normalize(*this, b, aa, bb, dd);
    return DafnyReal(DafnyBigInt(aa + bb), dd);
  }
  DafnyReal operator-(const DafnyReal& b) const {
    DafnyBigInt aa, bb, dd; Normalize(*this, b, aa, bb, dd);
    return DafnyReal(DafnyBigInt(aa - bb), dd);
  }
  // BigRational: num*num / den*den, UNREDUCED.
  DafnyReal operator*(const DafnyReal& b) const {
    return DafnyReal(DafnyBigInt(num * b.num), DafnyBigInt(den * b.den));
  }
  // BigRational: a * reciprocal(b), keeping den >= 1. reciprocal(b) = b.den/b.num
  // (with the sign moved onto the numerator when b.num < 0). UNREDUCED.
  DafnyReal operator/(const DafnyReal& b) const {
    if (dafny_sign(b.num) > 0) {
      return DafnyReal(DafnyBigInt(num * b.den), DafnyBigInt(den * b.num));
    } else {
      // b.num < 0: reciprocal is (-b.den)/(-b.num) to keep den positive.
      return DafnyReal(DafnyBigInt(num * DafnyBigInt(-b.den)),
                       DafnyBigInt(den * DafnyBigInt(-b.num)));
    }
  }
  DafnyReal operator-() const { return DafnyReal(DafnyBigInt(-num), den); }

  // Compare by cross-multiplication: sign(a.num*b.den - b.num*a.den), valid
  // because both denominators are >= 1 (positive). Matches BigRational.CompareTo.
  int cmp(const DafnyReal& b) const {
    DafnyBigInt lhs = num * b.den;
    DafnyBigInt rhs = b.num * den;
    if (lhs < rhs) { return -1; }
    if (lhs > rhs) { return 1; }
    return 0;
  }
  bool operator==(const DafnyReal& b) const { return cmp(b) == 0; }
  bool operator!=(const DafnyReal& b) const { return cmp(b) != 0; }
  bool operator<(const DafnyReal& b) const { return cmp(b) < 0; }
  bool operator<=(const DafnyReal& b) const { return cmp(b) <= 0; }
  bool operator>(const DafnyReal& b) const { return cmp(b) > 0; }
  bool operator>=(const DafnyReal& b) const { return cmp(b) >= 0; }

  // real -> int, flooring toward negative infinity (Dafny's `.Floor`, and the
  // target for `r as int` when r is provably integral). Works on the unreduced
  // fraction: floor(num/den) with den >= 1. Both backends' `/` truncate toward
  // zero, so subtract one when the truncation rounded the wrong way (num < 0
  // with a nonzero remainder).
  DafnyBigInt Floor() const {
    DafnyBigInt q = num / den;
    DafnyBigInt r = num - q * den;
    if (dafny_sign(r) < 0) { q = q - 1; }
    return q;
  }
};

// Neither backend ships a std::hash for its bignum type usable here for DafnyReal,
// and Dafny stores reals in hash-based collections (sets/maps). The stored num/den
// are UNREDUCED, so equal values (e.g. 3/1 and 150/50) have different num/den; we
// must hash the REDUCED form so they collide, matching DafnyReal::operator==.
namespace std {
  template <> struct hash<DafnyReal> {
    size_t operator()(const DafnyReal& x) const {
      DafnyBigInt num = x.num, den = x.den;
      if (dafny_sign(num) == 0) {
        den = 1;                       // 0/d normalizes to 0/1
      } else {
        DafnyBigInt g = dafny_gcd(dafny_abs(num), den);
        num = num / g;
        den = den / g;
      }
      return std::hash<std::string>()(dafny_int_str(num) + "/" + dafny_int_str(den));
    }
  };
}

// Dafny defines integer division/modulo as EUCLIDEAN: a == (a/b)*b + a%b with
// 0 <= a%b < |b|. Both backends' operator/ and operator% truncate toward zero,
// so route int Div/Mod through these helpers (used under --bignum).
inline DafnyBigInt DafnyEuclideanMod(const DafnyBigInt& a, const DafnyBigInt& b) {
  DafnyBigInt r = a % b;                 // truncated; sign follows a
  if (dafny_sign(r) < 0) { r = r + dafny_abs(b); }
  return r;                              // now 0 <= r < |b|
}

inline DafnyBigInt DafnyEuclideanDiv(const DafnyBigInt& a, const DafnyBigInt& b) {
  DafnyBigInt q = a / b;                 // truncated toward zero
  DafnyBigInt r = a % b;
  if (dafny_sign(r) < 0) { q = q + ((dafny_sign(b) > 0) ? -1 : 1); }
  return q;
}

// Materialize a value of Dafny type `int` / `real` into a concrete DafnyBigInt /
// DafnyReal. Overloads let the concrete type pass through while disambiguating
// cardinality results (|s|, |m|, ...) which come back as a plain uint64 that the
// bignum ctor may not accept unambiguously. Used by the print path.
inline DafnyBigInt dafny_as_int(const DafnyBigInt& x) { return x; }
// Boost cpp_int constructs from unsigned long long directly, no truncation.
inline DafnyBigInt dafny_as_int(unsigned long long x) { return DafnyBigInt(x); }
inline DafnyReal dafny_as_real(const DafnyReal& x) { return x; }

#endif  // DAFNY_BIGNUM

typedef uint8_t  uint8;
typedef uint16_t uint16;
typedef uint32_t uint32;
typedef uint64_t uint64;

typedef int8_t   int8;
typedef int16_t  int16;
typedef int32_t  int32;
typedef int64_t  int64;

/*********************************************************
 *  UTILITIES                                            *
 *********************************************************/

class DafnyHaltException : public std::runtime_error{
  public:
  DafnyHaltException(std::string msg) : std::runtime_error(msg) {}
};

// using boost::hash_combine
template <class T>
inline void hash_combine(std::size_t& seed, T const& v)
{
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

// From https://stackoverflow.com/a/7185723
class IntegerRange {
 public:
   class iterator {
      friend class IntegerRange;
    public:
      long int operator *() const { return i_; }
      const iterator &operator ++() { ++i_; return *this; }
      iterator operator ++(int) { iterator copy(*this); ++i_; return copy; }

      bool operator ==(const iterator &other) const { return i_ == other.i_; }
      bool operator !=(const iterator &other) const { return i_ != other.i_; }

    protected:
      iterator(long int start) : i_ (start) { }

    private:
      unsigned long i_;
   };

   iterator begin() const { return begin_; }
   iterator end() const { return end_; }
   IntegerRange(long int  begin, long int end) : begin_(begin), end_(end) {}
private:
   iterator begin_;
   iterator end_;
};

// Workaround the fact that Apple's clang and g++ print nullptr as 0x0,
// while Linux's g++ prints it as 0
template<typename T>
void dafny_print(T x) {
  std::cout << x;
}

// Special-case bool so that the C++ output matches that of other backends
template<>
void dafny_print<bool>(bool x) {
  if (x) {
    std::cout << "true";
  } else {
    std::cout << "false";
  }
}

template<typename T>
void dafny_print(T* x) {
  std::cout << (x ? "true" : "false");
}

template<typename T>
void dafny_print(std::shared_ptr<T> x) {
  if (x == nullptr) {
    std::cout << "NULL";
  } else {
    std::cout << x;
  }
}

#ifdef DAFNY_BIGNUM
// Unbounded Dafny `int` prints as a plain decimal.
inline void dafny_print(const DafnyBigInt& x) {
  std::cout << dafny_int_str(x);
}

// DividesAPowerOf10: returns true if `d` (>= 1) divides some 10^k, i.e. it has
// only factors 2 and 5. On success `factor` and `log10` satisfy
//   10^log10 == factor * d
inline bool dafny__divides_pow10(const DafnyBigInt& d_in, DafnyBigInt& factor, int& log10) {
  DafnyBigInt i = d_in;
  factor = 1;
  log10 = 0;
  if (dafny_sign(i) <= 0) { return false; }
  while (i % 10 == 0) { i = i / 10; log10++; }
  while (i % 5 == 0)  { i = i / 5;  factor = factor * 2; log10++; }
  while (i % 2 == 0)  { i = i / 2;  factor = factor * 5; log10++; }
  return i == 1;
}

// Print a real EXACTLY the way Dafny's BigRational.ToString does, operating on
// the UNREDUCED num/den (so trailing-zero precision matches C#, e.g. 150/50 ->
// "3.00"):
//   * whole numbers ("num == 0 || den == 1")           -> "<num>.0"
//   * terminating decimals (den has only 2/5 factors)  -> "<int>.<frac>"
//   * everything else (non-terminating, e.g. 1/3)      -> "(<num>.0 / <den>.0)"
// Core formatter: writes to any ostream so it serves both the top-level
// dafny_print(DafnyReal) and operator<<(ostream&, DafnyReal) used when a real is
// nested inside a printed collection/tuple/datatype.
inline void dafny_real_write(std::ostream& os, const DafnyReal& x) {
  const DafnyBigInt& num = x.num;
  const DafnyBigInt& den = x.den;

  if (dafny_sign(num) == 0 || den == 1) {
    os << dafny_int_str(num) << ".0";
    return;
  }

  DafnyBigInt factor;
  int log10;
  if (dafny__divides_pow10(den, factor, log10)) {
    // n = num * factor; place decimal point log10 digits from the right.
    DafnyBigInt n = num * factor;
    bool neg = (dafny_sign(n) < 0);
    if (neg) { n = -n; }
    std::string digits = dafny_int_str(n);   // no sign
    int dlen = (int)digits.size();
    if (neg) { os << "-"; }
    if (log10 < dlen) {
      int digitCount = dlen - log10;
      os << digits.substr(0, digitCount) << "."
         << digits.substr(digitCount);
    } else {
      // 0.<zeros><digits>
      os << "0.";
      for (int k = 0; k < log10 - dlen; k++) { os << "0"; }
      os << digits;
    }
  } else {
    // Non-terminating: exact fraction form "(num.0 / den.0)".
    os << "(" << dafny_int_str(num) << ".0 / " << dafny_int_str(den) << ".0)";
  }
}

inline void dafny_print(const DafnyReal& x) { dafny_real_write(std::cout, x); }

// Needed when an int/real is an element of a printed collection/tuple/datatype:
// the generic collection printers do `dafny_print_to(os, element)` -> `os << x`.
inline std::ostream& operator<<(std::ostream& os, const DafnyReal& x) {
  dafny_real_write(os, x);
  return os;
}
#endif  // DAFNY_BIGNUM

/*********************************************************
 *  DEFAULTS                                             *
 *********************************************************/

template<typename T>
struct get_default {
  static T call();
};

template<>
struct get_default<bool> {
  static bool call() { return true; }
};

template<>
struct get_default<int> {
  static int call() { return 0; }
};

template<>
struct get_default<unsigned int> {
  static unsigned int call() { return 0; }
};

template<>
struct get_default<unsigned long> {
  static unsigned long call() { return 0; }
};

template<>
struct get_default<unsigned long long> {
  static unsigned long long call() { return 0; }
};

#ifdef DAFNY_BIGNUM
// The bignum value types need a default too, otherwise a
// Tuple<DafnyBigInt, ...> or a default-constructed field references an undefined
// get_default at link time. int -> DafnyBigInt(0), real -> DafnyReal(0).
template<>
struct get_default<DafnyBigInt> {
  static DafnyBigInt call() { return DafnyBigInt(0); }
};

template<>
struct get_default<DafnyReal> {
  static DafnyReal call() { return DafnyReal(0L); }
};
#endif  // DAFNY_BIGNUM

template<typename U>
struct get_default<std::shared_ptr<U>> {
  static std::shared_ptr<U> call() {
    return std::make_shared<U>(get_default<U>::call());
  }
};

/*********************************************************
 *  TUPLES                                               *
 *********************************************************/

struct Tuple0 {};

template <typename... Types>
struct Tuple{
 public:
  Tuple() : Tuple(get_default<Types>::call()...) {}
  Tuple(Types... values) : values_(values...) {}

  using StdTuple = std::tuple<Types...>;

  template <std::size_t Index>
  std::tuple_element_t<Index, StdTuple> get() {
    return std::get<Index>(values_);
  }

  StdTuple values_;
};

template <typename TupleType, int Index = TupleType::size() - 1 >
std::ostream& PrintElements(const TupleType& tuple, std::ostream& out) {
  if (Index != 0) {
    PrintElements<TupleType, Index - 1>(tuple, out);
  }
  return out << std::get<Index>(tuple);
}

// Use a separate head template parameter to force Tuple to have at least one
// element. This prevents the compiler from eagerly expanding Tail as an empty
// list and causing compilation errors.
template <typename Head, typename... Tail>
inline std::ostream& operator<<(std::ostream& out, const Tuple<Head, Tail...>& val){
  return PrintElements(val.values_, out);
}

/*********************************************************
 *  MATH                                                 *
 *********************************************************/


inline int64 EuclideanDivision_int64(int64 a, int64 b) {
    if (0 <= a) {
        if (0 <= b) {
            // +a +b: a/b
            return (int64)((uint64) a / (uint64) b);
        } else {
            // +a -b: -(a/(-b))
            return -(int64)((uint64) a / (uint64) -b);
        }
    } else {
        if (0 <= b) {
            // -a +b: -((-a-1)/b) - 1
            return -(int64)((((uint64) (-(a + 1)))/ (uint64) b) - 1);
        } else {
            // -a -b: ((-a-1)/(-b)) + 1
            return (int64)((((uint64) (-(a + 1)))/ (uint64) -b) + 1);
        }
    }
}

/*********************************************************
 *  ARRAYS
 *********************************************************/

template <typename T>
struct DafnyArray {
  std::shared_ptr<T> sptr;
  size_t len;

  DafnyArray() { }
  DafnyArray(size_t len) : len(len) {
    sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
  }
  DafnyArray(std::vector<T> contents) : DafnyArray(contents.size()) {
    for (uint64 i = 0; i < contents.size(); i++) {
        sptr[i] = contents[i];
    }
  }

  void assign(T* start, T* end) {
    T* src = sptr.get();
    while (start < end) {
      *src = *start;
      src++;
      start++;
    }
  }

  DafnyArray(T* start, T* end) : DafnyArray((end - start)/sizeof(T)) {
    assign(start, end);
  }

  static DafnyArray<T> Null() { return DafnyArray<T>(); }
  static DafnyArray<T> New(size_t len) { return DafnyArray<T>(len); }

  size_t size() const { return len; }
  T& at(uint64 idx) const { return *(sptr.get() + idx); }
  T& operator[](uint64 idx) const { return at(idx); }

  bool operator==(DafnyArray<T> const& other) const {
    return sptr == other.sptr;
  }

  T* ptr() const { return sptr.get(); }

  T* begin() const { return sptr.get(); }
  T* end() const { return sptr.get() + len; }

  void clear_and_resize(uint64 new_len) {
    std::shared_ptr<T> new_sptr = std::shared_ptr<T> (new T[new_len], std::default_delete<T[]>());
    sptr = new_sptr;
  }


};

template<typename U>
struct get_default<DafnyArray<U>> {
  static DafnyArray<U> call() {
    DafnyArray<U> ret;
    return ret;
  }
};

/*********************************************************
 *  SEQUENCES                                            *
 *********************************************************/

template <typename T>
T* global_empty_ptr = new T[1];

template <class T>
struct DafnySequence {
    std::shared_ptr<T> sptr;
    T* start;
    size_t len;

    DafnySequence() {
      sptr = nullptr;
      start = global_empty_ptr<T>;
      len = 0;
    }

    explicit DafnySequence(uint64 len) {
      sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
      start = &*sptr;
      this->len = len;
    }

    DafnySequence(const DafnySequence<T>& other) {
      sptr = other.sptr;
      start = other.start;
      len = other.len;
    }

    // Update one element
    DafnySequence(const DafnySequence<T>& other, uint64 i, T t) {
      len = other.length();
      sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
      start = &*sptr;

      std::copy(other.start, other.start + len, start);
      start[i] = t;
    }

    explicit DafnySequence(DafnyArray<T> arr) {
      len = arr.size();
      sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
      start = &*sptr;
      std::copy(arr.begin(), arr.end(), start);
    }

    DafnySequence(DafnyArray<T> arr, uint64 lo, uint64 hi) {
      len = hi - lo;
      sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
      start = &*sptr;
      std::copy(arr.begin() + lo, arr.begin() + hi, start);
    }

    DafnySequence(std::initializer_list<T> il) {
      len = il.size();
      sptr = std::shared_ptr<T> (new T[len], std::default_delete<T[]>());
      start = &*sptr;

      int i = 0;
      for (T const& t : il) {
        start[i] = t;
        i++;
      }
    }

    static DafnySequence<T> SeqFromArray(DafnyArray<T> arr) {
        DafnySequence<T> ret(arr);
        return ret;
    }

    static DafnySequence<T> SeqFromArrayPrefix(DafnyArray<T> arr, uint64 hi) {
        DafnySequence<T> ret(arr, 0, hi);
        return ret;
    }

    static DafnySequence<T> SeqFromArraySuffix(DafnyArray<T> arr, uint64 lo) {
        DafnySequence<T> ret(arr, lo, arr.size());
        return ret;
    }

    static DafnySequence<T> SeqFromArraySlice(DafnyArray<T> arr, uint64 lo, uint64 hi) {
        DafnySequence<T> ret(arr, lo, hi);
        return ret;
    }

    static DafnySequence<T> Create(std::initializer_list<T> il) {
        DafnySequence<T> ret(il);
        return ret;
    }

    // TODO: isPrefixOf, isProperPrefixOf

    DafnySequence<T> concatenate(DafnySequence<T> other) {
        DafnySequence<T> ret(this->size() + other.size());
        std::copy(this->ptr(), this->ptr() + this->size(), ret.ptr());
        std::copy(other.ptr(), other.ptr() + other.size(), ret.ptr() + this->size());
        return ret;
    }

    T select(uint64 i) const {
        return start[i];
    }

    uint64 length () const { return len; }
    uint64 size() const { return len; }

    DafnySequence<T> update(uint64 i, T t) const {
        DafnySequence<T> ret(*this, i, t);
        return ret;
    }

    bool contains(T t) const {
        for (uint64 i = 0; i < size(); i++) {
            if (select(i) == t) {
                return true;
            }
        }
        return false;
    }

    // Returns the subsequence of values [lo..hi)
    DafnySequence<T> subsequence(uint64 lo, uint64 hi) const {
        DafnySequence<T> ret;
        ret.sptr = sptr;
        ret.start = start + lo;
        ret.len = hi - lo;
        return ret;
    }

    // Returns the subsequence of values [lo..length())
    DafnySequence<T> drop(uint64 lo) const {
        return subsequence(lo, size());
    }

    // Returns the subsequence of values [0..hi)
    DafnySequence<T> take(uint64 hi) const {
        return subsequence(0, hi);
    }

    // TODO: slice

    bool equals(const DafnySequence<T> other) const {
      if (size() != other.size()) {
        return false;
      }
      for (size_t i = 0; i < size(); i++) {
        if (start[i] != other.start[i]) {
          return false;
        }
      }
      return true;
    }

    T* ptr() const { return start; }
};

inline DafnySequence<char> DafnySequenceFromString(std::string const& s) {
  DafnySequence<char> seq(s.size());
  memcpy(seq.ptr(), &s[0], s.size());
  return seq;
}

inline std::string ToVerbatimString(DafnySequence<char> s) {
  std::string ret(s.start, s.len);
  return ret;
}

template <typename T>
std::ostream& operator<<(std::ostream& os, const DafnySequence<T>& s)
{
  os << "[";
  for (size_t i = 0; i < s.size(); i++) {
    os << s.select(i);
    if (i != s.size() - 1) {
      os << ", ";
    }
  }
  return os << "]";
}

template <typename U>
struct get_default<DafnySequence<U> > {
  static DafnySequence<U> call() {
    DafnySequence<U> ret;
    return ret;
  }
};

template <typename U>
bool operator==(const DafnySequence<U> &s0, const DafnySequence<U> &s1) {
    return s0.equals(s1);
}

template <typename U>
bool operator!=(const DafnySequence<U> &s0, const DafnySequence<U> &s1) {
    return !s0.equals(s1);
}

inline std::ostream& operator<<(std::ostream& out, const DafnySequence<char>& val){
    for (size_t i = 0; i < val.size(); i++) {
        out << val.select(i);
    }
    return out;
}

template <typename U>
struct std::hash<DafnySequence<U>> {
    size_t operator()(const DafnySequence<U>& s) const {
        size_t seed = 0;
        for (size_t i = 0; i < s.size(); i++) {
            hash_combine<U>(seed, s.select(i));
        }
        return seed;
    }
};

template <typename U>
struct std::hash<DafnyArray<U>> {
    size_t operator()(const DafnyArray<U>& s) const {
        size_t seed = 0;
        for (size_t i = 0; i < s.size(); i++) {
            hash_combine<U>(seed, s.at(i));
        }
        return seed;
    }
};

/*********************************************************
 *  SETS                                                 *
 *********************************************************/

template <class T>
struct DafnySet {
    DafnySet() {
    }

    DafnySet(const DafnySet<T>& other) {
        set = std::unordered_set<T>(other.set);
    }

    DafnySet(std::initializer_list<T> il) {
        std::unordered_set<T> a_set(il);
        set = a_set;
    }

    static DafnySet<T> Create(std::initializer_list<T> il) {
        DafnySet<T> ret(il);
        return ret;
    }

    static DafnySet<T> empty() {
        return DafnySet();
    }

    bool IsSubsetOf(const DafnySet<T>& other) const {
        if (set.size() > other.set.size()) {
            return false;
        }
        for (const auto& elt:set) {
            if (other.set.find(elt) == other.set.end()) {
                return false;
             }
        }
        return true;
    }

    bool IsProperSubsetOf(const DafnySet<T>& other) {
        return IsSubsetOf(other) && (size() < other.size());
     }

    bool contains(T t) const {
        return set.find(t) != set.end();
    }

    bool disjoint(const DafnySet<T>& other) {
        for (auto const& elt:set) {
            if (other.set.find(elt) != other.set.end()) {
                return false;
            }
        }
        return true;
    }

    DafnySet<T> Union(const DafnySet<T>& other) {
        DafnySet<T> ret = DafnySet(other);
        ret.set.insert(set.begin(), set.end());
        return ret;
    }

    // Returns a DafnySet containing elements only found in the current DafnySet
    DafnySet<T> Difference(const DafnySet<T>& other) {
        DafnySet<T> ret;
        for (auto const& elt:set) {
            if (!other.contains(elt)) {
                ret.set.insert(elt);
            }
        }
        return ret;
    }

    DafnySet<T> Intersection(const DafnySet<T>& other) {
        DafnySet<T> ret;
        for (auto const& elt:set) {
            if (other.set.find(elt) != other.set.end()) {
                ret.set.insert(elt);
            }
        }
        return ret;
    }

    std::unordered_set<T> Elements() {
        return set;
    }

    uint64 size () const { return set.size(); }

    bool isEmpty() const { return set.empty(); }


    bool equals(const DafnySet<T> other) const {
        return IsSubsetOf(other) && other.IsSubsetOf(*this);
    }

    // TODO: toString

    std::unordered_set<T> set;
};

template <typename U>
bool operator==(const DafnySet<U> &s0, const DafnySet<U> &s1) {
    return s0.equals(s1);
}

template <typename U>
bool operator!=(const DafnySet<U> &s0, const DafnySet<U> &s1) {
    return !s0.equals(s1);
}

template <typename U>
inline std::ostream& operator<<(std::ostream& out, const DafnySet<U>& val){
    for (auto const& c:val.set) {
        out << c;
    }
    return out;
}

template <typename U>
struct std::hash<DafnySet<U>> {
    size_t operator()(const DafnySet<U>& s) const {
        size_t seed = 0;
        for (auto const& elt:s.set) {
            hash_combine<U>(seed, elt);
        }
        return seed;
    }
};


#ifdef DAFNY_BIGNUM
/*********************************************************
 *  MULTISETS                                            *
 *********************************************************/

// A Dafny `multiset<T>` (enabled under --bignum). Backed by
// std::unordered_multiset<T>, so multiplicities and set-like operations come
// straight from the STL rather than a hand-rolled structure.
//   * multiplicity(x)  -> m[x]
//   * size()           -> |m|
//   * contains(x)      -> x in m
// Union/Intersection/Difference follow Dafny multiset semantics (per-element
// max/min/truncated-subtraction of multiplicities).
template <class T>
struct DafnyMultiset {
    std::unordered_multiset<T> multiset;

    DafnyMultiset() {}
    DafnyMultiset(const DafnyMultiset<T>& other) {
        multiset = std::unordered_multiset<T>(other.multiset);
    }
    DafnyMultiset(std::initializer_list<T> il) {
        std::unordered_multiset<T> a(il);
        multiset = a;
    }

    static DafnyMultiset<T> Create(std::initializer_list<T> il) {
        DafnyMultiset<T> ret(il);
        return ret;
    }

    static DafnyMultiset<T> empty() {
        return DafnyMultiset();
    }

    // Multiplicity of x: m[x].
    uint64 multiplicity(T t) const {
        return multiset.count(t);
    }

    // m[x := n]: return a copy in which x has multiplicity EXACTLY n (matching
    // Dafny's IMultiSet.Update — set, not add). Remove all existing copies of x,
    // then insert n of them.
    DafnyMultiset<T> update(T t, uint64 n) const {
        DafnyMultiset<T> ret(*this);
        ret.multiset.erase(t);
        for (uint64 i = 0; i < n; i++) { ret.multiset.insert(t); }
        return ret;
    }

    // |m|: total number of elements (counting duplicates).
    uint64 size() const { return multiset.size(); }

    bool isEmpty() const { return multiset.empty(); }

    // x in m  <=>  multiplicity(x) > 0
    bool contains(T t) const {
        return multiset.find(t) != multiset.end();
    }

    // Distinct elements present in this multiset (each once).
    std::unordered_set<T> keys() const {
        std::unordered_set<T> ks;
        for (auto const& e : multiset) { ks.insert(e); }
        return ks;
    }

    // Multiset union (Dafny `+`): multiplicity = SUM of the two.
    DafnyMultiset<T> Union(const DafnyMultiset<T>& other) const {
        DafnyMultiset<T> ret;
        for (auto const& e : multiset) { ret.multiset.insert(e); }
        for (auto const& e : other.multiset) { ret.multiset.insert(e); }
        return ret;
    }

    // Multiset intersection: multiplicity = min of the two.
    DafnyMultiset<T> Intersection(const DafnyMultiset<T>& other) const {
        DafnyMultiset<T> ret;
        for (auto const& k : keys()) {
            uint64 a = multiplicity(k), b = other.multiplicity(k);
            uint64 m = a < b ? a : b;
            for (uint64 i = 0; i < m; i++) { ret.multiset.insert(k); }
        }
        return ret;
    }

    // Multiset difference: truncated subtraction of multiplicities.
    DafnyMultiset<T> Difference(const DafnyMultiset<T>& other) const {
        DafnyMultiset<T> ret;
        for (auto const& k : keys()) {
            uint64 a = multiplicity(k), b = other.multiplicity(k);
            uint64 m = a > b ? a - b : 0;
            for (uint64 i = 0; i < m; i++) { ret.multiset.insert(k); }
        }
        return ret;
    }

    bool IsSubsetOf(const DafnyMultiset<T>& other) const {
        for (auto const& k : keys()) {
            if (multiplicity(k) > other.multiplicity(k)) { return false; }
        }
        return true;
    }

    bool IsSupersetOf(const DafnyMultiset<T>& other) const {
        return other.IsSubsetOf(*this);
    }

    bool IsProperSubsetOf(const DafnyMultiset<T>& other) const {
        return IsSubsetOf(other) && size() < other.size();
    }

    bool IsProperSupersetOf(const DafnyMultiset<T>& other) const {
        return other.IsProperSubsetOf(*this);
    }

    bool IsDisjointFrom(const DafnyMultiset<T>& other) const {
        for (auto const& k : keys()) {
            if (other.multiplicity(k) > 0) { return false; }
        }
        return true;
    }

    bool equals(const DafnyMultiset<T>& other) const {
        return IsSubsetOf(other) && other.IsSubsetOf(*this);
    }
};

template <typename U>
bool operator==(const DafnyMultiset<U> &s0, const DafnyMultiset<U> &s1) {
    return s0.equals(s1);
}

template <typename U>
bool operator!=(const DafnyMultiset<U> &s0, const DafnyMultiset<U> &s1) {
    return !s0.equals(s1);
}

// Print like the other Dafny back-ends: "multiset{a, b, b, ...}" listing every
// element (with repetitions), grouped so equal elements are adjacent.
template <typename U>
inline std::ostream& operator<<(std::ostream& out, const DafnyMultiset<U>& val){
    out << "multiset{";
    bool first = true;
    for (auto const& k : val.keys()) {
        uint64 m = val.multiplicity(k);
        for (uint64 i = 0; i < m; i++) {
            if (!first) { out << ", "; }
            dafny_print_to(out, k);
            first = false;
        }
    }
    out << "}";
    return out;
}

template <typename U>
struct std::hash<DafnyMultiset<U>> {
    size_t operator()(const DafnyMultiset<U>& s) const {
        // Combine element hashes with a commutative fold (XOR of per-element hashes,
        // each mixed with its multiplicity) so the result does not depend on the
        // unordered_multiset's iteration order: equal multisets must hash equally.
        size_t h = 0;
        for (auto const& k : s.keys()) {
            size_t eh = std::hash<U>()(k);
            h ^= eh * 0x9e3779b97f4a7c15ULL + s.multiplicity(k);
        }
        return h;
    }
};
#endif  // DAFNY_BIGNUM


/*********************************************************
 *  MAPS                                                 *
 *********************************************************/

template <class K, class V>
struct DafnyMap {
    DafnyMap() {
    }

    DafnyMap(const DafnyMap<K,V>& other) {
        map = std::unordered_map<K,V>(other.map);
    }

    DafnyMap(std::initializer_list<std::pair<const K,V>> il) {
        std::unordered_map<K,V> a_map(il);
        map = a_map;
    }

    static DafnyMap<K,V> Create(std::initializer_list<std::pair<const K,V>> il) {
        DafnyMap<K,V> ret(il);
        return ret;
    }

    static DafnyMap<K,V> empty() {
        return DafnyMap();
    }

    bool contains(K t) const {
        return map.find(t) != map.end();
    }

    V get(K key) const {
        return map.find(key)->second;
    }

    DafnyMap<K, V> update(K k, V v) {
        DafnyMap<K,V> ret(*this);
        auto ptr = ret.map.find(k);
        if (ptr == ret.map.end()) {
            ret.map.emplace(k, v);
        } else {
            ptr->second = v;
        }
        return ret;
    }

    DafnyMap<K, V> Merge(DafnyMap<K, V> other) {
        DafnyMap<K,V> ret(other);
        for (const auto& kv : map) {
            auto ptr = other.map.find(kv.first);
            if (ptr == other.map.end()) {
                ret.map.emplace(kv.first, kv.second);
            }
        }
        return ret;
    }

    DafnyMap<K, V> Subtract(DafnySet<K> keys) {
        DafnyMap<K,V> ret = DafnyMap();
        for (const auto& kv : map) {
            if (!keys.contains(kv.first)) {
                ret.map.emplace(kv.first, kv.second);
            }
        }
        return ret;
    }

    uint64 size () const { return map.size(); }

    bool isEmpty() const { return map.empty(); }

    DafnySet<K> dafnyKeySet() {
        DafnySet<K> ret;
        for (const auto& kv : map) {
            ret.set.insert(kv.first);
        }
        return ret;
    }

    DafnySet<V> dafnyValues() {
        DafnySet<V> ret;
        for (const auto& kv : map) {
            ret.set.insert(kv.second);
        }
        return ret;
    }


    bool equals(const DafnyMap<K,V> other) const {
        if (map.size() != other.size()) { return false; }

        for (const auto& kv : map) {
            auto ptr = other.map.find(kv.first);
            if (ptr == other.map.end()) { return false; }
            if (ptr->second != kv.second) { return false; }
        }
        return true;
    }

    // TODO: hash
    // TODO: toString

    std::unordered_map<K,V> map;
};


template <typename T, typename U>
bool operator==(const DafnyMap<T,U> &s0, const DafnyMap<T,U> &s1) {
    return s0.equals(s1);
}

template <typename T, typename U>
bool operator!=(const DafnyMap<T,U> &s0, const DafnyMap<T,U> &s1) {
    return !s0.equals(s1);
}

template <typename T, typename U>
inline std::ostream& operator<<(std::ostream& out, const DafnyMap<T,U>& val){
    for (auto const& kv:val.map) {
        out << "(" << kv.first << " -> " << kv.second << ")";
    }
    return out;
}

template <typename T, typename U>
struct std::hash<DafnyMap<T,U>> {
    size_t operator()(const DafnyMap<T,U>& s) const {
        size_t seed = 0;
        for (auto const& kv:s.map) {
            hash_combine<T>(seed, kv.first);
            hash_combine<U>(seed, kv.second);
        }
        return seed;
    }
};

DafnySequence<DafnySequence<char>> dafny_get_args(int argc, char* argv[]) {
  DafnySequence<DafnySequence<char>> dafnyArgs((uint64)argc);
  for(int i = 0; i < argc; i++) {
    std::string s = argv[i];
    dafnyArgs.start[i] = DafnySequenceFromString(s);
  }
  return dafnyArgs;
}
