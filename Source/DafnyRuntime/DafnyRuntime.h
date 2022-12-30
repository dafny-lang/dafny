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
T* global_empty_ptr = new T[0];

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
            if (other.find(elt) != other.set.end()) {
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
