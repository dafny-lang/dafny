#pragma once

#include <iostream>
#include <string>
#include <vector>
#include <unordered_set>
#include <unordered_map>

using namespace std;

class _dafny {
  public:
    static void Print(string s) { cout << s << endl; }
};


typedef unsigned char       uint8;
typedef unsigned short     uint16;
typedef unsigned long      uint32;
typedef unsigned long long uint64;

typedef char       int8;
typedef short     int16;
typedef long      int32;
typedef long long int64;

/*********************************************************
 *  UTILITIES                                            *
 *********************************************************/

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

/*********************************************************
 *  DEFAULTS                                             *
 *********************************************************/

template <typename T>
T get_default(T*);

template <>
bool get_default<bool>(bool*) { return true; }
template <>
int get_default<int>(int*) { return 0; }
template <>
unsigned int get_default<unsigned int>(unsigned int*) { return 0; }
template <>
unsigned long get_default<unsigned long>(unsigned long*) { return 0; }
template <>
unsigned long long get_default<unsigned long long>(unsigned long long*) { return 0; }

/*********************************************************
 *  TUPLES                                               *
 *********************************************************/

template <typename T0, typename T1>
struct Tuple2 {
  T0 t0;
  T1 t1;

  Tuple2() { 
    t0 = get_default<T0>(NULL);
    t1 = get_default<T0>(NULL);
  }
  
  Tuple2(T0 _t0, T1 _t1) { 
    t0 = _t0;
    t1 = _t1;
  }

  T0 get_0() { return t0; }
  T1 get_1() { return t1; }
};

/*********************************************************
 *  SEQUENCES                                            *
 *********************************************************/
template <class T>
struct DafnySequence {
    DafnySequence() {    
    }
    
    DafnySequence(uint64 len) {
        vector<T> a_seq(len);
        seq = a_seq;
    }
    
    DafnySequence<char>(string s) {
        seq = vector<char>(s.begin(), s.end());        
    }
    
    DafnySequence(const DafnySequence<T>& other) {
        seq = vector<T>(other.seq);        
    }
    
    DafnySequence(shared_ptr<vector<T>> arr) {
        vector<T> a_seq(*arr);
        seq = a_seq;
    }
    
    DafnySequence(initializer_list<T> il) {
        vector<T> a_seq(il);
        seq = a_seq;
    }
    
    static DafnySequence<T> SeqFromArray(shared_ptr<vector<T>> arr) {
        DafnySequence<T> ret(arr);         
        return ret;
    }

    static DafnySequence<T> Create(initializer_list<T> il) {
        DafnySequence<T> ret(il);
        return ret;            
    }
    
    // TODO: isPrefixOf, isPropoerPrefixOf
    
    DafnySequence<T> concatenate(DafnySequence<T> other) {
        DafnySequence<T> ret(seq.size() + other.seq.size());
        for (uint64 i = 0; i < seq.size(); i++) {
            ret.seq[i] = seq[i];
        }            
        for (uint64 i = 0; i < other.seq.size(); i++) {
            ret.seq[i + seq.size()] = other.seq[i];
        }
        return ret; 
    }
    
    T select(uint64 i) {
        return seq[i];
    }
    
    uint64 length () { return seq.size(); }
    
    DafnySequence<T> update(uint64 i, T t) {
        DafnySequence<T> ret(*this);
        ret.seq[i] = t;
        return ret;
    }
    
    bool contains(T t) {
        for (uint64 i = 0; i < seq.size(); i++) {
            if (seq[i] == t) {
                return true;
            }
        }
        return false;
    }
    
    // Returns the subsequence of values [lo..hi)
    DafnySequence<T> subsequence(uint64 lo, uint64 hi) {
        DafnySequence<T> ret(hi - lo);
        for (uint64 i = 0; i < ret.seq.size(); i++) {
            ret.seq[i] = seq[i + lo];
        }            
        return ret;
    }
    
    // Returns the subsequence of values [lo..length())
    DafnySequence<T> drop(uint64 lo) {
        return subsequence(lo, seq.size());
    }
    
    // Returns the subsequence of values [0..hi)
    DafnySequence<T> take(uint64 hi) {
        return subsequence(0, hi);
    }
    
    // TODO: slice

    bool equals(const DafnySequence<T> other) const {        
        return seq == other.seq;
    }
    
    
    // TODO: toString
    
    vector<T> seq;
};

template <typename U>
bool operator==(const DafnySequence<U> &s0, const DafnySequence<U> &s1) {
    return s0.equals(s1);
}

inline ostream& operator<<(ostream& out, const DafnySequence<char>& val){
    for (auto const& c:val.seq) {
        out << c;
    }    
    return out;
}

template <typename U>
struct hash<DafnySequence<U>> {
    size_t operator()(const DafnySequence<U>& s) const {
        size_t seed = 0;
        for (size_t i = 0; i < s.seq.size(); i++) {      
            hash_combine(seed, s.seq[i]);
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
        set = unordered_set<T>(other.set);        
    }

    DafnySet(initializer_list<T> il) {
        unordered_set<T> a_set(il);
        set = a_set;
    }
       
    static DafnySet<T> Create(initializer_list<T> il) {
        DafnySet<T> ret(il);
        return ret;            
    }
    
    static DafnySet<T> empty() {
        return DafnySet();
    }
    
    bool IsSubsetOf(const DafnySet<T>& other) {
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
        // This attempts to sort the elements (which then requires defining an ordering on DafnySeq, DafnySet, etc.)
        //set_difference(set.begin(), set.end(), other.set.begin(), other.set.end(), inserter(ret.set, ret.set.end()));
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
    
    unordered_set<T> Elements() {
        return set;
    }

    uint64 size () const { return set.size(); }
    
    bool isEmpty() const { return set.empty(); }
    
    
    bool equals(DafnySet<T> other) {        
        return IsSubsetOf(other) && other.IsSubsetOf(*this);
    }

    // TODO: toString
    
    unordered_set<T> set;
};

template <typename U>
bool operator==(DafnySet<U> &s0, DafnySet<U> &s1) {
    return s0.equals(s1);
}

template <typename U>
inline ostream& operator<<(ostream& out, const DafnySet<U>& val){
    for (auto const& c:val.set) {
        out << c;
    }    
    return out;
}

template <typename U>
struct hash<DafnySet<U>> {
    size_t operator()(const DafnySet<U>& s) const {
        size_t seed = 0;
        for (auto const& elt:s.set) {      
            hash_combine(seed, elt);
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
        map = unordered_map<K,V>(other.map);        
    }

    DafnyMap(initializer_list<pair<const K,V>> il) {
        unordered_map<K,V> a_map(il);
        map = a_map;
    }
       
    static DafnyMap<K,V> Create(initializer_list<pair<const K,V>> il) {
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
    
    /*
    bool disjoint(const DafnyMap<K,V>& other) {
        for (auto const& elt:map) {
            if (other.find(elt) != other.map.end()) {
                return false;
            }
        }
        return true;
    }
    
    DafnyMap<K,V> Union(const DafnyMap<K,V>& other) {
        DafnyMap<K,V> ret = DafnyMap(other);
        ret.map.insert(map.begin(), map.end());
        return ret;            
    }
    
    
    // Returns a DafnyMap containing elements only found in the current DafnyMap
    DafnyMap<K,V> Difference(const DafnyMap<K,V>& other) {
        DafnyMap<K,V> ret;
        for (auto const& elt:map) {
            if (!other.contains(elt)) {
                ret.map.insert(elt);
            }
        }
        // K,Vhis attempts to sort the elements (which then requires defining an ordering on DafnySeq, DafnyMap, etc.)
        //map_difference(map.begin(), map.end(), other.map.begin(), other.map.end(), inserter(ret.map, ret.map.end()));
        return ret;            
    }
    
    DafnyMap<K,V> Intersection(const DafnyMap<K,V>& other) {
        DafnyMap<K,V> ret;
        for (auto const& elt:map) {
            if (other.map.find(elt) != other.map.end()) {
                ret.map.insert(elt);                
            }
        }
        return ret;            
    }
    */

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
    
    
    bool equals(DafnyMap<K,V> other) {
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
    
    unordered_map<K,V> map;
};


template <typename T, typename U>
bool operator==(DafnyMap<T,U> &s0, DafnyMap<T,U> &s1) {
    return s0.equals(s1);
}

template <typename T, typename U>
inline ostream& operator<<(ostream& out, const DafnyMap<T,U>& val){
    for (auto const& kv:val.map) {
        out << "(" << kv.first << " -> " << kv.second << ")";
    }    
    return out;
}

template <typename T, typename U>
struct hash<DafnyMap<T,U>> {
    size_t operator()(const DafnyMap<T,U>& s) const {
        size_t seed = 0;
        for (auto const& kv:s.map) {      
            hash_combine(seed, kv.first);
            hash_combine(seed, kv.second);
        }
        return seed; 
    }
};

