#pragma once

#include <iostream>
#include <string>
#include <vector>
#include <unordered_set>

using namespace std;

class _dafny {
  public:
    static void Print(string s) { cout << s << endl; }
};

typedef unsigned long long uint64;

// using boost::hash_combine
template <class T>
inline void hash_combine(std::size_t& seed, T const& v)
{
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

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

    uint64 size () const { return set.size(); }
    
    bool isEmpty() const { return set.empty(); }
    
    
    bool equals(DafnySet<T> other) {        
        return IsSubsetOf(other) && other.IsSubsetOf(*this);
    }
    
    // TODO: hash
    // TODO: toString
    
    unordered_set<T> set;
};

template <typename U>
bool operator==(DafnySet<U> &s0, DafnySet<U> &s1) {
    return s0.equals(s1);
}

inline ostream& operator<<(ostream& out, const DafnySet<unsigned int>& val){
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
