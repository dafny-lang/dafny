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

template <class T>
struct DafnySequence {
    DafnySequence() {    
    }
    
    DafnySequence(uint64 len) {
        vector<T> a_seq(len);
        seq = a_seq;
    }
    
    DafnySequence(const DafnySequence<T>& other) {
        seq = vector(other.seq);        
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

    bool equals(DafnySequence<T> other) {        
        return seq == other.seq;
    }
    
    // TODO: hash
    // TODO: toString
    
    vector<T> seq;
};

template <typename U>
bool operator==(DafnySequence<U> &s0, DafnySequence<U> &s1) {
    return s0.equals(s1);
}



template <class T>
struct DafnySet {
    DafnySet() {    
    }
    
    DafnySet(const DafnySet<T>& other) {
        set = unordered_set(other.set);        
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
    
    bool isSubsetOf(const DafnySet<T>& other) {
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

    bool isProperSubsetOf(const DafnySet<T>& other) {
        return isSubsetOf(other) && (size() < other.size());
     }

    bool contains(T t) {
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
    
    DafnySet<T> set_union(const DafnySet<T>& other) {
        DafnySet<T> ret = DafnySet(other);
        ret.set.insert(set.first, set.last);
        return ret;            
    }
    
    // Returns a DafnySet containing elements only found in the current DafnySet
    DafnySet<T> difference(const DafnySet<T>& other) {
        DafnySet<T> ret = DafnySet(*this);
        ret.set.remove(other.set.first, other.set.last);
        return ret;            
    }
    
    DafnySet<T> intersection(const DafnySet<T>& other) {
        DafnySet<T> ret;
        for (auto const& elt:set) {
            if (other.set.find(elt) != other.set.end()) {
                ret.set.insert(elt);                
            }
        }
        return ret;            
    }

    uint64 size () { return set.size(); }
    
    bool isEmpty() { return set.empty(); }
    
    
    bool equals(DafnySet<T> other) {        
        return isSubsetOf(other) && other.isSubsetOf(*this);
    }
    
    // TODO: hash
    // TODO: toString
    
    unordered_set<T> set;
};

template <typename U>
bool operator==(DafnySet<U> &s0, DafnySet<U> &s1) {
    return s0.equals(s1);
}