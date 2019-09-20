#include <iostream>
#include <string>

using namespace std;

class _dafny {
  public:
    static void Print(string s) { cout << s << endl; }
};

typedef unsigned long long uint64;

template <class T>
struct DafnySequence {
    DafnySequence() {
        len = 0;
        seq = nullptr;        
    }
    
    DafnySequence(uint64 length) {
        len = length;
        seq = make_shared<T[]>(new T[len]);
    }

    DafnySequence(DafnySequence<T>& other) {        
        seq = make_shared<T[]>(new T[other.len]);
        len = other.len;
        memcpy((void*)seq.get(), (void*)other.seq.get(), len * sizeof(T));
    }
    
    /*
    // Added this overload to avoid error:
    //  copy assignment operator of 'DafnySequence<unsigned int>' is implicitly deleted 
    //   because field 'seq' has a deleted copy assignment operator
    DafnySequence& operator=(const DafnySequence<T>& other) {
        if (&other == this) {
            return *this;
        }
        if (len != other.len) {  // Avoid our existing allocation if we can
            seq.reset(new T[other.len]);
        }
        copy(&other.seq[0], &other.seq[0] + min(len, other.len), &seq[0]);
        return *this;
    }
    */
    
    static DafnySequence<T> SeqFromArray(uint64 length, T arr[]) {
        DafnySequence<T> ret(length); 
        for (uint64 i = 0; i < length; i++) {
            ret.seq.get()[i] = arr[i];
        }
        return ret;
    }
    
    static DafnySequence<T> Create(uint64 length, T(*init)(uint64)) {
        DafnySequence<T> ret(length);        
        for (uint64 i = 0; i < length; i++) {
            ret.seq.get()[i] = init(i);
        }
        return ret;            
    }
    
    /////////////////////////////////////////////////////////////////////////////////////////////
    // WARNING: Not for ordinary use; mutates in place.  Only use with EmitCollectionDisplay
    /////////////////////////////////////////////////////////////////////////////////////////////
    DafnySequence<T> stuff(uint64 i, T t) {
        seq[i] = t;
        return this;
    }
    
    /*
    ~DafnySequence() {
        delete [] seq;
    }
    */
    
    /*
    static DafnySequence<char> asString(string s) {
        //return mk_shared_ptr DafnySequence
    }
    */
    
    // TODO: isPrefixOf, isPropoerPrefixOf
    
    DafnySequence<T> concatenate(DafnySequence<T> other) {
        DafnySequence<T> ret(len + other.len);
        for (uint64 i = 0; i < len; i++) {
            ret.seq[i] = seq[i];
        }            
        for (uint64 i = 0; i < other.len; i++) {
            ret.seq[i + len] = other.seq[i];
        }
        return ret; 
    }
    
    T select(uint64 i) {
        return seq[i];
    }
    
    uint64 length () { return len; }
    
    DafnySequence<T> update(uint64 i, T t) {
        DafnySequence<T> ret(this);
        ret.seq[i] = t;
        return ret;
    }
    
    ///////////////////////////////////////////////////////
    // WARNING: May break when comparing references!?
    ///////////////////////////////////////////////////////
    bool contains(T t) {
        for (uint64 i = 0; i < len; i++) {
            if (seq[i] == t) {
                return true;
            }
        }
        return false;
    }
    
    // Returns the subsequence of values [lo..hi)
    DafnySequence<T> subsequence(uint64 lo, uint64 hi) {
        DafnySequence<T> ret(hi - lo);
        for (uint64 i = 0; i < ret.len; i++) {
            ret.seq[i] = seq[i + lo];
        }            
        return ret;
    }
    
    // Returns the subsequence of values [lo..length())
    DafnySequence<T> drop(uint64 lo) {
        return subsequence(lo, len);
    }
    
    // Returns the subsequence of values [0..hi)
    DafnySequence<T> take(uint64 hi) {
        return subsequence(0, hi);
    }
    
    // TODO: slice
    
    friend bool operator==(DafnySequence<T> s0, DafnySequence<T> s1);
    
    bool equals(DafnySequence<T> other) {
        return *this == other;
    }
    
    // TODO: hash
    // TODO: toString
    
    int len;
    shared_ptr<T[]> seq;
};

template <typename T>
bool operator==(DafnySequence<T> &s0, DafnySequence<T> &s1) {
    if (s0.length() != s1.length()) {
        return false;
    }
    for (uint64 i = 0; i < s0.length(); i++) {
        if (s0.select(i) != s1.select(i)) {
            return false;
        }
    }
    return true;
}
