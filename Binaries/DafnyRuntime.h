#include <iostream>
#include <string>

using namespace std;

class _dafny {
  public:
    static void Print(string s) { cout << s << endl; }
};

typedef unsigned long long uint64;

template <class T>
class DafnySequence {
    public:
        DafnySequence() {
            seq = NULL;
            len = 0;
        }
        
        DafnySequence(std::shared_ptr<DafnySequence<T> > other) {
            assert(other != nullptr);
            this->seq = new T[other->len];
            this->len = other->len;
            memcpy(this->seq, other->seq, this->len * sizeof(T));
        }
        
        static std::shared_ptr<DafnySequence<T> > Create(uint64 length, T(*init)(int)) {
            std::shared_ptr<DafnySequence<T> > ret = std::make_shared<DafnySequence<T> >();
            ret->seq = new T[length];
            ret->len = length;
            for (uint64 i = 0; i < length; i++) {
                ret->seq[i] = init(i);
            }
            return ret;            
        }
        
        /////////////////////////////////////////////////////////////////////////////////////////////
        // WARNING: Not for ordinary use; mutates in place.  Only use with EmitCollectionDisplay
        /////////////////////////////////////////////////////////////////////////////////////////////
        std::shared_ptr<DafnySequence<T> > stuff(uint64 i, T t) {
            seq[i] = t;
            return this;
        }
        
        ~DafnySequence() {
            delete [] seq;
        }
        
        /*
        static std::shared_ptr<DafnySequence<char> > asString(string s) {
            return std::mk_shared_ptr DafnySequence
        }
        */
        
        // TODO: isPrefixOf, isPropoerPrefixOf
        
        std::shared_ptr<DafnySequence<T> > concatenate(std::shared_ptr<DafnySequence<T> > other) {
            std::shared_ptr<DafnySequence<T> > ret = std::make_shared<DafnySequence<T> >();
            ret->len = len + other->len;
            ret->seq = new T[ret->len];
            for (uint64 i = 0; i < len; i++) {
                ret->seq[i] = seq[i];
            }            
            for (uint64 i = 0; i < other->len; i++) {
                ret->seq[i + len] = other->seq[i];
            }
            return ret; 
        }
        
        T select(uint64 i) {
            return seq[i];
        }
        
        uint64 length () { return len; }
        
        std::shared_ptr<DafnySequence<T> > update(uint64 i, T t) {
            std::shared_ptr<DafnySequence<T> > ret = std::make_shared<DafnySequence<T> >(this);
            ret->seq[i] = t;
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
        std::shared_ptr<DafnySequence<T> > subsequence(uint64 lo, uint64 hi) {
            std::shared_ptr<DafnySequence<T> > ret = std::make_shared<DafnySequence<T> >();
            ret->len = hi - lo;
            ret->seq = new T[len];
            for (uint64 i = 0; i < ret->len; i++) {
                ret->seq[i] = seq[i + lo];
            }            
            return ret;
        }
        
        // Returns the subsequence of values [lo..length())
        std::shared_ptr<DafnySequence<T> > drop(uint64 lo) {
            return subsequence(lo, len);
        }
        
        // Returns the subsequence of values [0..hi)
        std::shared_ptr<DafnySequence<T> > take(uint64 hi) {
            return subsequence(0, hi);
        }
        
        // TODO: slice
        
        friend bool operator==(DafnySequence<T> s0, DafnySequence<T> s1);
        
        // TODO: hash
        // TODO: toString
        
     

    private:
        int len;
        T* seq;
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
