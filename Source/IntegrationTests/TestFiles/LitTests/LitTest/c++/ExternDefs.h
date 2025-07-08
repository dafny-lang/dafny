#pragma once

using namespace std;

typedef uint64_t uint64;

namespace Extern {
  struct state {
    uint64 u;
  };

  struct state get_state_default() {
    struct state ret;
    ret.u = 22;
    return ret;
  }

  template <typename T>
  static DafnyArray<T> newArrayFill(uint64 size, T v) {
    DafnyArray<T> ret = DafnyArray<T>::New(size);
    for (uint64 i = 0; i < size; i++) {
      ret.at(i) = v;
    }
    return ret;
  }

  class ExternClass {
    public:
    bool my_method0(uint64 a) { (void)a; return true; }
    bool my_method1(uint64 c) { (void)c; return false; }
  };

  class ExternClass2 {
    public:
      ExternClass2(uint64 x) { (void)x; }
  };


  uint64 Caller(uint64 (*inc)(uint64), uint64 x) {
    return inc(x);
  }

  template <typename A>
  A GenericCaller(A (*inc)(A), A x) {
    return inc(x);
  }

  template <typename A>
  class GenericClass {
    public:
    GenericClass(A (*inc)(A), A x) { a = inc(x); }
    A get() { return a; }
    private:
    A a;
  };
/*
class __default {

  public:
  template <typename T>
  static shared_ptr<vector<T>> newArrayFill(uint64 size, T v) {
    shared_ptr<vector<T>> ret = make_shared<vector<T>>(size);
    for (uint64 i = 0; i < size; i++) {
      ret[i] = v;
    }
    return ret;
  }
};*/
}
