#pragma once

using namespace std;

typedef unsigned long long uint64;

namespace Extern {

  template <typename T>
  static shared_ptr<vector<T>> newArrayFill(uint64 size, T v) {
    shared_ptr<vector<T>> ret = make_shared<vector<T>>(size);
    for (uint64 i = 0; i < size; i++) {
      (*ret)[i] = v;
    }
    return ret;
  }
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
