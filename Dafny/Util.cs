using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny {
  class Util
  {
     public delegate string ToString<T>(T t);
     public static string Comma<T>(string comma, IEnumerable<T> l, ToString<T> f) {
       string res = "";
       string c = "";
       foreach(var t in l) {
         res += c + f(t);
         c = comma;
       }
       return res;
     }
  }
}
