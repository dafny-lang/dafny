using System;
using Dafny;  // BigRational is defined here

using System;
using System.Numerics;  // For BigInteger
using Dafny;

namespace ExternalMath {
    public static class __default {
        public static BigRational Sqrt(BigRational x) {
            double xd = (double)x.num / (double)x.den;  
            double res = Math.Sqrt(xd);
            return new BigRational(res);
        }
    }
}

