namespace ExternalMath {
    
    using System;
    using System.Numerics;  // For BigInteger
    using Dafny;
    public static class __default
    {
        public static BigRational Sqrt(BigRational x)
        {
            double xd = (double)x.num / (double)x.den;
            double res = Math.Sqrt(xd);
            return new BigRational(res);
        }
    }
}

