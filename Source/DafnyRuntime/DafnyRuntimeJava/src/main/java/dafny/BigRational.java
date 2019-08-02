package dafny;

import java.math.BigInteger;

public class BigRational {
    //TODO: Implement default method, and disallow 0 for den
    public static final BigRational ZERO = new BigRational(0);

    BigInteger num, den; // invariant 1 <= den || (num == 0 && den == 0)

    @Override
    public String toString() {
        if (den.equals(BigInteger.ONE) || num.equals(BigInteger.ZERO)) {
            return num + ".0";
        } else {
            Tuple2<Boolean, Integer> t = IsPowerOf10(den);
            Integer log10 = t.dtor__1();
            if (t.dtor__0()) {
                String sign;
                String digits;
                if (num.signum() < 0) {
                    sign = "-";
                    digits = (num.negate()).toString();
                } else {
                    sign = "";
                    digits = num.toString();
                }

                if (log10 < digits.length()) {
                    int n = digits.length() - log10;
                    return sign + digits.substring(0, n) + "." + digits.substring(n);
                } else {
                    int z = log10 - digits.length();
                    StringBuffer outputBuffer = new StringBuffer(z);
                    for (int i = 0; i < z; i++) {
                        outputBuffer.append("0");
                    }
                    return sign + "0." + outputBuffer.toString() + digits;
                }
            } else {
                return "(" + num + ".0 / " + den + ".0)";
            }
        }
    }

    public Tuple2<Boolean, Integer> IsPowerOf10(BigInteger x) {
        int log10 = 0;
        if (x.equals(BigInteger.ZERO)) {
            return new Tuple2<>(false, log10);
        }

        while (true) {
            // invariant: x != 0 && x * 10^log10 == old(x)
            if (x.equals(BigInteger.ONE)) {
                return new Tuple2<>(true, log10);
            } else if (x.mod(BigInteger.TEN).equals(BigInteger.ZERO)) {
                log10++;
                x = x.divide(BigInteger.TEN);
            } else {
                return new Tuple2<>(false, log10);
            }
        }
    }

    public BigRational() {
        this(0, 1);
    }

    public BigRational(int n) {
        this(n, 1);
    }

    public BigRational(int n, int d) {
        this(BigInteger.valueOf(n), BigInteger.valueOf(d));
    }

    public BigRational(BigInteger n, BigInteger d) {
        assert !d.equals(BigInteger.ZERO) : "Precondition Failure";
        // ensures 1 <= den
        if (d.compareTo(BigInteger.ZERO) < 0) {
            num = n.negate();
            den = d.negate();
        } else {
            num = n;
            den = d;
        }
    }

    public BigInteger ToBigInteger() {
        if (num.equals(BigInteger.ZERO) || den.equals(BigInteger.ONE)) {
            return num;
        } else if (0 < num.signum()) {
            return num.divide(den);
        } else {
            // Dafny uses Euclidean Division, so divide will not always satisfy the preconditions of
            // num = (den * BigInteger) + remainder
            // when the numerator is negative.
            return (num.subtract(den).add(BigInteger.ONE)).divide(den);
        }
    }

    // In order to compare, add, and subtract fractions, they must have the same denominator. This computes the
    // common denominator of the fractions, and returns a tuple containing:
    // aa: the numerator for a when multiplied by the common denominator
    // bb: the numerator for b when multiplied by the common denominator
    // dd: the common denominator
    private static Tuple3<BigInteger, BigInteger, BigInteger> Normalize(BigRational a, BigRational b) {
        BigInteger aa, bb, dd;
        if (a.num.equals(BigInteger.ZERO)) {
            aa = a.num;
            bb = b.num;
            dd = b.den;
        } else if (b.num.equals(BigInteger.ZERO)) {
            aa = a.num;
            dd = a.den;
            bb = b.num;
        } else {
            BigInteger gcd = a.den.gcd(b.den);
            BigInteger xx = a.den.divide(gcd);
            BigInteger yy = b.den.divide(gcd);
            // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
            aa = a.num.multiply(yy);
            bb = b.num.multiply(xx);
            // 1 <= a.den * yy -> 1 <= dd
            dd = a.den.multiply(yy);
        }
        return new Tuple3<>(aa, bb, dd);
    }

    public int compareTo(BigRational that) {
        // simple things first
        int asign = this.num.signum();
        int bsign = that.num.signum();
        if (asign < 0 && 0 <= bsign) {
            return -1;
        } else if (asign <= 0 && 0 < bsign) {
            return -1;
        } else if (bsign < 0 && 0 <= asign) {
            return 1;
        } else if (bsign <= 0 && 0 < asign) {
            return 1;
        }

        BigInteger aa, bb, dd;
        Tuple3<BigInteger, BigInteger, BigInteger> n = Normalize(this, that);
        return n.dtor__0().compareTo(n.dtor__1());
    }

    @Override
    public int hashCode() {
        return num.hashCode() + 29 * den.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        BigRational o = (BigRational) obj;
        Tuple3<BigInteger, BigInteger, BigInteger> t = Normalize(this, o);
        return t.dtor__0().equals(t.dtor__1());
    }

    public static BigRational add(BigRational a, BigRational b) {
        Tuple3<BigInteger, BigInteger, BigInteger> t = Normalize(a, b);
        return new BigRational(t.dtor__0().add(t.dtor__1()), t.dtor__2());
    }

    public static BigRational subtract(BigRational a, BigRational b) {
        Tuple3<BigInteger, BigInteger, BigInteger> t = Normalize(a, b);
        return new BigRational(t.dtor__0().subtract(t.dtor__1()), t.dtor__2());
    }

    public static BigRational negate(BigRational a) {
        return new BigRational(a.num.negate(), a.den);
    }

    public static BigRational multiply(BigRational a, BigRational b) {
        return new BigRational(a.num.multiply(b.num), a.den.multiply(b.den));
    }

    public static BigRational divide(BigRational a, BigRational b) {
        BigRational bReciprocal;
        if (0 < b.num.signum()) {
            bReciprocal = new BigRational(b.den, b.num);
        } else {
            // We track the sign of the rational in the numerator, so ensure that the numerator of the reciprocal
            // has the sign of rational.
            bReciprocal = new BigRational(b.den.negate(), b.num.negate());
        }

        return multiply(a, bReciprocal);
    }

    public BigRational add(BigRational b) {
        return add(this, b);
    }

    public BigRational subtract(BigRational b) {
        return subtract(this, b);
    }

    public BigRational negate() {
        return new BigRational(num.negate(), den);
    }

    public BigRational multiply(BigRational b) {
        return multiply(this, b);
    }

    public BigRational divide(BigRational b) {
        return divide(this, b);
    }
}
