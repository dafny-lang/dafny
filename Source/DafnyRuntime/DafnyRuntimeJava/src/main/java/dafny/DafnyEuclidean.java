package dafny;

import java.math.BigInteger;

public class DafnyEuclidean {
    // Properties of Euclidean Division, as referenced in post conditions
    // quotient >= 0 if sign(a) = sign(b) else quotient <= 0
    // remainder is always positive
    // a = quotient*b + remainder
    // there are no max values for these operations, but casting to unsigned is required if b is the MIN_VALUE of a
    // given type because there will be overflow. Since this is division, the return value for all methods will be
    // at a maximum the input value a, which is required to be well defined

    // pre: b != 0
    // post: quotient == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static byte EuclideanDivision(byte a, byte b) {
        assert b != 0 : "Precondition Failure";
        return (byte) EuclideanDivision((int) a, (int) b);
    }

    public static short EuclideanDivision(short a, short b) {
        assert b != 0 : "Precondition Failure";
        return (short) EuclideanDivision((int) a, (int) b);
    }

    public static int EuclideanDivision(int a, int b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            if (0 <= b) {
                // +a +b: a/b
                return a / b;
            } else {
                // +a -b: -(a/(-b))
                // if value of b is 0x80000000, then there is no positive representation for integers, so use uint
                if (b == Integer.MIN_VALUE)
                    return new UInt(a).divide(new UInt(Integer.MIN_VALUE)).value() * -1;
                else return -(a / -b);
            }
        } else {
            if (0 <= b) {
                // -a +b: -((-a-1)/b) - 1
                // minvalue check for a is not necessary because it will always be incremented one, and can
                // be represented in an int
                return -((-(a + 1)) / b) - 1;
            } else {
                // -a -b: ((-a-1)/(-b)) + 1
                if (b == Integer.MIN_VALUE)
                    return new UInt(-(a + 1)).divide(new UInt(Integer.MIN_VALUE)).value() + 1;
                else return (-(a + 1)) / (-b) + 1;
            }
        }
    }

    public static long EuclideanDivision(long a, long b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            if (0 <= b) {
                // +a +b: a/b
                return a / b;
            } else {
                // +a -b: -(a/(-b))
                // if value of b is 0x8000000000000000L, then there is no positive representation for longs,
                // so use ulong
                if (b == Long.MIN_VALUE) return new ULong(a).divide(new ULong(Long.MIN_VALUE)).value() * -1;
                else return -(a / -b);
            }
        } else {
            if (0 <= b) {
                // -a +b: -((-a-1)/b) - 1
                // minvalue check for a is not necessary because it will always be incremented one, and can
                // be represented in a long
                return -((-(a + 1)) / b) - 1;
            } else {
                // -a -b: ((-a-1)/(-b)) + 1
                if (b == Long.MIN_VALUE)
                    return new ULong(-(a + 1)).divide(new ULong(Long.MIN_VALUE)).value() + 1;
                else return (-(a + 1)) / (-b) + 1;
            }
        }
    }

    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
        assert b.compareTo(BigInteger.ZERO) != 0 : "Precondition Failure";
        if (0 <= a.signum()) {
            if (0 <= b.signum()) {
                // +a +b: a/b
                return a.divide(b);
            } else {
                // +a -b: -(a/(-b))
                return a.divide(b.negate()).negate();
            }
        } else {
            if (0 <= b.signum()) {
                // -a +b: -((-a-1)/b) - 1
                return a.add(BigInteger.ONE).negate().divide(b).negate().subtract(BigInteger.ONE);
            } else {
                // -a -b: ((-a-1)/(-b)) + 1
                return a.add(BigInteger.ONE).negate().divide(b.negate()).add(BigInteger.ONE);
            }
        }
    }

    // pre: b != 0
    // post: remainder == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static byte EuclideanModulus(byte a, byte b) {
        assert b != 0 : "Precondition Failure";
        return (byte) EuclideanModulus((int) a, (int) b);
    }

    public static short EuclideanModulus(short a, short b) {
        assert b != 0 : "Precondition Failure";
        return (short) EuclideanModulus((int) a, (int) b);
    }

    public static int EuclideanModulus(int a, int b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            // +a: a % b'
            if (b == Integer.MIN_VALUE) return (int) new UInt(a).mod(new UInt(b)).value();
            else if (b < 0) return a % -b;
            else return a % b;
        } else {
            // c = ((-a) % b')
            // -a: b' - c if c > 0
            // -a: 0 if c == 0
            if (a == Integer.MIN_VALUE || b == Integer.MIN_VALUE) {
                if (a == b) return 0;
                else if (b == Integer.MIN_VALUE) {
                    return new UInt(b).subtract(new UInt(-a).mod(new UInt(b))).value();
                } else {
                    int bp = b < 0 ? -b : b;
                    return new UInt(bp).subtract(new UInt(a).mod(new UInt(bp))).value();
                }
            } else {
                int bp = b < 0 ? -b : b;
                int c = ((-a) % bp);
                return c == 0 ? c : bp - c;
            }
        }
    }

    public static long EuclideanModulus(long a, long b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            // +a: a % b'
            if (b == Long.MIN_VALUE) return (int) new ULong(a).mod(new ULong(b)).value();
            else if (b < 0) return a % -b;
            else return a % b;
        } else {
            // c = ((-a) % b')
            // -a: b' - c if c > 0
            // -a: 0 if c == 0
            if (a == Long.MIN_VALUE || b == Long.MIN_VALUE) {
                if (a == b) return 0;
                else if (b == Long.MIN_VALUE) {
                    return new ULong(b).subtract(new ULong(-a).mod(new ULong(b))).value();
                } else {
                    long bp = b < 0 ? -b : b;
                    return new ULong(bp).subtract(new ULong(a).mod(new ULong(bp))).value();
                }
            } else {
                long bp = b < 0 ? -b : b;
                long c = ((-a) % bp);
                return c == 0 ? c : bp - c;
            }
        }
    }

    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
        assert b.compareTo(BigInteger.ZERO) != 0 : "Precondition Failure";
        BigInteger bp = b.abs();
        if (0 <= a.signum()) {
            // +a: a % b'
            return a.mod(bp);
        } else {
            // c = ((-a) % b')
            // -a: b' - c if c > 0
            // -a: 0 if c == 0
            BigInteger c = a.negate().mod(bp);
            return c.equals(BigInteger.ZERO) ? c : bp.subtract(c);
        }
    }
}
