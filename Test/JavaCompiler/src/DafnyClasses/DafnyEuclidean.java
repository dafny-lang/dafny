package DafnyClasses;

import java.math.BigInteger;

public class DafnyEuclidean {
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static byte EuclideanDivision_sbyte(byte a, byte b) {
        return (byte) EuclideanDivision_int(a, b);
    }

    public static short EuclideanDivision_short(short a, short b) {
        return (short) EuclideanDivision_int(a, b);
    }

    public static int EuclideanDivision_int(int a, int b) {
        if (0 <= a) {
            if (0 <= b) {
                // +a +b: a/b
                return a / b;
            } else {
                // +a -b: -(a/(-b))
                // if value of b is 0x80000000, then there is no positive representation for integers, so use uint
                if (b == Integer.MIN_VALUE)
                    return new DafnyUInt(a).divide(new DafnyUInt(Integer.MIN_VALUE)).value() * -1;
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
                    return new DafnyUInt(-(a + 1)).divide(new DafnyUInt(Integer.MIN_VALUE)).value() + 1;
                else return (-(a + 1)) / (-b) + 1;
            }
        }
    }

    public static long EuclideanDivision_long(long a, long b) {
        if (0 <= a) {
            if (0 <= b) {
                // +a +b: a/b
                return a / b;
            } else {
                // +a -b: -(a/(-b))
                // if value of b is 0x8000000000000000L, then there is no positive representation for longs,
                // so use ulong
                if (b == Long.MIN_VALUE) return new DafnyULong(a).divide(new DafnyULong(Long.MIN_VALUE)).value() * -1;
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
                    return new DafnyULong(-(a + 1)).divide(new DafnyULong(Long.MIN_VALUE)).value() + 1;
                else return (-(a + 1)) / (-b) + 1;
            }
        }
    }

    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
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
}
