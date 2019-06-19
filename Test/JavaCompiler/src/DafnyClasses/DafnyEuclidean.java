package DafnyClasses;

import java.math.BigInteger;

public class DafnyEuclidean {
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static byte EuclideanDivision_sbyte(byte a, byte b) {
        assert b != 0 : "Precondition Failure";
        return (byte) EuclideanDivision_int(a, b);
    }

    public static short EuclideanDivision_short(short a, short b) {
        assert b != 0 : "Precondition Failure";
        return (short) EuclideanDivision_int(a, b);
    }

    public static int EuclideanDivision_int(int a, int b) {
        assert b != 0 : "Precondition Failure";
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
        assert b != 0 : "Precondition Failure";
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
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static byte EuclideanModulus_byte(byte a, byte b) {
        assert b != 0 : "Precondition Failure";
        return (byte) EuclideanModulus_int(a, b);
    }

    public static short EuclideanModulus_short(short a, short b) {
        assert b != 0 : "Precondition Failure";
        return (short) EuclideanModulus_int(a, b);
    }

    public static int EuclideanModulus_int(int a, int b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            // +a: a % b'
            if (b == Integer.MIN_VALUE) return (int) new DafnyUInt(a).modulus(new DafnyUInt(b)).value();
            else if (b < 0) return a % -b;
            else return a % b;
        } else {
            // c = ((-a) % b')
            // -a: b' - c if c > 0
            // -a: 0 if c == 0
            if (a == Integer.MIN_VALUE || b == Integer.MIN_VALUE) {
                if (a == b) return 0;
                else if (b == Integer.MIN_VALUE) {
                    return new DafnyUInt(b).subtract(new DafnyUInt(-a).modulus(new DafnyUInt(b))).value();
                } else {
                    int bp = b < 0 ? -b : b;
                    return new DafnyUInt(bp).subtract(new DafnyUInt(a).modulus(new DafnyUInt(bp))).value();
                }
            } else {
                int bp = b < 0 ? -b : b;
                int c = ((-a) % bp);
                return c == 0 ? c : bp - c;
            }
        }
    }

    public static long EuclideanModulus_long(long a, long b) {
        assert b != 0 : "Precondition Failure";
        if (0 <= a) {
            // +a: a % b'
            if (b == Long.MIN_VALUE) return (int) new DafnyULong(a).modulus(new DafnyULong(b)).value();
            else if (b < 0) return a % -b;
            else return a % b;
        } else {
            // c = ((-a) % b')
            // -a: b' - c if c > 0
            // -a: 0 if c == 0
            if (a == Long.MIN_VALUE || b == Long.MIN_VALUE) {
                if (a == b) return 0;
                else if (b == Long.MIN_VALUE) {
                    return new DafnyULong(b).subtract(new DafnyULong(-a).modulus(new DafnyULong(b))).value();
                } else {
                    long bp = b < 0 ? -b : b;
                    return new DafnyULong(bp).subtract(new DafnyULong(a).modulus(new DafnyULong(bp))).value();
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
