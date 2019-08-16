package dafny;

import java.math.BigInteger;
import java.util.Iterator;

public class AllIntegers implements Iterable<BigInteger> {
    @Override
    public Iterator<BigInteger> iterator() {
        return new AllIntegersIterator();
    }
}

class AllIntegersIterator implements Iterator<BigInteger> {

    BigInteger i = BigInteger.ZERO;

    @Override
    public boolean hasNext() {
        return true;
    }

    @Override
    public BigInteger next() {
        BigInteger j = i;
        if(i.equals(BigInteger.ZERO))
            i.add(BigInteger.ONE);
        else if(i.signum() > 0)
            i.multiply(BigInteger.valueOf(-1L));
        else
            i.multiply(BigInteger.valueOf(-1L)).add(BigInteger.ONE);
        return j;
    }
}
