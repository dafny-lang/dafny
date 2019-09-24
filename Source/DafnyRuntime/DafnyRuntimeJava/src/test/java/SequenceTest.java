import dafny.DafnyMultiset;
import dafny.DafnySequence;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import static org.junit.Assert.*;

public class SequenceTest {
    Integer[] testSequenceArr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7};
    Integer[] testSequencePreArr = new Integer[]{1, 3, 2, 4, 2, 4};
    Integer[] testSequenceNPreArr = new Integer[]{1, 3, 2, 4, 2, 5};
    Integer[] testSequenceNPre2Arr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7, 3};
    Integer[] testSequenceSubArr = new Integer[]{2, 4, 6, 5};
    Integer[] testSequenceTakeArr = new Integer[]{1, 3, 2, 4, 2};
    Integer[] testSequenceDropArr = new Integer[]{4, 6, 5, 4, 1, 7};
    Integer[] testSequenceEmptyArr = new Integer[]{};
    DafnySequence<Integer> testSequence = DafnySequence.fromArray(testSequenceArr);
    DafnySequence<Integer> testSequencePre = DafnySequence.fromArray(testSequencePreArr);
    DafnySequence<Integer> testSequenceNPre = DafnySequence.fromArray(testSequenceNPreArr);
    DafnySequence<Integer> testSequenceNPre2 = DafnySequence.fromArray(testSequenceNPre2Arr);
    DafnySequence<Integer> testSequenceSub = DafnySequence.fromArray(testSequenceSubArr);
    DafnySequence<Integer> testSequenceDrop = DafnySequence.fromArray(testSequenceDropArr);
    DafnySequence<Integer> testSequenceTake = DafnySequence.fromArray(testSequenceTakeArr);
    DafnySequence<Integer> testSequenceEmpty = DafnySequence.fromArray(testSequenceEmptyArr);
    DafnySequence<Integer> testCopy = DafnySequence.fromArray(testSequenceArr);

    @Test
    public void testSequencePrefix() {
        assertTrue(testSequencePre.isPrefixOf(testSequence));
        assertFalse(testSequenceNPre.isPrefixOf(testSequence));
        assertFalse(testSequenceNPre2.isPrefixOf(testSequence));
        assertTrue(testSequence.isPrefixOf(testSequence));
        assertFalse(testSequence.isPrefixOf(testSequencePre));
    }

    @Test
    public void testSequenceProperPrefix() {
        assertTrue(testSequencePre.isProperPrefixOf(testSequence));
        assertFalse(testSequence.isProperPrefixOf(testSequenceNPre));
        assertFalse(testSequence.isProperPrefixOf(testSequence));
        assertFalse(testSequenceNPre.isProperPrefixOf(testSequence));
        assertFalse(testSequenceNPre2.isProperPrefixOf(testSequence));
    }

    @Test
    public void testSequenceConcatenate() {
        DafnySequence<Integer> fatty = testSequence.concatenate(testSequencePre);
        assertEquals(fatty.length(), testSequencePre.length() + testSequence.length());
        for (int i = 0; i < testSequence.length(); i++) {
            assertEquals(fatty.select(i), testSequence.select(i));
        }
        for (int i = 0; i < testSequencePre.length(); i++) {
            assertEquals(fatty.select(i + testSequence.length()), testSequencePre.select(i));
        }
    }

    @Test
    public void testSequenceLength() {
        assertEquals(11, testSequence.length());
        assertEquals(6, testSequencePre.length());
        assertEquals(6, testSequenceNPre.length());
        assertEquals(12, testSequenceNPre2.length());
    }

    @Test
    public void testSequenceUpdate() {
        DafnySequence<Integer> temp;
        temp = testSequence.update(5, 5);
        DafnySequence<Integer> testUpdate = DafnySequence.fromArray(new Integer[]{1, 3, 2, 4, 2, 5, 6, 5, 4, 1, 7});
        assertEquals(temp, testUpdate);
        assertEquals(testSequence, testCopy);
    }

    @Test
    public void testSequenceMembership() {
        assertTrue(testSequence.contains(1));
        assertTrue(testSequence.contains(2));
        assertTrue(testSequence.contains(3));
        assertTrue(testSequence.contains(4));
        assertTrue(testSequence.contains(5));
        assertTrue(testSequence.contains(6));
        assertTrue(testSequence.contains(7));
        assertFalse(testSequence.contains(8));
        assertFalse(testSequence.contains(9));
        assertFalse(testSequence.contains(10));
    }

    @Test
    public void testSequenceSubsequenceStuff() {
        assertEquals(testSequenceSub, testSequence.subsequence(4, 8));
        assertEquals(testSequenceDrop, testSequence.drop(5));
        assertEquals(testSequenceTake, testSequence.take(5));
    }

    @Test
    public void testSequenceMultisetConversion() {
        DafnyMultiset<Integer> m = new DafnyMultiset<>();
        m = m.update(1, BigInteger.valueOf(2));
        m = m.update(2, BigInteger.valueOf(2));
        m = m.update(3, BigInteger.valueOf(1));
        m = m.update(4, BigInteger.valueOf(3));
        m = m.update(5, BigInteger.valueOf(1));
        m = m.update(6, BigInteger.valueOf(1));
        m = m.update(7, BigInteger.valueOf(1));
        DafnyMultiset<Integer> c = testSequence.asDafnyMultiset();
        assertEquals(m, c);

    }

    @Test
    public void testSequenceSlice() {
        List<Integer> l = new ArrayList<>();
        l.add(5);
        l.add(0);
        l.add(6);
        DafnySequence<DafnySequence<Integer>> sliced = testSequence.slice(l);
        Iterator<DafnySequence<Integer>> it = sliced.iterator();
        assertEquals(it.next(), testSequenceTake);
        assertEquals(it.next(), testSequenceEmpty);
        assertEquals(it.next(), testSequenceDrop);
    }

    @Test
    public void testObjectMethods() {
        assertEquals(testSequence, testCopy);
        assertEquals(testSequence.hashCode(), testCopy.hashCode());
        assertEquals("[1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7]", testSequence.toString());
        assertEquals("[1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7]", testCopy.toString());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();


    @Test
    @SuppressWarnings("all")
    public void testNullFailures() {
        List<Integer> l = null;
        thrown.expect(AssertionError.class);
        DafnySequence.fromList(l);
        testSequence.isPrefixOf(null);
        testSequence.isProperPrefixOf(null);
        testSequence.contains(null);
        testSequence.concatenate(null);
        testSequence.update(1, null);
        testSequence.slice(null);
        l = new ArrayList<>();
        l.add(null);
        testSequence.slice(l);
        testSequence.forEach(null);
    }

    @Test
    public void testIndexFailures() {
        thrown.expect(AssertionError.class);
        testSequence.drop(13);
        testSequence.drop(-3);
        testSequence.take(13);
        testSequence.take(-3);
        testSequence.subsequence(-3, 4);
        testSequence.subsequence(3, 42);
        testSequence.subsequence(2, 1);
        testSequence.subsequence(testSequence.length(), testSequence.length());
        testSequence.update(45, 3);
        testSequence.update(-8, 3);
    }

    @Test
    public void testNullMembers() {
        Integer[] testNulls = new Integer[]{3, null, 2};
        DafnySequence<Integer> testNull = DafnySequence.fromArray(testNulls);
        testNull = testNull.update(0, null);
        assertEquals(testNull, DafnySequence.fromArray(new Integer[]{null, null, 2}));
    }
}
