import DafnyClasses.DafnyMultiset;
import DafnyClasses.DafnySet;
import DafnyClasses.DafnyString;
import DafnyClasses.DafnySequence;

import java.math.BigInteger;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;
import static org.hamcrest.CoreMatchers.startsWith;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

public class SequenceTest {
    Integer[] testSequenceArr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7};
    Integer[] testSequencePreArr = new Integer[]{1, 3, 2, 4, 2, 4};
    Integer[] testSequenceNPreArr = new Integer[]{1, 3, 2, 4, 2, 5};
    Integer[] testSequenceNPre2Arr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7, 3};
    Integer[] testSequenceSubArr = new Integer[]{2, 4, 6, 5};
    Integer[] testSequenceTakeArr = new Integer[]{1, 3, 2, 4, 2};
    Integer[] testSequenceDropArr = new Integer[]{4, 6, 5, 4, 1, 7};
    Integer[] testSequenceEmptyArr = new Integer[]{};
    DafnySequence<Integer> testSequence = new DafnySequence<>(Arrays.asList(testSequenceArr));
    DafnySequence<Integer> testSequencePre = new DafnySequence<>(Arrays.asList(testSequencePreArr));
    DafnySequence<Integer> testSequenceNPre = new DafnySequence<>(Arrays.asList(testSequenceNPreArr));
    DafnySequence<Integer> testSequenceNPre2 = new DafnySequence<>(Arrays.asList(testSequenceNPre2Arr));
    DafnySequence<Integer> testSequenceSub = new DafnySequence<>(Arrays.asList(testSequenceSubArr));
    DafnySequence<Integer> testSequenceDrop = new DafnySequence<>(Arrays.asList(testSequenceDropArr));
    DafnySequence<Integer> testSequenceTake = new DafnySequence<>(Arrays.asList(testSequenceTakeArr));
    DafnySequence<Integer> testSequenceEmpty = new DafnySequence<>(Arrays.asList(testSequenceEmptyArr));
    DafnySequence<Integer> testCopy = new DafnySequence<>(Arrays.asList(testSequenceArr));

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
        DafnySequence<Integer> testUpdate = new DafnySequence(Arrays.asList(new Integer[]{1, 3, 2, 4, 2, 5, 6, 5, 4, 1, 7}));
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
        m.update(1, new BigInteger("2"));
        m.update(2, new BigInteger("2"));
        m.update(3, new BigInteger("1"));
        m.update(4, new BigInteger("3"));
        m.update(5, new BigInteger("1"));
        m.update(6, new BigInteger("1"));
        m.update(7, new BigInteger("1"));
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
        Iterator<DafnySequence> it = sliced.iterator();
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
    public void testNullFailures() {
        List<Integer> l = null;
        DafnySequence<Integer> s = null;
        thrown.expect(AssertionError.class);
        new DafnySequence<>(l);
        new DafnySequence<Integer>(s);
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
        DafnySequence<Integer> testNull = new DafnySequence(Arrays.asList(testNulls));
        testNull = testNull.update(0, null);
        assertEquals(testNull, new DafnySequence<>(Arrays.asList(new Integer[]{null, null, 2})));
    }

    Character[] testStringArr = new Character[]{'1', '3', '2', '4', '2', '4', '6', '5', '4', '1', '7'};
    Character[] testStringPreArr = new Character[]{'1', '3', '2', '4', '2', '4'};
    Character[] testStringNPreArr = new Character[]{'1', '3', '2', '4', '2', '5'};
    Character[] testStringNPre2Arr = new Character[]{'1', '3', '2', '4', '2', '4', '6', '5', '4', '1', '7', '3'};
    Character[] testStringSubArr = new Character[]{'2', '4', '6', '5'};
    Character[] testStringTakeArr = new Character[]{'1', '3', '2', '4', '2'};
    Character[] testStringDropArr = new Character[]{'4', '6', '5', '4', '1', '7'};
    Character[] testStringEmptyArr = new Character[]{};
    DafnyString testString = new DafnyString(Arrays.asList(testStringArr));
    DafnyString testStringPre = new DafnyString(Arrays.asList(testStringPreArr));
    DafnyString testStringNPre = new DafnyString(Arrays.asList(testStringNPreArr));
    DafnyString testStringNPre2 = new DafnyString(Arrays.asList(testStringNPre2Arr));
    DafnyString testStringSub = new DafnyString(Arrays.asList(testStringSubArr));
    DafnyString testStringDrop = new DafnyString(Arrays.asList(testStringDropArr));
    DafnyString testStringTake = new DafnyString(Arrays.asList(testStringTakeArr));
    DafnyString testStringCopy = new DafnyString(Arrays.asList(testStringArr));

    DafnySequence<Character> testStringDropSlice = new DafnySequence<>(Arrays.asList(testStringDropArr));
    DafnySequence<Character> testStringTakeSlice = new DafnySequence<>(Arrays.asList(testStringTakeArr));
    DafnySequence<Character> testStringEmptySlice = new DafnySequence<>(Arrays.asList(testStringEmptyArr));

    @Test
    public void testStringPrefix() {
        assertTrue(testStringPre.isPrefixOf(testString));
        assertFalse(testStringNPre.isPrefixOf(testString));
        assertFalse(testStringNPre2.isPrefixOf(testString));
        assertTrue(testString.isPrefixOf(testString));
    }

    @Test
    public void testStringProperPrefix() {
        assertTrue(testStringPre.isProperPrefixOf(testString));
        assertFalse(testString.isProperPrefixOf(testStringNPre));
        assertTrue(testString.isProperPrefixOf(testStringNPre2));
        assertFalse(testString.isProperPrefixOf(testString));
        assertFalse(testStringNPre.isProperPrefixOf(testString));
        assertFalse(testStringNPre2.isProperPrefixOf(testString));
    }

    @Test
    public void testStringConcatenate() {
        DafnyString fatty = testString.concatenate(testStringPre);
        assertEquals(fatty.length(), testStringPre.length() + testString.length());
        for (int i = 0; i < testString.length(); i++) {
            assertEquals(fatty.select(i), testString.select(i));
        }
        for (int i = 0; i < testStringPre.length(); i++) {
            assertEquals(fatty.select(i + testString.length()), testStringPre.select(i));
        }
    }

    @Test
    public void testStringLength() {
        assertEquals(11, testString.length());
        assertEquals(6, testStringPre.length());
        assertEquals(6, testStringNPre.length());
        assertEquals(12, testStringNPre2.length());
    }

    @Test
    public void testStringUpdate() {
        DafnyString temp = new DafnyString(Arrays.asList(testStringPreArr));
        assertEquals(temp, testStringPre);
        temp = temp.update(5, '5');
        assertEquals(temp, testStringNPre);
    }

    @Test
    public void testStringMembership() {
        assertTrue(testString.contains('1'));
        assertTrue(testString.contains('2'));
        assertTrue(testString.contains('3'));
        assertTrue(testString.contains('4'));
        assertTrue(testString.contains('5'));
        assertTrue(testString.contains('6'));
        assertTrue(testString.contains('7'));
        assertFalse(testString.contains('8'));
        assertFalse(testString.contains('9'));
    }

    @Test
    public void testStringSubStringStuff() {
        assertEquals(testStringSub, testString.subsequence(4, 8));
        assertEquals(testStringDrop, testString.drop(5));
        assertEquals(testStringTake, testString.take(5));
    }

    @Test
    public void testStringMultisetConversion() {
        DafnyMultiset<Character> m = new DafnyMultiset<>();
        m.update('1', new BigInteger("2"));
        m.update('2', new BigInteger("2"));
        m.update('3', new BigInteger("1"));
        m.update('4', new BigInteger("3"));
        m.update('5', new BigInteger("1"));
        m.update('6', new BigInteger("1"));
        m.update('7', new BigInteger("1"));
        DafnyMultiset<Character> c = testString.asDafnyMultiset();
        assertEquals(m, c);

    }

    @Test
    public void testStringSlice() {
        List<Integer> l = new ArrayList<>();
        l.add(5);
        l.add(0);
        l.add(6);
        DafnySequence<DafnySequence<Character>> sliced = testString.slice(l);
        Iterator<DafnySequence> it = sliced.iterator();
        assertEquals(it.next(), testStringTakeSlice);
        assertEquals(it.next(), testStringEmptySlice);
        assertEquals(it.next(), testStringDropSlice);
    }

    @Test
    public void testStringObjectMethods() {
        assertEquals(testString, testStringCopy);
        assertEquals(testString.hashCode(), testStringCopy.hashCode());
        assertEquals("13242465417", testString.toString());
        assertEquals("13242465417", testStringCopy.toString());
    }

    @Test
    public void testNullStringFailures() {
        List<Character> l = null;
        DafnyString s = null;
        thrown.expect(AssertionError.class);
        new DafnyString(l);
        l = new ArrayList<>();
        l.add(null);
        new DafnyString(l);
        new DafnyString(s);
        testString.isPrefixOf(null);
        testString.isProperPrefixOf(null);
        testString.contains(null);
        testString.concatenate(null);
        testString.update(1, null);
        testString.slice(null);
        List<Integer> ints = new ArrayList<>();
        ints.add(null);
        testString.slice(ints);
        testString.forEach(null);
    }

    @Test
    public void testStringIndexFailures() {
        thrown.expect(AssertionError.class);
        testString.drop(13);
        testString.drop(-3);
        testString.take(13);
        testString.take(-3);
        testString.subsequence(-3, 4);
        testString.subsequence(3, 42);
        testString.subsequence(2, 1);
        testString.subsequence(testString.length(), testString.length());
        testString.update(45, 'C');
        testString.update(-8, 'C');
    }
}