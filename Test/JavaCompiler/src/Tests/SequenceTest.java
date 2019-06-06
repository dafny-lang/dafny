package Tests;

import DafnyClasses.DafnyMultiset;
import DafnyClasses.DafnyString;
import DafnyClasses.DafnySequence;
import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;

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

    @Test
    public void testSequencePrefix() {
        assertTrue(testSequence.prefix(testSequencePre));
        assertFalse(testSequence.prefix(testSequenceNPre));
        assertFalse(testSequence.prefix(testSequenceNPre2));
        assertTrue(testSequence.prefix(testSequence));
    }

    @Test
    public void testSequenceProperPrefix() {
        assertTrue(testSequence.properPrefix(testSequencePre));
        assertFalse(testSequence.properPrefix(testSequenceNPre));
        assertFalse(testSequence.properPrefix(testSequenceNPre2));
        assertFalse(testSequence.properPrefix(testSequence));
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
        DafnySequence<Integer> temp = new DafnySequence<>(Arrays.asList(testSequencePreArr));
        assertEquals(temp, testSequencePre);
        temp = temp.update(5, 5);
        assertEquals(temp, testSequenceNPre);
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
    DafnyString testStringEmpty = new DafnyString(Arrays.asList(testStringEmptyArr));

    DafnySequence<Character> testStringDropSlice = new DafnySequence<>(Arrays.asList(testStringDropArr));
    DafnySequence<Character> testStringTakeSlice = new DafnySequence<>(Arrays.asList(testStringTakeArr));
    DafnySequence<Character> testStringEmptySlice = new DafnySequence<>(Arrays.asList(testStringEmptyArr));

    @Test
    public void testStringPrefix() {
        assertTrue(testString.prefix(testStringPre));
        assertFalse(testString.prefix(testStringNPre));
        assertFalse(testString.prefix(testStringNPre2));
        assertTrue(testString.prefix(testString));
    }

    @Test
    public void testStringProperPrefix() {
        assertTrue(testString.properPrefix(testStringPre));
        assertFalse(testString.properPrefix(testStringNPre));
        assertFalse(testString.properPrefix(testStringNPre2));
        assertFalse(testString.properPrefix(testString));
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

}