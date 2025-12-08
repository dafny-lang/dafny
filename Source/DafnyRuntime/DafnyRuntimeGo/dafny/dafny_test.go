package dafny

import "testing"

func TestArraySequence(t *testing.T) {
	arrSeq := MakeArraySequence()
	AssertImplementsSequence(arrSeq, t)
}

func MakeArraySequence() Sequence {
	underlying := &arrayStruct{
		contents: []interface{}{},
		dims:     []int{0},
	}
	arr := GoNativeArray{underlying: underlying}
	arrSeq := New_ArraySequence_()
	arrSeq.Ctor__(arr, false)
	return arrSeq
}

func TestConcatSequence(t *testing.T) {
	left := MakeArraySequence()
	right := MakeArraySequence()

	concatSeq := New_ConcatSequence_()
	concatSeq.Ctor__(left, right)

	AssertImplementsSequence(concatSeq, t)
}

func TestLazySequence(t *testing.T) {
	arrSeq := MakeArraySequence()

	lazySeq := New_LazySequence_()
	lazySeq.Ctor__(arrSeq)

	AssertImplementsSequence(lazySeq, t)
}

// Test byte sequence optimization using arrayForByte wrapper
func TestByteSequenceOptimization(t *testing.T) {
	// Test creating byte sequence from slice
	data := []byte{1, 2, 3, 4, 5}
	seq := SeqOfBytes(data)

	// Verify it implements Sequence interface
	AssertImplementsSequence(seq, t)

	// Verify ToArray returns GoNativeArray
	arr := seq.ToArray()
	if byteArr, ok := arr.(GoNativeArray); ok {
		if byteArr.Length() != 5 {
			t.Errorf("Expected length 5, got %d", byteArr.Length())
		}
		if byteArr.Select(0).(uint8) != 1 {
			t.Errorf("Expected first element 1, got %v", byteArr.Select(0))
		}
	} else {
		t.Errorf("Expected GoNativeArray, got %T", arr)
	}
}

// Test optimization detection for uint8 vs non-uint8
func TestSeqOf(t *testing.T) {
	// Test uint8 slice - should optimize
	uint8Contents := []interface{}{uint8(1), uint8(2), uint8(3)}
	seq := SeqOf(uint8Contents...)
	if !SequenceIsBackedByByteArray(seq) {
		t.Error("Expected optimization for uint8 slice")
	}

	// Verify it returns GoNativeArray
	arr := seq.ToArray()
	if _, ok := arr.(GoNativeArray); !ok {
		t.Errorf("Expected GoNativeArray, got %T", arr)
	}

	// Test non-uint8 slice - should not optimize
	intContents := []interface{}{1, 2, 3}
	seq2 := SeqOf(intContents...)
	if SequenceIsBackedByByteArray(seq2) {
		t.Error("Expected no optimization for int slice")
	}

	// Test empty slice - should not optimize
	emptyContents := []interface{}{}
	seq3 := SeqOf(emptyContents...)
	if SequenceIsBackedByByteArray(seq3) {
		t.Error("Expected no optimization for empty slice")
	}
}

func TestSeqFromArray(t *testing.T) {
	// Test uint8 slice - should not optimize
	// (in fact it should use the array without copying)
	uint8Contents := []interface{}{uint8(1), uint8(2), uint8(3)}
	seq := SeqFromArray(uint8Contents, false)
	if SequenceIsBackedByByteArray(seq) {
		t.Error("Expected no optimization for int slice")
	}

	// Mutate the array (exactly as you're not supposed to :)
	// and check the sequence changes.
	uint8Contents[1] = uint8(42)
	if seq.Select(1) != uint8(42) {
		t.Errorf("Expected element at index 1 to be 42, got %v", seq.Select(1))
	}
}

// Test refactored CompanionStruct_NativeArray_ functions
func TestNativeArrayFunctions(t *testing.T) {
	// Test Make function
	arr := Companion_NativeArray_.Make(3)
	if goArr, ok := arr.(GoNativeArray); ok {
		if goArr.Length() != 3 {
			t.Errorf("Expected length 3, got %d", goArr.Length())
		}
	} else {
		t.Errorf("Expected GoNativeArray, got %T", arr)
	}

	// Test MakeWithInit function
	initFunc := func(i uint32) interface{} { return int(i * 2) }
	arr2 := Companion_NativeArray_.MakeWithInit(3, initFunc)
	if goArr2, ok := arr2.(GoNativeArray); ok {
		if goArr2.Length() != 3 {
			t.Errorf("Expected length 3, got %d", goArr2.Length())
		}
		if goArr2.Select(1) != 2 {
			t.Errorf("Expected element at index 1 to be 2, got %v", goArr2.Select(1))
		}
	} else {
		t.Errorf("Expected GoNativeArray, got %T", arr2)
	}

	// Test Copy function with GoNativeArray
	arr3 := Companion_NativeArray_.Copy(arr2.(GoNativeArray))
	if goArr3, ok := arr3.(GoNativeArray); ok {
		if goArr3.Length() != 3 {
			t.Errorf("Expected length 3, got %d", goArr3.Length())
		}
		if goArr3.Select(1) != 2 {
			t.Errorf("Expected element at index 1 to be 2, got %v", goArr3.Select(1))
		}
	} else {
		t.Errorf("Expected GoNativeArray, got %T", arr3)
	}

	// Test Copy function with GoNativeArray
	data := []byte{10, 20, 30}
	byteSeq := SeqOfBytes(data)
	byteArr := byteSeq.ToArray()
	arr4 := Companion_NativeArray_.Copy(byteArr)
	if byteArr4, ok := arr4.(GoNativeArray); ok {
		if byteArr4.Length() != 3 {
			t.Errorf("Expected length 3, got %d", byteArr4.Length())
		}
		if byteArr4.Select(1).(uint8) != 20 {
			t.Errorf("Expected element at index 1 to be 20, got %v", byteArr4.Select(1))
		}
	} else {
		t.Errorf("Expected GoNativeArray, got %T", arr4)
	}
}

func TestArrayCopy(t *testing.T) {
	arr := NewArray(Five)
	copy := arr.arrayCopy()
	if arr.(EqualsGeneric).EqualsGeneric(copy) {
		t.Errorf("Expected array to not compare EqualsGeneric to its copy")
	}
}

func AssertImplementsSequence(s interface{}, t *testing.T) {
	_, ok := s.(Sequence)
	if !ok {
		t.Errorf("Expected %v to implement the Sequence interface", s)
	}
}

func SequenceIsBackedByByteArray(seq Sequence) bool {
	_, ok := seq.(*ArraySequence)._values.(GoNativeArray).underlying.(*arrayForByte)
	return ok
}


