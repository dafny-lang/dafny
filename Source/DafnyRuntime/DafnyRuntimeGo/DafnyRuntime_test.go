package dafny

import "testing"

func TestSequenceInterface(t *testing.T){
	arr := GoNativeArray{}
	arrSeq := New_ArraySequence_()
	arrSeq.Ctor__(arr, false) 
	AssertImplementsSequence(arrSeq, t)
}

func AssertImplementsSequence(s interface{}, t *testing.T) {
	_, ok := s.(Sequence)
	if (!ok) {
		t.Errorf("BLARG")
	}
}