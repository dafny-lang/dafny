package dafny

import "testing"

// These tests are currently just useful sanity checks on the interface
// between the manually-written and Dafny-generated Go code,
// but could easily be expanded to include more unit tests in the future.

func TestArraySequence(t *testing.T){
  arrSeq := MakeArraySequence()
  AssertImplementsSequence(arrSeq, t)
}

func MakeArraySequence() Sequence {
  arr := GoNativeArray{}
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

func AssertImplementsSequence(s interface{}, t *testing.T) {
  _, ok := s.(Sequence)
  if (!ok) {
    t.Errorf("Expected %v to implement the Sequence interface", s)
  }
}