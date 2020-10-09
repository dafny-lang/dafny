package DafnyProfiling

import (
  "fmt"
)

// The Dummy__ type, which each compiled Dafny module declares, is just so that
// we can generate "var _ dafny.Dummy__" to suppress the unused-import error.
type Dummy__ struct{}

type CodeCoverage_ struct {
  tallies []int
}
var CodeCoverage = CodeCoverage_ {
}

func (_static *CodeCoverage_) Setup(size int) {
  _static.tallies = make([]int, size)
}

func (_static *CodeCoverage_) TearDown() {
  for i := 0; i < len(_static.tallies); i++ {
    fmt.Printf("%d: %d\n", i, _static.tallies[i])
  }
  empty := [0]int{}
  _static.tallies = empty[:]
}

func (_static *CodeCoverage_) Record(id int) bool {
  _static.tallies[id]++
  return true;
}
