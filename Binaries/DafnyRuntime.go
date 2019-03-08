package dafny

import (
	fmt "fmt"
)

type showable interface{ String() string }

// PrintAny prints an arbitrary value to standard output.
func PrintAny(x interface{}) {
	switch x.(type) {
	case showable:
		fmt.Printf("%s", x.(showable).String())
		break
	default:
		fmt.Printf("%+v", x)
		break
	}
}

// The Dummy type is just so that we can generate "var _ dafny.Dummy" to
// suppress the unused-import error.
type Dummy struct{}
