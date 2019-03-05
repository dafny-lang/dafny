package main

import (
	fmt "fmt"
	big "math/big"
)

var _ big.Int

type showable interface{ String() string }

func printAny(x interface{}) {
	switch x.(type) {
	case showable:
		fmt.Printf("%s", x.(showable).String())
		break
	default:
		fmt.Printf("%+v", x)
		break
	}
}
