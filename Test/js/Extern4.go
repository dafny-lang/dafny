package Library

import (
	"dafny"
)

type CompanionStruct_LibClass_ struct{}

var Companion_LibClass_ = CompanionStruct_LibClass_{}

func (CompanionStruct_LibClass_) CallMeInt(x dafny.Int) (y, z dafny.Int) {
	y = x.Plus(dafny.One)
	z = y.Plus(y)
	return
}

func (CompanionStruct_LibClass_) CallMeNative(x int32, b bool) int32 {
	var y int32
	if b {
		y = x + 1
	} else {
		y = x - 1
	}
	return y
}

type Dummy__ struct{}
