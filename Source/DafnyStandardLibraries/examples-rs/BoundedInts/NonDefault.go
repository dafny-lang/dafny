package Externs

type NonDefault struct{}
var Companion_NonDefault_ = NonDefault{}

func (NonDefault) SquareNativeInt(i int32) (int32) {
  return i * i
}