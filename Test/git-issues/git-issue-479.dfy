
predicate int32?(x: int) { -0x8000_0000 <= x < 0x8000_0000 }
newtype {:nativeType "int"} int32 = x | int32?(x)


