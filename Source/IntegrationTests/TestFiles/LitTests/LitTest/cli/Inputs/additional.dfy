type nat32 = x: int32
  | x >= 0

type int32 = x: int
  | -0x7fff_ffff <= x && x <= 0x7fff_ffff // lower bound is incorrect