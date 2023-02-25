// RUN: %verify "%s"

module {:options "-functionSyntax:4"} BoundedInts {
  const TWO_TO_THE_0:   int := 1

  const TWO_TO_THE_1:   int := 2
  const TWO_TO_THE_2:   int := 4
  const TWO_TO_THE_4:   int := 16
  const TWO_TO_THE_5:   int := 32
  const TWO_TO_THE_8:   int := 0x100
  const TWO_TO_THE_16:  int := 0x10000
  const TWO_TO_THE_24:  int := 0x1000000
  const TWO_TO_THE_32:  int := 0x1_00000000
  const TWO_TO_THE_40:  int := 0x100_00000000
  const TWO_TO_THE_48:  int := 0x10000_00000000
  const TWO_TO_THE_56:  int := 0x1000000_00000000
  const TWO_TO_THE_64:  int := 0x1_00000000_00000000
  const TWO_TO_THE_128: int := 0x1_00000000_00000000_00000000_00000000
  const TWO_TO_THE_256: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
  const TWO_TO_THE_512: int :=
    0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;

  newtype uint8 = x: int  | 0 <= x < TWO_TO_THE_8
  newtype uint16 = x: int | 0 <= x < TWO_TO_THE_16
  newtype uint32 = x: int | 0 <= x < TWO_TO_THE_32
  newtype uint64 = x: int | 0 <= x < TWO_TO_THE_64

  newtype int8 = x: int   | -0x80 <= x < 0x80
  newtype int16 = x: int  | -0x8000 <= x < 0x8000
  newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  newtype nat8 = x: int   | 0 <= x < 0x80
  newtype nat16 = x: int  | 0 <= x < 0x8000
  newtype nat32 = x: int  | 0 <= x < 0x8000_0000
  newtype nat64 = x: int  | 0 <= x < 0x8000_0000_0000_0000

}
