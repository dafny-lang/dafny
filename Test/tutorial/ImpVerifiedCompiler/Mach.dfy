include "Common.dfy"

type offset = int

datatype instruction =
  | Iconst(int)
  | Ivar(ident)
  | Isetvar(string)
  | Iadd
	| Iopp
  | Ibranch(offset)
  | Ibeq(offset,offset)
  | Ible(offset,offset)
  | Ihalt

type code = seq<instruction>



