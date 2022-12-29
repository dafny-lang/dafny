// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NativeTypes {
	newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
}

abstract module AbstractModuleA
{
	import opened NativeTypes
	datatype T = T(i:uint16)
}

abstract module AbstractModuleB
{
	import opened A : AbstractModuleA
}

abstract module AbstractModuleC
{
	import opened B : AbstractModuleB
}

