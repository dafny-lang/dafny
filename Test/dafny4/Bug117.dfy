// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module AbstractModule1
{
	type AbstractType1
}

abstract module AbstractModule2
{
	import opened AM1 : AbstractModule1

	datatype AbstractType2 = AbstractType2(x:AbstractType1)
}

abstract module AbstractModule3
{
	import AM1 : AbstractModule1

	datatype AbstractType2 = AbstractType2(x:AM1.AbstractType1)
}

module ConcreteModule1 refines AbstractModule1
{
	type AbstractType1 = int
}

module ConcreteModule2 refines AbstractModule2
{
	import AM1 = ConcreteModule1 // error: must be declared "opened" to match AbstratctModule2
}

module ConcreteModule3 refines AbstractModule3
{
	import opened AM1 = ConcreteModule1 // error: can't be declared "opened" to match AbstractModule3
}

