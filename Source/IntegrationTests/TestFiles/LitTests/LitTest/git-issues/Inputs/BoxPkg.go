// An extern Go class that follows the contract in the reference manual's
// "Equality of extern types": it implements EqualsGeneric as identity, which is
// the equality Dafny assumes for a class. Dafny cannot generate this, because Go
// does not allow methods to be declared on another package's type.
package BoxPkg

type Box struct {
	dummy byte
}

type CompanionStruct_Box_ struct{}

var Companion_Box_ = CompanionStruct_Box_{}

func New_Box_() *Box {
	return &Box{}
}

func (_this *Box) Equals(other *Box) bool {
	return _this == other
}

func (_this *Box) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*Box)
	return ok && _this.Equals(other)
}
