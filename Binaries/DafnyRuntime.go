package dafny

import (
	fmt "fmt"
	big "math/big"
	refl "reflect"
)

/******************************************************************************
 * Characters
 ******************************************************************************/

// A Char is a rune in a wrapper so that we can detect it and treat it
// distinctly from int32.
type Char rune

func (char Char) String() string {
	return fmt.Sprintf("%c", rune(char))
}

/******************************************************************************
 * Arrays
 ******************************************************************************/

// An Array is a Go slice representing a (possibly) multidimensional array,
// along with metadata.  There aren't any methods for updating; instead, you can
// update by mutating the value returned by Index (either by using its Set
// method or by getting a pointer using its Addr method).
type Array struct {
	contents refl.Value // stored as a flat one-dimensional slice
	dims     []*big.Int // keep as *big.Ints because we return them to user code
	sizes    []int      // use ints because we only use them internally
}

// NewArray returns a new Array full of the zero value of the given type.
func NewArray(typ refl.Type, dims ...*big.Int) Array {
	sizes := make([]int, len(dims))
	size := 1
	for d := len(dims) - 1; d >= 0; d-- {
		sizes[d] = size
		size *= int(dims[d].Int64())
	}
	contents := refl.MakeSlice(refl.SliceOf(typ), size, size)
	return Array{
		contents: contents,
		dims:     dims,
		sizes:    sizes,
	}
}

// NewArrayFromString converts from a string to an array of Chars.
func NewArrayFromString(str string) Array {
	return Array{
		contents: refl.ValueOf(([]Char)(str)),
		dims:     []*big.Int{big.NewInt(int64(len(str)))},
		sizes:    []int{1},
	}
}

// NewArrayWith returns a new Array full of the given initial value.
func NewArrayWith(init interface{}, dims ...*big.Int) Array {
	ans := NewArray(refl.TypeOf(init), dims...)
	initValue := refl.ValueOf(init)
	n := ans.contents.Len()
	for i := 0; i < n; i++ {
		ans.contents.Index(i).Set(initValue)
	}
	return ans
}

// Len returns the length of the array in the given dimension.
func (array Array) Len(dim *big.Int) *big.Int {
	return array.dims[int(dim.Int64())]
}

func (array Array) index(ixs ...int) refl.Value {
	i := 0
	for d := range array.dims {
		i += ixs[d] * array.sizes[d]
	}
	return array.contents.Index(i)
}

// Index gets the element at the given indices into the array.
func (array Array) Index(ixs ...*big.Int) refl.Value {
	if len(ixs) != len(array.dims) {
		panic(fmt.Sprintf("Expected %d indices but got %d", len(array.dims), len(ixs)))
	}
	i := 0
	for d := range array.dims {
		i += int(ixs[d].Int64()) * array.sizes[d]
	}
	return array.contents.Index(i)
}

// Slice takes the slice a[from:to] of the given array.
func (array Array) Slice(from, to *big.Int) Array {
	if len(array.dims) != 1 {
		panic("TODO: Slices of multidimensional arrays")
	}
	return Array{
		contents: array.contents.Slice(int(from.Int64()), int(to.Int64())),
		dims:     []*big.Int{new(big.Int).Sub(to, from)},
		sizes:    []int{1},
	}
}

// SliceAll takes the slice a[:] of the given array.
func (array Array) SliceAll() Array {
	return array.Slice(zero, array.Len(zero))
}

// SliceFrom takes the slice a[from:] of the given array.
func (array Array) SliceFrom(ix *big.Int) Array {
	return array.Slice(ix, array.Len(zero))
}

// SliceTo takes the slice a[:to] of the given array.
func (array Array) SliceTo(ix *big.Int) Array {
	return array.Slice(zero, ix)
}

func (array Array) stringOfSubspace(d int, ixs []int) string {
	if d == len(array.dims) {
		return fmt.Sprint(array.index(ixs...))
	}
	s := "["
	for i := 0; int64(i) < array.dims[d].Int64(); i++ {
		if i > 0 {
			s += ", "
		}
		ixs[d] = i
		s += array.stringOfSubspace(d+1, ixs)
	}
	s += "]"
	return s
}

func (array Array) String() string {
	switch arr := array.contents.Interface().(type) {
	case []Char:
		s := ""
		for _, c := range arr {
			s += c.String()
		}
		return s
	default:
		ixs := make([]int, len(array.dims))
		return array.stringOfSubspace(0, ixs)
	}
}

/******************************************************************************
 * Integers
 ******************************************************************************/

// Note: We treat all *big.Ints as immutable integer values.

// TODO: Encapsulate *big.Int?  Then we could protect them from mutation.  And
// then we could pool common ones and not allocate them so much.

// Don't export these!  They're mutable!
var zero = big.NewInt(0)
var one = big.NewInt(1)

// Incr increments the given big integer by one, returning a newly allocated
// value.
func Incr(n *big.Int) *big.Int {
	return new(big.Int).Add(n, one)
}

// Decr decrements the given big integer by one, returning a newly allocated
// value.
func Decr(n *big.Int) *big.Int {
	return new(big.Int).Sub(n, one)
}

// Double doubles the given big integer, returning a newly allocated value.
func Double(n *big.Int) *big.Int {
	return new(big.Int).Lsh(n, 1)
}

/******************************************************************************
 * Hacks for generated code
 ******************************************************************************/

// The Dummy type, which each compiled Dafny module declares, is just so that
// we can generate "var _ dafny.Dummy" to suppress the unused-import error.
type Dummy struct{}
