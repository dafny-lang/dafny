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
	dims     []Int      // keep as Ints because we return them to user code
	sizes    []int      // use ints because we only use them internally
}

// NewArray returns a new Array full of the zero value of the given type.
func NewArray(typ refl.Type, dims ...Int) Array {
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
		dims:     []Int{IntOf(int64(len(str)))},
		sizes:    []int{1},
	}
}

// NewArrayWithValue returns a new Array full of the given initial value.
func NewArrayWithValue(init interface{}, dims ...Int) Array {
	ans := NewArray(refl.TypeOf(init), dims...)
	initValue := refl.ValueOf(init)
	n := ans.contents.Len()
	for i := 0; i < n; i++ {
		ans.contents.Index(i).Set(initValue)
	}
	return ans
}

// NewArrayWithValues returns a new one-dimensional Array with the given initial
// values, which must be of the given type.  (The type must be given in case
// there are no values.)
func NewArrayWithValues(typ refl.Type, values ...refl.Value) Array {
	n := len(values)
	contents := refl.MakeSlice(refl.SliceOf(typ), n, n)
	for i, v := range values {
		contents.Index(i).Set(v)
	}
	return Array{
		contents: contents,
		dims:     []Int{IntOf(int64(n))},
		sizes:    []int{1},
	}
}

// Len returns the length of the array in the given dimension.
func (array Array) Len(dim Int) Int {
	return array.dims[int(dim.Int64())]
}

// Equals compares two arrays for equality.  Values are compared using
// refl.DeepEqual.
func (array Array) Equals(array2 Array) bool {
	if len(array.dims) != len(array2.dims) {
		return false
	}
	for i, d := range array.dims {
		if d.Cmp(array2.dims[i]) != 0 {
			return false
		}
	}

	// Not clear that this will always do the right thing.  It definitely won't
	// with user-defined types with traits (since those values contain
	// back pointers).
	return refl.DeepEqual(array.contents.Interface(), array2.contents.Interface())
}

func (array Array) index(ixs ...int) refl.Value {
	i := 0
	for d := range array.dims {
		i += ixs[d] * array.sizes[d]
	}
	return array.contents.Index(i)
}

// Index gets the element at the given indices into the array.
func (array Array) Index(ixs ...Int) refl.Value {
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
func (array Array) Slice(from, to Int) Array {
	if len(array.dims) != 1 {
		panic("TODO: Slices of multidimensional arrays")
	}
	return Array{
		contents: array.contents.Slice(int(from.Int64()), int(to.Int64())),
		dims:     []Int{to.Minus(from)},
		sizes:    []int{1},
	}
}

// SliceAll takes the slice a[:] of the given array.
func (array Array) SliceAll() Array {
	return array.Slice(Zero, array.Len(Zero))
}

// SliceFrom takes the slice a[from:] of the given array.
func (array Array) SliceFrom(ix Int) Array {
	return array.Slice(ix, array.Len(Zero))
}

// SliceTo takes the slice a[:to] of the given array.
func (array Array) SliceTo(ix Int) Array {
	return array.Slice(Zero, ix)
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

// An Int is an immutable big integer.
type Int struct {
	impl  *big.Int
	debug string
} // Careful not to mutate!

// A BV is an immutable big bitvector (presumed to be positive).
type BV = Int

func intOf(i *big.Int) Int {
	return Int{
		impl:  i,
		debug: i.String(),
	}
}

// IntOf turns the given int64 into an Int.  Common values are cached.
func IntOf(i int64) Int {
	switch i {
	case -1:
		return NegativeOne
	case 0:
		return Zero
	case 1:
		return One
	case 2:
		return Two
	case 5:
		return Five
	case 10:
		return Ten
	default:
		return intOf(big.NewInt(i))
	}
}

// IntOfString parses the given string as an Int, panicking on failure.
func IntOfString(s string) Int {
	switch s {
	case "-1":
		return NegativeOne
	case "0":
		return Zero
	case "1":
		return One
	case "2":
		return Two
	case "5":
		return Five
	case "10":
		return Ten
	default:
		i, ok := new(big.Int).SetString(s, 0)
		if !ok {
			panic("Unable to parse string as int: " + s)
		} else {
			return intOf(i)
		}
	}
}

// Int64 converts back to an int64.  If the result is not within int64 range,
// the value is undefined.
func (i Int) Int64() int64 {
	return i.impl.Int64()
}

// Uint64 converts back to a uint64.  If the result is not within uint64 range,
// the value is undefined.
func (i Int) Uint64() uint64 {
	return i.impl.Uint64()
}

func (i Int) String() string {
	return i.impl.String()
}

// NegativeOne is the constant -1.
var NegativeOne = intOf(big.NewInt(-1))

// Zero is the constant 0.
var Zero = intOf(big.NewInt(0))

// One is the constant 1.
var One = intOf(big.NewInt(1))

// Two is the constant 2.
var Two = intOf(big.NewInt(2))

// Five is the constant 5.
var Five = intOf(big.NewInt(5))

// Ten is the constant 10.
var Ten = intOf(big.NewInt(10))

func (i Int) binOp(j Int, f func(*big.Int, *big.Int, *big.Int) *big.Int) Int {
	return intOf(f(new(big.Int), i.impl, j.impl))
}

// Plus adds two Ints.
func (i Int) Plus(j Int) Int {
	return i.binOp(j, (*big.Int).Add)
}

// Minus subtracts one Int from another.
func (i Int) Minus(j Int) Int {
	return i.binOp(j, (*big.Int).Sub)
}

// Times multiplies two Ints.
func (i Int) Times(j Int) Int {
	return i.binOp(j, (*big.Int).Mul)
}

// DivBy divides one Int by another.  (So named to distinguish from
// big.Int.Div(), which is an in-place operation.)
func (i Int) DivBy(j Int) Int {
	return i.binOp(j, (*big.Int).Div)
}

// Modulo takes the remainder when dividing one Int by another.  (So named to
// distinguish from big.Int.Mod(), which performs the operation in place.)
func (i Int) Modulo(j Int) Int {
	return i.binOp(j, (*big.Int).Mod)
}

// Negated negates an Int.
func (i Int) Negated() Int {
	return intOf(new(big.Int).Neg(i.impl))
}

// Lsh performs a left shift.
func (i Int) Lsh(j Int) Int {
	return intOf(new(big.Int).Lsh(i.impl, uint(j.Uint64())))
}

// Rsh performs a right shift.
func (i Int) Rsh(j Int) Int {
	return intOf(new(big.Int).Rsh(i.impl, uint(j.Uint64())))
}

// Lrot performs a left rotate on a BV with width w.
func (i BV) Lrot(j Int, w uint) BV {
	// (i <<< j) == ((i << j) % 2^w) | (i >> (w-j))

	ju := uint(j.Uint64())
	l := new(big.Int).Lsh(i.impl, ju)
	modulus := new(big.Int).Lsh(One.impl, w)
	l.Mod(l, modulus)
	r := modulus.Rsh(i.impl, w-ju) // reuse memory from modulus
	return intOf(l.Or(l, r))
}

// Rrot performs a right rotate on a BV with width w.
func (i BV) Rrot(j BV, w uint) BV {
	// (i >>> j) == ((i << (w-j)) % 2^w) | (i >> j)

	ju := uint(j.Uint64())
	l := new(big.Int).Lsh(i.impl, w-ju)
	modulus := new(big.Int).Lsh(One.impl, w)
	l.Mod(l, modulus)
	r := modulus.Rsh(i.impl, ju) // reuse memory from modulus
	return intOf(l.Or(l, r))
}

// Cmp compares two Ints, returning -1 for less, 0 for equal, or 1 for greater.
func (i Int) Cmp(j Int) int {
	return i.impl.Cmp(j.impl)
}

// And performs bitwise AND.
func (i Int) And(j Int) Int {
	return i.binOp(j, (*big.Int).And)
}

// Or performs bitwise OR.
func (i Int) Or(j Int) Int {
	return i.binOp(j, (*big.Int).Or)
}

// Xor performs bitwise XOR.
func (i Int) Xor(j Int) Int {
	return i.binOp(j, (*big.Int).Xor)
}

// Not performs bitwise NOT.
func (i Int) Not() Int {
	return intOf(new(big.Int).Not(i.impl))
}

func (i Int) isPowerOf10() (bool, int) {
	if i.Cmp(Zero) != 1 {
		return false, -1
	}
	n := 0
	j := i
	for {
		if j.Cmp(One) == 0 {
			return true, n
		} else if j.Modulo(Ten).Cmp(Zero) != 0 {
			return false, -1
		} else {
			j = j.DivBy(Ten)
			n++
		}
	}
}

func (i Int) dividesAPowerOf10() (yes bool, factor Int, log10 int) {
	if i.Cmp(Zero) != 1 {
		return false, Zero, -1
		// okay, so technically you could multiply by a
		// negative number, but that's not useful to
		// Real.String().
	}
	n := 0
	j := i
	fact := One
	for {
		if j.Cmp(One) == 0 {
			return true, One, n
		} else if j.Modulo(Ten).Cmp(Zero) != 0 {
			if j.Modulo(Five).Cmp(Zero) == 0 {
				for {
					fact = fact.Times(Two)
					j = j.DivBy(Five)
					n++
					if j.Cmp(One) == 0 {
						return true, fact, n
					} else if j.Modulo(Five).Cmp(Zero) != 0 {
						return false, NegativeOne, -1
					}
				}
			} else if j.Modulo(Two).Cmp(Zero) == 0 {
				for {
					fact = fact.Times(Five)
					j = j.DivBy(Two)
					n++
					if j.Cmp(One) == 0 {
						return true, fact, n
					} else if j.Modulo(Two).Cmp(Zero) != 0 {
						return false, NegativeOne, -1
					}
				}
			} else {
				return false, NegativeOne, -1
			}
		} else {
			j = j.DivBy(Ten)
			n++
		}
	}
}

/******************************************************************************
 * Reals
 ******************************************************************************/

// A Real is an arbitrary-precision real number, represented as a ratio of
// arbitrary-precision integers.
type Real struct {
	impl  *big.Rat
	debug string
}

func realOf(r *big.Rat) Real {
	return Real{impl: r, debug: r.String()}
}

// RealOf converts a float64 into a Real.  Common values are cached.
func RealOf(f float64) Real {
	if f == 0.0 {
		return ZeroReal
	}
	return realOf(new(big.Rat).SetFloat64(f))
}

// RealOfFrac makes a Real of the ratio of two Ints.
func RealOfFrac(num, denom Int) Real {
	if num.Cmp(Zero) == 0 {
		return ZeroReal
	}
	return realOf(new(big.Rat).SetFrac(num.impl, denom.impl))
}

// ZeroReal is the Real value zero.
var ZeroReal = realOf(new(big.Rat))

// RealOfString parses the given string in base 10 and panics if this is not
// possible.
func RealOfString(s string) Real {
	x, ok := new(big.Rat).SetString(s)
	if !ok {
		panic("Can't parse generated string as ratio: \"" + s + "\"")
	}
	if x.Cmp(ZeroReal.impl) == 0 {
		return ZeroReal
	}
	return realOf(x)
}

// Int converts the given real to an integer using Euclidean division.
func (x Real) Int() Int {
	return intOf(new(big.Int).Div(x.impl.Num(), x.impl.Denom()))
}

// Num returns the given Real's numerator as an Int
func (x Real) Num() Int {
	return intOf(x.impl.Num())
}

// Denom returns the given Real's denominator as an Int
func (x Real) Denom() Int {
	return intOf(x.impl.Denom())
}

func (x Real) String() string {
	if x.Num().Cmp(Zero) == 0 || x.Denom().Cmp(One) == 0 {
		return x.Num().String() + ".0"
	}
	divsPow10, fact, log10 := x.Denom().dividesAPowerOf10()
	if divsPow10 {
		num := x.Num().Times(fact)
		var sign, digits string
		if x.Cmp(ZeroReal) < 0 {
			sign, digits = "-", num.Negated().String()
		} else {
			sign, digits = "", num.String()
		}
		if log10 < len(digits) {
			n := len(digits) - log10
			return sign + digits[0:n] + "." + digits[n:]
		} else {
			s := sign + "0."
			for i := 0; i < log10-len(digits); i++ {
				s = s + "0"
			}
			return s + digits
		}
	} else {
		return "(" + x.Num().String() + ".0 / " + x.Denom().String() + ".0)"
	}
}

func (x Real) isPowerOf10() (bool, int) {
	if x.Num().Cmp(Zero) != 1 {
		return false, -1
	} else if x.Num().Cmp(One) == 1 {
		b, i := x.Denom().isPowerOf10()
		return b, -i
	} else if x.Denom().Cmp(One) != 1 {
		return false, -1
	} else {
		return x.Num().isPowerOf10()
	}
}

// binOp lifts a binary operation on *big.Rat to one on Reals.  The second
// argument is intended to be of the form (*big.Rat).Op.
func (x Real) binOp(y Real, f func(*big.Rat, *big.Rat, *big.Rat) *big.Rat) Real {
	return realOf(f(new(big.Rat), x.impl, y.impl))
}

// Plus adds two Reals.
func (x Real) Plus(y Real) Real {
	return x.binOp(y, (*big.Rat).Add)
}

// Minus subtracts one Real from another.
func (x Real) Minus(y Real) Real {
	return x.binOp(y, (*big.Rat).Sub)
}

// Times multiplies two Reals.
func (x Real) Times(y Real) Real {
	return x.binOp(y, (*big.Rat).Mul)
}

// DivBy divides one Real by another.
func (x Real) DivBy(y Real) Real {
	return x.binOp(y, (*big.Rat).Quo)
}

// Cmp compares one Real to another, returning -1 for less, 0 for equal, or 1
// for greater.
func (x Real) Cmp(y Real) int {
	return x.impl.Cmp(y.impl)
}

/******************************************************************************
 * Native math
 ******************************************************************************/

// Div_int does Euclidean division on the given ints
func Div_int(x int, y int) int {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_int8 does Euclidean divison on the given int8s
func Div_int8(x int8, y int8) int8 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_int16 does Euclidean divison on the given int16s
func Div_int16(x int16, y int16) int16 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_int32 does Euclidean divison on the given int32s
func Div_int32(x int32, y int32) int32 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_int64 does Euclidean divison on the given int64s
func Div_int64(x int64, y int64) int64 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_float32 does Euclidean division on the given float32s
func Div_float32(x float32, y float32) float32 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Div_float64 does Euclidean division on the given float64s
func Div_float64(x float64, y float64) float64 {
	if x >= 0 {
		if y >= 0 {
			return x / y
		} else {
			return -(x / -y)
		}
	} else {
		if y >= 0 {
			return -((-x - 1) / y) - 1
		} else {
			return ((-x - 1) / (-y)) + 1
		}
	}
}

// Lrot_uint8 performs left rotation on the low w bits of an int8
func Lrot_uint8(x uint8, n Int, w uint) uint8 {
	y := uint(n.Uint64())
	return ((x << y) % (1 << w)) | (x >> (w - y))
}

// Mod_int finds Euclidean remainder of the given ints
func Mod_int(x int, y int) int {
	if y < 0 {
		y = -y
	}
	if x >= 0 {
		return x % y
	} else {
		z := (-x) % y
		if z == 0 {
			return 0
		} else {
			return y - z
		}
	}
}

// Mod_int8 finds Euclidean remainder of the given int8s
func Mod_int8(x int8, y int8) int8 {
	if y < 0 {
		y = -y
	}
	if x >= 0 {
		return x % y
	} else {
		z := (-x) % y
		if z == 0 {
			return 0
		} else {
			return y - z
		}
	}
}

// Mod_int16 finds Euclidean remainder of the given int16s
func Mod_int16(x int16, y int16) int16 {
	if y < 0 {
		y = -y
	}
	if x >= 0 {
		return x % y
	} else {
		z := (-x) % y
		if z == 0 {
			return 0
		} else {
			return y - z
		}
	}
}

// Mod_int32 finds Euclidean remainder of the given int32s
func Mod_int32(x int32, y int32) int32 {
	if y < 0 {
		y = -y
	}
	if x >= 0 {
		return x % y
	} else {
		z := (-x) % y
		if z == 0 {
			return 0
		} else {
			return y - z
		}
	}
}

// Mod_int64 finds Euclidean remainder of the given int64s
func Mod_int64(x int64, y int64) int64 {
	if y < 0 {
		y = -y
	}
	if x >= 0 {
		return x % y
	} else {
		z := (-x) % y
		if z == 0 {
			return 0
		} else {
			return y - z
		}
	}
}

func Rrot_uint8(x uint8, n Int, w uint) uint8 {
	y := uint(n.Uint64())
	return (x >> y) | ((x << (w - y)) % (1 << w))
}

/******************************************************************************
 * Hacks for generated code
 ******************************************************************************/

// The Dummy type, which each compiled Dafny module declares, is just so that
// we can generate "var _ dafny.Dummy" to suppress the unused-import error.
type Dummy struct{}
