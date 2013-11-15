type MyType  // compile error: arbitrary type
iterator Iter()  // compile error: body-less iterator
ghost method M()  // compile error: body-less ghost method
method P()  // compile error: body-less method
method Q()
{
  if g == 0 {
    assume true;  // compile error: assume
  }
}
ghost var g: int;

function F(): int  // compile error: body-less ghost function
function method H(): int  // compile error: body-less function method
