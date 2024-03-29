function F(a: array<int>): int
  requires a.Length > 0
{
  a[0] // Suggests to "read a"
}

class C {
  var data: int

  function H(): int {
    var th := this;
    // the suggestion here is to use "reads th#Z" (maybe it's better to give up with
    // a precise "reads" term if the receiver looks complicated, for some definition
    // of complicated)
    th.data
  }
}

codatatype Stream = More(int, Stream)

function Repeat(c: C): Stream {
  // Here, it would be better not to give a "reads" suggestion, since functions with
  // co-recursive calls aren't allowed to have a reads clause. (The AST contain
  // information that says whether or not a call is co-recursive. But I'm not sure if
  // the AST remembers which functions are sometimes targets of co-recursive calls.
  // You could add this. If so, the place to mark a function as such is right next to
  // the ".IsCoCall = true" in ModuleResolver.cs.)
  More(c.data, Repeat(c))
}