// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype EInt = Int(val: int) | Unknown
type Pair = (string, EInt)

ghost function Inc(p: Pair): Pair
{
  match p
  case (s, Int(x)) => (s, Int(x + 1))
  case (s, Unknown) => (s, Unknown)
}

ghost function Inc2(s1:string, t1:EInt): Pair
{
  match (s1, t1)
  case (s1, Int(x)) => (s1, Int(x + 1))
  case (s1, Unknown) => (s1, Unknown)
}

ghost function Inc3(s1: string, t1: EInt, t2: EInt) : Pair
{
  match (s1, t1, t2)
  case (s1, Int(x), Unknown) => (s1, Int(x + 1))
  case (s1, Int(x), Int(y)) => (s1, Int(x + y + 1))
  case (s1, Unknown, Unknown) => (s1, Unknown)
  case (s1, Unknown, Int(y)) => (s1, Int(y+1))
}

type Triple = (string, EInt, EInt)

ghost function Inc4(t: Triple) : Pair
{
  match t
  case (s1, Int(x), Unknown) => (s1, Int(x + 1))
  case (s1, Int(x), Int(y)) => (s1, Int(x + y + 1))
  case (s1, Unknown, Unknown) => (s1, Unknown)
  case (s1, Unknown, Int(y)) => (s1, Int(y+1))
}

method IncM(p: Pair)
{
  match p {
  	case (s, Int(x)) =>
  	case (s, Unknown) =>
  }
}

method IncM2(s:string, t:EInt)
{
  match (s,t) {
  	case (s, Int(x)) =>
  	case (s, Unknown) =>
  }
}

method IncM3(s1: string, t1: EInt, t2: EInt) {
  match (s1, t1, t2)
  case (s1, Int(x), Unknown) =>
  case (s1, Int(x), Int(y)) =>
  case (s1, Unknown, Unknown) =>
  case (s1, Unknown, Int(y)) =>
}

method IncM4(t: Triple) {
  match t
  case (s1, Int(x), Unknown) =>
  case (s1, Int(x), Int(y)) =>
  case (s1, Unknown, Unknown) =>
  case (s1, Unknown, Int(y)) =>
}
