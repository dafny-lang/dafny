type neg = r : real | r <= 0.0

datatype formula<T> = 
   | Var(z: T)
   | Plus(x: formula<T>, y: formula<T>) 
   | Minus(x: formula<T>, y: formula<T>) 
   | Mult(x: formula<T>, y: formula<T>)
   | Divide(x: formula<T>, y: formula<T>)

function method toReal(x: formula<real>) : real
{
   match x
   case Var(z) => z
   case Plus(y, z) => toReal(y) + toReal(z)
   case Minus(y, z) => toReal(y) - toReal(z)
   case Mult(y, z) => toReal(y) * toReal(z)
   case Divide(y, z) => 
      if toReal(z) == 0.0 then 42.0 else 43.0
}

datatype ChildLineItem = ChildLineItem(negChargeAmount: formula<neg>)

predicate isValidChildLineItem(l: ChildLineItem) 
{ toReal(l.negChargeAmount) <= 0.0 }
