// RUN: %testDafnyForEachResolver "%s"


datatype OnOff = On | Off

lemma Test<K>(t: OnOff)
{
  match t
  case On =>
  case Off =>
    // The following once caused a crash
    forall x: K {:trigger} {
    }
}
