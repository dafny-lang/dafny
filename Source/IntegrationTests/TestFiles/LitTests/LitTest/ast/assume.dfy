// RUN: ! %testDafnyForEachResolver "%s" -- --allow-axioms=false
// NONUNIFORM: warning will be the same for all back-end
// RUN: ! %verify --standard-libraries --allow-axioms:false "%s" &> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
 assume false;
 assume {:axiom} false;
 
 var xs := { 1, 2 };
 var x :| assume x in xs;

 var ys :- assume Some(3); 
}

/** This datatype is the conventional Some/None datatype that is often used
  in place of a reference or null.
*/
datatype Option<+T> = None | Some(value: T) {

    /** True if is None */
    predicate IsFailure() {
      None?
    }

    /** Converts a None result to an Option value with a different value type. */
    function PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    /** Returns the value encapsulated in Some */
    function Extract(): T
      requires Some?
    {
      value
    }

    /** Returns the value encapsulated in Some or a default value if None */
    function GetOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }

    /** Applies the given function to convert the Option to something else  */
    function Map<FC>(rewrap: Option<T> -> FC): FC
    {
      rewrap(this)
    }
}