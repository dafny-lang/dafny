// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
/* This is a trimmed down version of the original bug. The original program can be found in Issue #227.
   This trimmed version is only for the purpose of testing the type-checking error messages. */

module AbstractMap {

  datatype Constants = Constants
  type View = imap<int, int>
  datatype Variables = Variables

  datatype Step = CompleteSync | SpontaneousCrashStep | Stutter

  ghost predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
      true
  }

  ghost predicate Next(k: Constants, s: Variables, s': Variables)
  {
      true
  }
}

module LogImpl {

  datatype Constants = Constants()
  datatype Variables = Variables()

  datatype Step =
      CrashAndRecover
    | TerminateScan

  ghost predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    true
  }

  ghost predicate Next(k: Constants, s: Variables, s': Variables)
  {
    true
  }

  ghost predicate Inv(k: Constants, s: Variables)
  {
    true
  }

} // module LogImpl


module RefinementProof {
  import opened LogImpl
  import AbstractMap

  ghost function IViews(k: Constants, s: Variables): seq<AbstractMap.View>
    requires Inv(k, s)
  {
    []
  }

  // Refinement to an AbstractMap
  ghost function I(k: Constants, s: Variables): AbstractMap.Variables
    requires Inv(k, s)
  {
    AbstractMap.Variables
  }

  ghost function Ik(k:Constants) : AbstractMap.Constants
  {
    AbstractMap.Constants
  }


  lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
  {
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');

    var step :| NextStep(k, s, s', step);

    match step {
        case TerminateScan => {
            calc {
                Is';
                IViews(k, s); // uncomment this line to witness bizarreness
                Is;
            }
        }
        case _ => {
        }
    }
  }

} // module RefinementProof
