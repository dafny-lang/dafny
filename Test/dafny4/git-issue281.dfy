// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT = ConstrA | ConstrB
datatype Either<S,T> = Left(left: S) | Right(right: T)
datatype Error = IOError

method M() returns (ret: Either<DT,Error>)
    ensures
        match ret
            case Left(x) =>
                match x {
                    case Left(ConstrA) => true
                    case Left(ConstrB) => false
                }
            case Right(_) => true
