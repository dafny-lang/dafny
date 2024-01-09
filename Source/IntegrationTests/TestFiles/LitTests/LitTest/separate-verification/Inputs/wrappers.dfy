module Wrappers {
  datatype Option<T> = Some(value: T) | None {
    function UnwrapOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }
  }
}