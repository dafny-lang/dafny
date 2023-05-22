// RUN: echo ""

module Wrappers {
  datatype Option<+T> = Some(value: T) | None
}