// RUN: %diff "%s" "%s"

module Included {
  import W = Dummy.Z.W
  datatype X = Z()
}