// RUN: echo 'lit should ignore this file' 

module Included {
  import W = Dummy.Z.W
  datatype X = Z()
}