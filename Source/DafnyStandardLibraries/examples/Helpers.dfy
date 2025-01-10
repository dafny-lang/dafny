/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helpers {
  import opened Std.Wrappers
  // TODO: consider tweaking /testContracts to support this use case better.
  method AssertAndExpect(p: bool, maybeMsg: Option<string> := None) requires p {
    match maybeMsg {
      case None => {
        expect p;
      }
      case Some(msg) => {
        expect p, msg;
      }
    }
  }
}
