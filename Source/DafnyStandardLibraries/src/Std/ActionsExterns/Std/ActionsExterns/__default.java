/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package Std.ActionsExterns;

import dafny.DafnySet;
import dafny.TypeDescriptor;

import Std.Producers.Producer;

public class __default {

  public static <T> Producer<T> MakeSetReader(TypeDescriptor<T> td, DafnySet<? extends T> s) {
    return new IteratorAsProducer<T>(td, s.Elements().iterator());
  }
}
