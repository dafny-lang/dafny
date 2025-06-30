/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

namespace Std.ActionsExterns {

  using Dafny;

  using Std.Producers;

  public partial class __default {
   
    public static Producer<T> MakeSetReader<T>(ISet<T> s) {
      return new EnumeratorAsProducer<T>(s.Elements.GetEnumerator());
    }
  }
}