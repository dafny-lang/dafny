/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

namespace Std.ActionsExterns {
  using System.Collections;
  using System.Collections.Generic;

  using Dafny;
  using _System;

  using Std.Producers;
  using Std.Wrappers;

  public class EnumeratorAsProducer<T> : Producer<T> {

    private IEnumerator<T> enumerator;

    public EnumeratorAsProducer(IEnumerator<T> enumerator) {
        this.enumerator = enumerator;
    }

    public _IOption<T> Invoke(_ITuple0 i) {
      if (enumerator.MoveNext()) {
        return Option<T>.create_Some(enumerator.Current);
      } else {
        return Option<T>.create_None();
      }
    }

    public void ForEachRemaining(Std.Consumers.IConsumer<T> consumer) {
      _Companion_Producer<T>.ForEachRemaining(this, consumer);
    }

    public _IOption<T> Next() {
      return _Companion_Producer<T>.Next(this);
    }

  }

}