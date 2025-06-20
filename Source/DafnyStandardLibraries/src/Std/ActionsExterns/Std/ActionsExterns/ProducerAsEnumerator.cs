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

  public class ProducerAsEnumerator<T> : IEnumerator<T> {

    private Producer<T> producer;
    private _IOption<T> next;

    public ProducerAsEnumerator(Producer<T> producer) {
      this.producer = producer;
      next = Option<T>.create_None();
    }


    public bool MoveNext() {
      next = producer.Invoke(Tuple0.Default());
      return next.is_Some;
    }

    public T Current { get {
      if (next.is_Some) {
        return next.dtor_value;
      } else {
        throw new System.InvalidOperationException("Current is undefined");
      }
    } }

    object IEnumerator.Current
    {
        get { return Current; }
    }

    public void Reset() {
      throw new System.NotSupportedException("Reset is not supported");
    }

    void IDisposable.Dispose() { }
  }

}