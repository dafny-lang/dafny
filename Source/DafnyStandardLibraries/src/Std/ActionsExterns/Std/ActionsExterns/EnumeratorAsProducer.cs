/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

namespace Std.ActionsExterns {
  using System.Collections;
  using System.Collections.Generic;
  using System.Numerics;

  using Dafny;
  using _System;

  using Std.Producers;
  using Std.Wrappers;

  public class EnumeratorAsProducer<T> : Producer<T> {

    private IEnumerator<T> enumerator;
    private BigInteger producedCount;

    public EnumeratorAsProducer(IEnumerator<T> enumerator) {
        this.enumerator = enumerator;
        this.producedCount = 0;
    }

    public _IOption<T> Invoke(_ITuple0 i) {
      if (enumerator.MoveNext()) {
        producedCount = producedCount + 1;
        return Option<T>.create_Some(enumerator.Current);
      } else {
        return Option<T>.create_None();
      }
    }

    public BigInteger ProducedCount() {
      return producedCount;
    }

    public _IOption<BigInteger> Remaining() {
      return Option<BigInteger>.create_None();
    }

    public void ForEach(Std.Consumers.IConsumer<T> consumer) {
      Std.Producers.__default.DefaultForEach(this, consumer);
    }

    public void Fill(Std.Consumers.Consumer<T> consumer) {
      Std.Producers.__default.DefaultFill(this, consumer);
    }

    public _IOption<T> Next() {
      return _Companion_Producer<T>.Next(this);
    }

  }

}