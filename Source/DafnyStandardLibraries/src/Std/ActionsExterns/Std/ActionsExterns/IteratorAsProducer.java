/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package Std.ActionsExterns;

import java.math.BigInteger;
import java.util.Iterator;

import Std.Producers.Producer;
import Std.Producers._Companion_Producer;
import Std.Wrappers.Option;

import dafny.Tuple0;
import dafny.TypeDescriptor;

class IteratorAsProducer<T> implements Producer<T> {
    private final TypeDescriptor<T> td;
    private final Iterator<? extends T> iterator;
    private BigInteger producedCount;

    public IteratorAsProducer(TypeDescriptor<T> td, java.util.Iterator<? extends T> iterator) {
        this.td = td;
        this.iterator = iterator;
        this.producedCount = BigInteger.ZERO;
    }

    @Override
    public Option<T> Invoke(Tuple0 i) {
        if (iterator.hasNext()) {
          producedCount = producedCount.add(BigInteger.ONE);
          return Option.create_Some(td, iterator.next());
        } else {
          return Option.create_None(td);
        }
    }

    public void ForEach(Std.Consumers.IConsumer<T> consumer) {
      Std.Producers.__default.DefaultForEach(td, this, consumer);
    }

    public void Fill(Std.Consumers.Consumer<T> consumer) {
      Std.Producers.__default.DefaultFill(td, this, consumer);
    }

    public BigInteger ProducedCount() {
      return producedCount;
    }

    public Option<BigInteger> Remaining() {
      return Option.create_None(TypeDescriptor.BIG_INTEGER);
    }

    public Option<T> Next() {
      return _Companion_Producer.Next(td, this);
    }
  
}