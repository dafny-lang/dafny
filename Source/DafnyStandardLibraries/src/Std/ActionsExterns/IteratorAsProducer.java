/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package Std.ActionsExterns;

import java.util.Iterator;

import Std.Producers.Producer;
import Std.Producers._Companion_Producer;
import Std.Wrappers.Option;

import dafny.Tuple0;
import dafny.TypeDescriptor;

class IteratorAsProducer<T> implements Producer<T> {
    private final TypeDescriptor td;
    private final Iterator<? extends T> iterator;

    public IteratorAsProducer(TypeDescriptor td, java.util.Iterator<? extends T> iterator) {
        this.td = td;
        this.iterator = iterator;
    }

    @Override
    public Option<T> Invoke(Tuple0 i) {
        if (iterator.hasNext()) {
          return Option.create_Some(td, iterator.next());
        } else {
          return Option.create_None(td);
        }
    }

    public void ForEach(Std.Consumers.IConsumer<T> consumer) {
      _Companion_Producer.ForEach(td, this, consumer);
    }

    public Option<T> Next() {
      return _Companion_Producer.Next(td, this);
    }
  
}