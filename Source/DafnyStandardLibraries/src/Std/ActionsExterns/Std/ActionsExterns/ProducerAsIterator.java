/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package Std.ActionsExterns;

import java.util.Iterator;

import Std.Producers.Producer;
import Std.Wrappers.Option;

import dafny.Tuple0;

class ProducerAsIterator<T> implements Iterator<T> {
    private final Producer<T> producer;
    private Option<T> next;

    public ProducerAsIterator(Producer<T> producer) {
        this.producer = producer;
        fetchNext();
    }

    @Override
    public boolean hasNext() {
        return next.is_Some();
    }

    @Override
    public T next() {
        if (!hasNext()) {
            throw new java.util.NoSuchElementException();
        }
        T result = next.dtor_value();
        fetchNext();
        return result;
    }

    private void fetchNext() {
      this.next = producer.Invoke(Tuple0.create());
    }
}
