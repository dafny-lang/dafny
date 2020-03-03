using System;
using System.Numerics;
using Xunit;

namespace DafnyRuntimeTests {

    class A {
        
    }

    class B : A {
        
    }

    interface Sequence<out T> {
        int Length();
        T Get(int i);
    }

    class ArraySequence<T> : Sequence<T> {
        private T[] array;

        public ArraySequence(T[] array) {
            this.array = array;
        }
        
        public int Length() {
            return array.Length;
        }

        public T Get(int i) {
            return array[i];
        }
    }
    
    public class UnitTest1 {
        [Fact]
        public void Test1() {
            B[] bs = new B[] { new B() };
            Sequence<A> s = new ArraySequence<B>(bs);
        }
    }
}