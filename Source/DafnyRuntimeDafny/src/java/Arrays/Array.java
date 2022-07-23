package Arrays;

public class Array<T> {
  private final dafny.Array<T> wrapped;
  private final int length;
  
  Array(dafny.Array<T> wrapped, int length) {
    this.wrapped = wrapped;
    this.length = length;
  }

  
}


