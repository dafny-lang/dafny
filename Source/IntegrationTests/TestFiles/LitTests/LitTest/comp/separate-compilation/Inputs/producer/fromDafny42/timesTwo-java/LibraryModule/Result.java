// Class Result<T, E>
// Dafny class Result<T, E> compiled into Java
package LibraryModule;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Result<T, E> {
  public Result() { }

  public static <T, E> Result<T, E> Default(T _default_T) {
    dafny.TypeDescriptor<T> _td_T = (dafny.TypeDescriptor<T>)dafny.TypeDescriptor.OBJECT;
    dafny.TypeDescriptor<E> _td_E = (dafny.TypeDescriptor<E>)dafny.TypeDescriptor.OBJECT;
    return LibraryModule.Result.<T, E>create_Success(_default_T);
  }
  public static <T, E> dafny.TypeDescriptor<Result<T, E>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<E> _td_E) {
    return (dafny.TypeDescriptor<Result<T, E>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Result<T, E>>referenceWithInitializer(Result.class, () -> Default(_td_T.defaultValue()));
  }
  public static <T, E> Result<T, E> create_Success(T value) {
    return new Result_Success<T, E>(value);
  }
  public static <T, E> Result<T, E> create_Failure(E error) {
    return new Result_Failure<T, E>(error);
  }
  public boolean is_Success() { return this instanceof Result_Success; }
  public boolean is_Failure() { return this instanceof Result_Failure; }
  public T dtor_value() {
    Result<T, E> d = this;
    return ((Result_Success<T, E>)d)._value;
  }
  public E dtor_error() {
    Result<T, E> d = this;
    return ((Result_Failure<T, E>)d)._error;
  }
}
