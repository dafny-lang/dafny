namespace AtomicBoxes_Compile {

  public class AtomicBox<T> where T : class {

    volatile T value;

    public static AtomicBox<T> Make(T value) {
      // TODO: Should need some kind of runtime check that T : class here
      var result = new AtomicBox<T>();
      result.Put(value);
      return result;
    }

    public T Get() => value;
    public void Put(T value) => this.value = value;

  }

}