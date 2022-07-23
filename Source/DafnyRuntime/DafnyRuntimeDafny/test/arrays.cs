namespace AtomicBoxes {

  public class AtomicBox<T> where T : class {

    volatile T value;

    public static AtomicBox<T> Make(T value) {
      var result = new AtomicBox<T>();
      result.Put(value);
      return result;
    }

    public T Get() => value;
    public void Put(T value) => this.value = value;

  }

}