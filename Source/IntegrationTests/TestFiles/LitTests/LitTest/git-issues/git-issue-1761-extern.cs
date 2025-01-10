namespace _module {
  public partial class ABC {
    public ABC(bool x) {
      this.y = x;
    }
    public ABC(bool x, bool z) {
      this.y = x && z;
    }
  }
}