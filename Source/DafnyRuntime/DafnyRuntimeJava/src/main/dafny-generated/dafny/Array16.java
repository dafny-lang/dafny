package dafny;

public final class Array16<T> {
  public final Object[][][][][][][][][][][][][][][] elmts;
  private final dafny.TypeDescriptor<T> elmtType;
  public final int dim0;
  public final int dim1;
  public final int dim2;
  public final int dim3;
  public final int dim4;
  public final int dim5;
  public final int dim6;
  public final int dim7;
  public final int dim8;
  public final int dim9;
  public final int dim10;
  public final int dim11;
  public final int dim12;
  public final int dim13;
  public final int dim14;
  public final int dim15;
  public Array16(dafny.TypeDescriptor<T> elmtType, int dim0, int dim1, int dim2, int dim3, int dim4, int dim5, int dim6, int dim7, int dim8, int dim9, int dim10, int dim11, int dim12, int dim13, int dim14, int dim15, Object[][][][][][][][][][][][][][][] elmts) {
    assert elmts.getClass().isArray();
    this.elmtType = elmtType;
    this.dim0 = dim0;
    this.dim1 = dim1;
    this.dim2 = dim2;
    this.dim3 = dim3;
    this.dim4 = dim4;
    this.dim5 = dim5;
    this.dim6 = dim6;
    this.dim7 = dim7;
    this.dim8 = dim8;
    this.dim9 = dim9;
    this.dim10 = dim10;
    this.dim11 = dim11;
    this.dim12 = dim12;
    this.dim13 = dim13;
    this.dim14 = dim14;
    this.dim15 = dim15;
    this.elmts = elmts;
  }
  public T get(int i0, int i1, int i2, int i3, int i4, int i5, int i6, int i7, int i8, int i9, int i10, int i11, int i12, int i13, int i14, int i15) {
    return elmtType.getArrayElement(elmts[i0][i1][i2][i3][i4][i5][i6][i7][i8][i9][i10][i11][i12][i13][i14], i15);
  }
  public void set(int i0, int i1, int i2, int i3, int i4, int i5, int i6, int i7, int i8, int i9, int i10, int i11, int i12, int i13, int i14, int i15, T value) {
    elmtType.setArrayElement(elmts[i0][i1][i2][i3][i4][i5][i6][i7][i8][i9][i10][i11][i12][i13][i14], i15, value);
  }
  public void fill(T z) {
    for(int i0 = 0; i0 < dim0; i0++) {
      for(int i1 = 0; i1 < dim1; i1++) {
        for(int i2 = 0; i2 < dim2; i2++) {
          for(int i3 = 0; i3 < dim3; i3++) {
            for(int i4 = 0; i4 < dim4; i4++) {
              for(int i5 = 0; i5 < dim5; i5++) {
                for(int i6 = 0; i6 < dim6; i6++) {
                  for(int i7 = 0; i7 < dim7; i7++) {
                    for(int i8 = 0; i8 < dim8; i8++) {
                      for(int i9 = 0; i9 < dim9; i9++) {
                        for(int i10 = 0; i10 < dim10; i10++) {
                          for(int i11 = 0; i11 < dim11; i11++) {
                            for(int i12 = 0; i12 < dim12; i12++) {
                              for(int i13 = 0; i13 < dim13; i13++) {
                                for(int i14 = 0; i14 < dim14; i14++) {
                                  elmtType.fillArray(elmts[i0][i1][i2][i3][i4][i5][i6][i7][i8][i9][i10][i11][i12][i13][i14], z);
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  public Array16 fillThenReturn(T z) {
    fill(z);
    return this;
  }
  @SuppressWarnings({"unchecked", "deprecation"})
  private static final dafny.TypeDescriptor<Array16<?>> TYPE = (dafny.TypeDescriptor<Array16<?>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Array16.class);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T> dafny.TypeDescriptor<Array16<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Array16<T>>) (dafny.TypeDescriptor<?>) TYPE;
  }
}
