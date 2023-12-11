// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
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
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
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
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Std.Wrappers {

  public partial class __default {
    public static Std.Wrappers._IOutcomeResult<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Std.Wrappers.OutcomeResult<__E>.create_Pass_k();
      } else {
        return Std.Wrappers.OutcomeResult<__E>.create_Fail_k(error);
      }
    }
  }

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    bool IsFailure();
    Std.Wrappers._IOption<__U> PropagateFailure<__U>();
    T Extract();
    Std.Wrappers._IResult<T, __E> ToResult<__E>(__E error);
    Std.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error);
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() {
    }
    public static Std.Wrappers._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOption<T>>(Std.Wrappers.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d)._value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public bool IsFailure() {
      return (this).is_None;
    }
    public Std.Wrappers._IOption<__U> PropagateFailure<__U>() {
      return Std.Wrappers.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
    public static T GetOr(Std.Wrappers._IOption<T> _this, T @default) {
      Std.Wrappers._IOption<T> _source0 = _this;
      if (_source0.is_None) {
        return @default;
      } else {
        T _0___mcc_h0 = _source0.dtor_value;
        T _1_v = _0___mcc_h0;
        return _1_v;
      }
    }
    public Std.Wrappers._IResult<T, __E> ToResult<__E>(__E error) {
      Std.Wrappers._IOption<T> _source1 = this;
      if (_source1.is_None) {
        return Std.Wrappers.Result<T, __E>.create_Failure(error);
      } else {
        T _2___mcc_h0 = _source1.dtor_value;
        T _3_v = _2___mcc_h0;
        return Std.Wrappers.Result<T, __E>.create_Success(_3_v);
      }
    }
    public Std.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error) {
      Std.Wrappers._IOption<T> _source2 = this;
      if (_source2.is_None) {
        return Std.Wrappers.Outcome<__E>.create_Fail(error);
      } else {
        T _4___mcc_h0 = _source2.dtor_value;
        T _5_v = _4___mcc_h0;
        return Std.Wrappers.Outcome<__E>.create_Pass();
      }
    }
    public static __FC Map<__FC>(Std.Wrappers._IOption<T> _this, Func<Std.Wrappers._IOption<T>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IOption<T>, __FC>>(rewrap)(_this);
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() : base() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _value;
    public Option_Some(T @value) : base() {
      this._value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Option_Some<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out R, out E> {
    bool is_Success { get; }
    bool is_Failure { get; }
    R dtor_value { get; }
    E dtor_error { get; }
    _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    bool IsFailure();
    Std.Wrappers._IResult<__U, E> PropagateFailure<__U>();
    R Extract();
    Std.Wrappers._IOption<R> ToOption();
    Std.Wrappers._IOutcome<E> ToOutcome();
  }
  public abstract class Result<R, E> : _IResult<R, E> {
    public Result() {
    }
    public static Std.Wrappers._IResult<R, E> Default(R _default_R) {
      return create_Success(_default_R);
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IResult<R, E>> _TypeDescriptor(Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Std.Wrappers._IResult<R, E>>(Std.Wrappers.Result<R, E>.Default(_td_R.Default()));
    }
    public static _IResult<R, E> create_Success(R @value) {
      return new Result_Success<R, E>(@value);
    }
    public static _IResult<R, E> create_Failure(E error) {
      return new Result_Failure<R, E>(error);
    }
    public bool is_Success { get { return this is Result_Success<R, E>; } }
    public bool is_Failure { get { return this is Result_Failure<R, E>; } }
    public R dtor_value {
      get {
        var d = this;
        return ((Result_Success<R, E>)d)._value;
      }
    }
    public E dtor_error {
      get {
        var d = this;
        return ((Result_Failure<R, E>)d)._error;
      }
    }
    public abstract _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Std.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return Std.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
    public R Extract() {
      return (this).dtor_value;
    }
    public static R GetOr(Std.Wrappers._IResult<R, E> _this, R @default) {
      Std.Wrappers._IResult<R, E> _source3 = _this;
      if (_source3.is_Success) {
        R _6___mcc_h0 = _source3.dtor_value;
        R _7_s = _6___mcc_h0;
        return _7_s;
      } else {
        E _8___mcc_h1 = _source3.dtor_error;
        E _9_e = _8___mcc_h1;
        return @default;
      }
    }
    public Std.Wrappers._IOption<R> ToOption() {
      Std.Wrappers._IResult<R, E> _source4 = this;
      if (_source4.is_Success) {
        R _10___mcc_h0 = _source4.dtor_value;
        R _11_s = _10___mcc_h0;
        return Std.Wrappers.Option<R>.create_Some(_11_s);
      } else {
        E _12___mcc_h1 = _source4.dtor_error;
        E _13_e = _12___mcc_h1;
        return Std.Wrappers.Option<R>.create_None();
      }
    }
    public Std.Wrappers._IOutcome<E> ToOutcome() {
      Std.Wrappers._IResult<R, E> _source5 = this;
      if (_source5.is_Success) {
        R _14___mcc_h0 = _source5.dtor_value;
        R _15_s = _14___mcc_h0;
        return Std.Wrappers.Outcome<E>.create_Pass();
      } else {
        E _16___mcc_h1 = _source5.dtor_error;
        E _17_e = _16___mcc_h1;
        return Std.Wrappers.Outcome<E>.create_Fail(_17_e);
      }
    }
    public static __FC Map<__FC>(Std.Wrappers._IResult<R, E> _this, Func<Std.Wrappers._IResult<R, E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IResult<R, E>, __FC>>(rewrap)(_this);
    }
    public static Std.Wrappers._IResult<R, __NewE> MapFailure<__NewE>(Std.Wrappers._IResult<R, E> _this, Func<E, __NewE> reWrap) {
      Std.Wrappers._IResult<R, E> _source6 = _this;
      if (_source6.is_Success) {
        R _18___mcc_h0 = _source6.dtor_value;
        R _19_s = _18___mcc_h0;
        return Std.Wrappers.Result<R, __NewE>.create_Success(_19_s);
      } else {
        E _20___mcc_h1 = _source6.dtor_error;
        E _21_e = _20___mcc_h1;
        return Std.Wrappers.Result<R, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(reWrap)(_21_e));
      }
    }
  }
  public class Result_Success<R, E> : Result<R, E> {
    public readonly R _value;
    public Result_Success(R @value) : base() {
      this._value = @value;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Success<__R, __E>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Result_Success<R, E>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<R, E> : Result<R, E> {
    public readonly E _error;
    public Result_Failure(E error) : base() {
      this._error = error;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Failure<__R, __E>(converter1(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Result_Failure<R, E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<out E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Std.Wrappers._IOutcome<E> PropagateFailure();
    Std.Wrappers._IOption<__R> ToOption<__R>(__R r);
    Std.Wrappers._IResult<__R, E> ToResult<__R>(__R r);
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() {
    }
    public static Std.Wrappers._IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOutcome<E>>(Std.Wrappers.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d)._error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Std.Wrappers._IOutcome<E> PropagateFailure() {
      return this;
    }
    public Std.Wrappers._IOption<__R> ToOption<__R>(__R r) {
      Std.Wrappers._IOutcome<E> _source7 = this;
      if (_source7.is_Pass) {
        return Std.Wrappers.Option<__R>.create_Some(r);
      } else {
        E _22___mcc_h0 = _source7.dtor_error;
        E _23_e = _22___mcc_h0;
        return Std.Wrappers.Option<__R>.create_None();
      }
    }
    public Std.Wrappers._IResult<__R, E> ToResult<__R>(__R r) {
      Std.Wrappers._IOutcome<E> _source8 = this;
      if (_source8.is_Pass) {
        return Std.Wrappers.Result<__R, E>.create_Success(r);
      } else {
        E _24___mcc_h0 = _source8.dtor_error;
        E _25_e = _24___mcc_h0;
        return Std.Wrappers.Result<__R, E>.create_Failure(_25_e);
      }
    }
    public static __FC Map<__FC>(Std.Wrappers._IOutcome<E> _this, Func<Std.Wrappers._IOutcome<E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IOutcome<E>, __FC>>(rewrap)(_this);
    }
    public static Std.Wrappers._IResult<__T, __NewE> MapFailure<__T, __NewE>(Std.Wrappers._IOutcome<E> _this, Func<E, __NewE> rewrap, __T @default)
    {
      Std.Wrappers._IOutcome<E> _source9 = _this;
      if (_source9.is_Pass) {
        return Std.Wrappers.Result<__T, __NewE>.create_Success(@default);
      } else {
        E _26___mcc_h0 = _source9.dtor_error;
        E _27_e = _26___mcc_h0;
        return Std.Wrappers.Result<__T, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(rewrap)(_27_e));
      }
    }
    public static Std.Wrappers._IOutcome<E> Need(bool condition, E error)
    {
      if (condition) {
        return Std.Wrappers.Outcome<E>.create_Pass();
      } else {
        return Std.Wrappers.Outcome<E>.create_Fail(error);
      }
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() : base() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E _error;
    public Outcome_Fail(E error) : base() {
      this._error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Outcome_Fail<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcomeResult<out E> {
    bool is_Pass_k { get; }
    bool is_Fail_k { get; }
    E dtor_error { get; }
    _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Std.Wrappers._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class OutcomeResult<E> : _IOutcomeResult<E> {
    public OutcomeResult() {
    }
    public static Std.Wrappers._IOutcomeResult<E> Default() {
      return create_Pass_k();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOutcomeResult<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOutcomeResult<E>>(Std.Wrappers.OutcomeResult<E>.Default());
    }
    public static _IOutcomeResult<E> create_Pass_k() {
      return new OutcomeResult_Pass_k<E>();
    }
    public static _IOutcomeResult<E> create_Fail_k(E error) {
      return new OutcomeResult_Fail_k<E>(error);
    }
    public bool is_Pass_k { get { return this is OutcomeResult_Pass_k<E>; } }
    public bool is_Fail_k { get { return this is OutcomeResult_Fail_k<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((OutcomeResult_Fail_k<E>)d)._error;
      }
    }
    public abstract _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail_k;
    }
    public Std.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return Std.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class OutcomeResult_Pass_k<E> : OutcomeResult<E> {
    public OutcomeResult_Pass_k() : base() {
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Pass_k<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.OutcomeResult_Pass_k<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Pass'";
      return s;
    }
  }
  public class OutcomeResult_Fail_k<E> : OutcomeResult<E> {
    public readonly E _error;
    public OutcomeResult_Fail_k(E error) : base() {
      this._error = error;
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Fail_k<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.OutcomeResult_Fail_k<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Fail'";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }
} // end of namespace Std.Wrappers
namespace Std.BoundedInts {

  public partial class __default {
    public static BigInteger TWO__TO__THE__8 { get {
      return new BigInteger(256);
    } }
    public static byte UINT8__MAX { get {
      return (byte)(255);
    } }
    public static BigInteger TWO__TO__THE__16 { get {
      return new BigInteger(65536);
    } }
    public static ushort UINT16__MAX { get {
      return (ushort)(65535);
    } }
    public static BigInteger TWO__TO__THE__32 { get {
      return new BigInteger(4294967296L);
    } }
    public static uint UINT32__MAX { get {
      return 4294967295U;
    } }
    public static BigInteger TWO__TO__THE__64 { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static ulong UINT64__MAX { get {
      return 18446744073709551615UL;
    } }
    public static BigInteger TWO__TO__THE__7 { get {
      return new BigInteger(128);
    } }
    public static sbyte INT8__MIN { get {
      return (sbyte)(-128);
    } }
    public static sbyte INT8__MAX { get {
      return (sbyte)(127);
    } }
    public static BigInteger TWO__TO__THE__15 { get {
      return new BigInteger(32768);
    } }
    public static short INT16__MIN { get {
      return (short)(-32768);
    } }
    public static short INT16__MAX { get {
      return (short)(32767);
    } }
    public static BigInteger TWO__TO__THE__31 { get {
      return new BigInteger(2147483648L);
    } }
    public static int INT32__MIN { get {
      return -2147483648;
    } }
    public static int INT32__MAX { get {
      return 2147483647;
    } }
    public static BigInteger TWO__TO__THE__63 { get {
      return new BigInteger(9223372036854775808UL);
    } }
    public static long INT64__MIN { get {
      return -9223372036854775808L;
    } }
    public static long INT64__MAX { get {
      return 9223372036854775807L;
    } }
    public static byte NAT8__MAX { get {
      return (byte)(127);
    } }
    public static ushort NAT16__MAX { get {
      return (ushort)(32767);
    } }
    public static uint NAT32__MAX { get {
      return 2147483647U;
    } }
    public static ulong NAT64__MAX { get {
      return 9223372036854775807UL;
    } }
    public static BigInteger TWO__TO__THE__128 { get {
      return BigInteger.Parse("340282366920938463463374607431768211456");
    } }
    public static BigInteger TWO__TO__THE__127 { get {
      return BigInteger.Parse("170141183460469231731687303715884105728");
    } }
    public static BigInteger TWO__TO__THE__0 { get {
      return BigInteger.One;
    } }
    public static BigInteger TWO__TO__THE__1 { get {
      return new BigInteger(2);
    } }
    public static BigInteger TWO__TO__THE__2 { get {
      return new BigInteger(4);
    } }
    public static BigInteger TWO__TO__THE__4 { get {
      return new BigInteger(16);
    } }
    public static BigInteger TWO__TO__THE__5 { get {
      return new BigInteger(32);
    } }
    public static BigInteger TWO__TO__THE__24 { get {
      return new BigInteger(16777216);
    } }
    public static BigInteger TWO__TO__THE__40 { get {
      return new BigInteger(1099511627776L);
    } }
    public static BigInteger TWO__TO__THE__48 { get {
      return new BigInteger(281474976710656L);
    } }
    public static BigInteger TWO__TO__THE__56 { get {
      return new BigInteger(72057594037927936L);
    } }
    public static BigInteger TWO__TO__THE__256 { get {
      return BigInteger.Parse("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    } }
    public static BigInteger TWO__TO__THE__512 { get {
      return BigInteger.Parse("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    } }
  }

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint128 {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int128 {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat128 {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class opt__byte {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.BoundedInts
namespace Std.Base64 {

  public partial class __default {
    public static bool IsBase64Char(Dafny.Rune c) {
      return (((((c) == (new Dafny.Rune('+'))) || ((c) == (new Dafny.Rune('/')))) || (((new Dafny.Rune('0')) <= (c)) && ((c) <= (new Dafny.Rune('9'))))) || (((new Dafny.Rune('A')) <= (c)) && ((c) <= (new Dafny.Rune('Z'))))) || (((new Dafny.Rune('a')) <= (c)) && ((c) <= (new Dafny.Rune('z'))));
    }
    public static bool IsUnpaddedBase64String(Dafny.ISequence<Dafny.Rune> s) {
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_28_s) => Dafny.Helpers.Quantifier<Dafny.Rune>((_28_s).UniqueElements, true, (((_forall_var_0) => {
        Dafny.Rune _29_k = (Dafny.Rune)_forall_var_0;
        return !((_28_s).Contains(_29_k)) || (Std.Base64.__default.IsBase64Char(_29_k));
      }))))(s));
    }
    public static Dafny.Rune IndexToChar(byte i) {
      if ((i) == ((byte)(63))) {
        return new Dafny.Rune('/');
      } else if ((i) == ((byte)(62))) {
        return new Dafny.Rune('+');
      } else if ((((byte)(52)) <= (i)) && ((i) <= ((byte)(61)))) {
        return new Dafny.Rune((int)(unchecked((byte)(((byte)((i) - ((byte)(4)))) & (byte)0x3F))));
      } else if ((((byte)(26)) <= (i)) && ((i) <= ((byte)(51)))) {
        return Dafny.Helpers.AddRunes(new Dafny.Rune((int)(i)), new Dafny.Rune((int)(new BigInteger(71))));
      } else {
        return Dafny.Helpers.AddRunes(new Dafny.Rune((int)(i)), new Dafny.Rune((int)(new BigInteger(65))));
      }
    }
    public static byte CharToIndex(Dafny.Rune c) {
      if ((c) == (new Dafny.Rune('/'))) {
        return (byte)(63);
      } else if ((c) == (new Dafny.Rune('+'))) {
        return (byte)(62);
      } else if (((new Dafny.Rune('0')) <= (c)) && ((c) <= (new Dafny.Rune('9')))) {
        return (byte)((Dafny.Helpers.AddRunes(c, new Dafny.Rune((int)(new BigInteger(4))))).Value);
      } else if (((new Dafny.Rune('a')) <= (c)) && ((c) <= (new Dafny.Rune('z')))) {
        return (byte)((Dafny.Helpers.SubtractRunes(c, new Dafny.Rune((int)(new BigInteger(71))))).Value);
      } else {
        return (byte)((Dafny.Helpers.SubtractRunes(c, new Dafny.Rune((int)(new BigInteger(65))))).Value);
      }
    }
    public static Dafny.ISequence<byte> BV24ToSeq(uint x) {
      byte _30_b0 = (byte)(((x) >> ((int)((byte)(16)))) & (255U));
      byte _31_b1 = (byte)(((x) >> ((int)((byte)(8)))) & (255U));
      byte _32_b2 = (byte)((x) & (255U));
      return Dafny.Sequence<byte>.FromElements(_30_b0, _31_b1, _32_b2);
    }
    public static uint SeqToBV24(Dafny.ISequence<byte> x) {
      return ((unchecked((uint)((((uint)((x).Select(BigInteger.Zero))) << ((int)((byte)(16)))) & (uint)0xFFFFFFU))) | (unchecked((uint)((((uint)((x).Select(BigInteger.One))) << ((int)((byte)(8)))) & (uint)0xFFFFFFU)))) | ((uint)((x).Select(new BigInteger(2))));
    }
    public static Dafny.ISequence<byte> BV24ToIndexSeq(uint x) {
      byte _33_b0 = (byte)(((x) >> ((int)((byte)(18)))) & (63U));
      byte _34_b1 = (byte)(((x) >> ((int)((byte)(12)))) & (63U));
      byte _35_b2 = (byte)(((x) >> ((int)((byte)(6)))) & (63U));
      byte _36_b3 = (byte)((x) & (63U));
      return Dafny.Sequence<byte>.FromElements(_33_b0, _34_b1, _35_b2, _36_b3);
    }
    public static uint IndexSeqToBV24(Dafny.ISequence<byte> x) {
      return (((unchecked((uint)((((uint)((x).Select(BigInteger.Zero))) << ((int)((byte)(18)))) & (uint)0xFFFFFFU))) | (unchecked((uint)((((uint)((x).Select(BigInteger.One))) << ((int)((byte)(12)))) & (uint)0xFFFFFFU)))) | (unchecked((uint)((((uint)((x).Select(new BigInteger(2)))) << ((int)((byte)(6)))) & (uint)0xFFFFFFU)))) | ((uint)((x).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> DecodeBlock(Dafny.ISequence<byte> s) {
      return Std.Base64.__default.BV24ToSeq(Std.Base64.__default.IndexSeqToBV24(s));
    }
    public static Dafny.ISequence<byte> EncodeBlock(Dafny.ISequence<byte> s) {
      return Std.Base64.__default.BV24ToIndexSeq(Std.Base64.__default.SeqToBV24(s));
    }
    public static Dafny.ISequence<byte> DecodeRecursively(Dafny.ISequence<byte> s)
    {
      Dafny.ISequence<byte> b = Dafny.Sequence<byte>.Empty;
      BigInteger _37_resultLength;
      _37_resultLength = (Dafny.Helpers.EuclideanDivision(new BigInteger((s).Count), new BigInteger(4))) * (new BigInteger(3));
      byte[] _38_result;
      Func<BigInteger, byte> _init0 = ((System.Func<BigInteger, byte>)((_39_i) => {
        return (byte)(0);
      }));
      byte[] _nw0 = new byte[Dafny.Helpers.ToIntChecked(_37_resultLength, "array size exceeds memory limit")];
      for (var _i0_0 = 0; _i0_0 < new BigInteger(_nw0.Length); _i0_0++) {
        _nw0[(int)(_i0_0)] = _init0(_i0_0);
      }
      _38_result = _nw0;
      BigInteger _40_i;
      _40_i = new BigInteger((s).Count);
      BigInteger _41_j;
      _41_j = _37_resultLength;
      while ((_40_i).Sign == 1) {
        _40_i = (_40_i) - (new BigInteger(4));
        _41_j = (_41_j) - (new BigInteger(3));
        Dafny.ISequence<byte> _42_block;
        _42_block = Std.Base64.__default.DecodeBlock((s).Subsequence(_40_i, (_40_i) + (new BigInteger(4))));
        (_38_result)[(int)((_41_j))] = (_42_block).Select(BigInteger.Zero);
        BigInteger _index0 = (_41_j) + (BigInteger.One);
        (_38_result)[(int)(_index0)] = (_42_block).Select(BigInteger.One);
        BigInteger _index1 = (_41_j) + (new BigInteger(2));
        (_38_result)[(int)(_index1)] = (_42_block).Select(new BigInteger(2));
      }
      b = Dafny.Helpers.SeqFromArray(_38_result);
      return b;
    }
    public static Dafny.ISequence<byte> EncodeRecursively(Dafny.ISequence<byte> b)
    {
      Dafny.ISequence<byte> s = Dafny.Sequence<byte>.Empty;
      BigInteger _43_resultLength;
      _43_resultLength = (Dafny.Helpers.EuclideanDivision(new BigInteger((b).Count), new BigInteger(3))) * (new BigInteger(4));
      byte[] _44_result;
      Func<BigInteger, byte> _init1 = ((System.Func<BigInteger, byte>)((_45_i) => {
        return (byte)(0);
      }));
      byte[] _nw1 = new byte[Dafny.Helpers.ToIntChecked(_43_resultLength, "array size exceeds memory limit")];
      for (var _i0_1 = 0; _i0_1 < new BigInteger(_nw1.Length); _i0_1++) {
        _nw1[(int)(_i0_1)] = _init1(_i0_1);
      }
      _44_result = _nw1;
      BigInteger _46_i;
      _46_i = new BigInteger((b).Count);
      BigInteger _47_j;
      _47_j = _43_resultLength;
      while ((_46_i).Sign == 1) {
        _46_i = (_46_i) - (new BigInteger(3));
        _47_j = (_47_j) - (new BigInteger(4));
        Dafny.ISequence<byte> _48_block;
        _48_block = Std.Base64.__default.EncodeBlock((b).Subsequence(_46_i, (_46_i) + (new BigInteger(3))));
        (_44_result)[(int)((_47_j))] = (_48_block).Select(BigInteger.Zero);
        BigInteger _index2 = (_47_j) + (BigInteger.One);
        (_44_result)[(int)(_index2)] = (_48_block).Select(BigInteger.One);
        BigInteger _index3 = (_47_j) + (new BigInteger(2));
        (_44_result)[(int)(_index3)] = (_48_block).Select(new BigInteger(2));
        BigInteger _index4 = (_47_j) + (new BigInteger(3));
        (_44_result)[(int)(_index4)] = (_48_block).Select(new BigInteger(3));
      }
      s = Dafny.Helpers.SeqFromArray(_44_result);
      return s;
    }
    public static Dafny.ISequence<byte> FromCharsToIndices(Dafny.ISequence<Dafny.Rune> s) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim0 = new BigInteger((s).Count);
        var arr0 = new byte[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _49_i = (BigInteger) i0;
          arr0[(int)(_49_i)] = Std.Base64.__default.CharToIndex((s).Select(_49_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr0);
      }))();
    }
    public static Dafny.ISequence<Dafny.Rune> FromIndicesToChars(Dafny.ISequence<byte> b) {
      return ((System.Func<Dafny.ISequence<Dafny.Rune>>) (() => {
        BigInteger dim1 = new BigInteger((b).Count);
        var arr1 = new Dafny.Rune[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
        for (int i1 = 0; i1 < dim1; i1++) {
          var _50_i = (BigInteger) i1;
          arr1[(int)(_50_i)] = Std.Base64.__default.IndexToChar((b).Select(_50_i));
        }
        return Dafny.Sequence<Dafny.Rune>.FromArray(arr1);
      }))();
    }
    public static Dafny.ISequence<byte> DecodeUnpadded(Dafny.ISequence<Dafny.Rune> s) {
      return Std.Base64.__default.DecodeRecursively(Std.Base64.__default.FromCharsToIndices(s));
    }
    public static Dafny.ISequence<Dafny.Rune> EncodeUnpadded(Dafny.ISequence<byte> b) {
      return Std.Base64.__default.FromIndicesToChars(Std.Base64.__default.EncodeRecursively(b));
    }
    public static bool Is1Padding(Dafny.ISequence<Dafny.Rune> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Std.Base64.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Std.Base64.__default.IsBase64Char((s).Select(BigInteger.One)))) && (Std.Base64.__default.IsBase64Char((s).Select(new BigInteger(2))))) && (((byte)((Std.Base64.__default.CharToIndex((s).Select(new BigInteger(2)))) & ((byte)(3)))) == ((byte)(0)))) && (((s).Select(new BigInteger(3))) == (new Dafny.Rune('=')));
    }
    public static Dafny.ISequence<byte> Decode1Padding(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<byte> _51_d = Std.Base64.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Std.Base64.__default.CharToIndex((s).Select(BigInteger.Zero)), Std.Base64.__default.CharToIndex((s).Select(BigInteger.One)), Std.Base64.__default.CharToIndex((s).Select(new BigInteger(2))), (byte)(0)));
      return Dafny.Sequence<byte>.FromElements((_51_d).Select(BigInteger.Zero), (_51_d).Select(BigInteger.One));
    }
    public static Dafny.ISequence<Dafny.Rune> Encode1Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _52_e = Std.Base64.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), (b).Select(BigInteger.One), (byte)(0)));
      return Dafny.Sequence<Dafny.Rune>.FromElements(Std.Base64.__default.IndexToChar((_52_e).Select(BigInteger.Zero)), Std.Base64.__default.IndexToChar((_52_e).Select(BigInteger.One)), Std.Base64.__default.IndexToChar((_52_e).Select(new BigInteger(2))), new Dafny.Rune('='));
    }
    public static bool Is2Padding(Dafny.ISequence<Dafny.Rune> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Std.Base64.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Std.Base64.__default.IsBase64Char((s).Select(BigInteger.One)))) && (((byte)((Std.Base64.__default.CharToIndex((s).Select(BigInteger.One))) % ((byte)(16)))) == ((byte)(0)))) && (((s).Select(new BigInteger(2))) == (new Dafny.Rune('=')))) && (((s).Select(new BigInteger(3))) == (new Dafny.Rune('=')));
    }
    public static Dafny.ISequence<byte> Decode2Padding(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<byte> _53_d = Std.Base64.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Std.Base64.__default.CharToIndex((s).Select(BigInteger.Zero)), Std.Base64.__default.CharToIndex((s).Select(BigInteger.One)), (byte)(0), (byte)(0)));
      return Dafny.Sequence<byte>.FromElements((_53_d).Select(BigInteger.Zero));
    }
    public static Dafny.ISequence<Dafny.Rune> Encode2Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _54_e = Std.Base64.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), (byte)(0), (byte)(0)));
      return Dafny.Sequence<Dafny.Rune>.FromElements(Std.Base64.__default.IndexToChar((_54_e).Select(BigInteger.Zero)), Std.Base64.__default.IndexToChar((_54_e).Select(BigInteger.One)), new Dafny.Rune('='), new Dafny.Rune('='));
    }
    public static bool IsBase64String(Dafny.ISequence<Dafny.Rune> s) {
      BigInteger _55_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && ((Std.Base64.__default.IsUnpaddedBase64String(s)) || ((Std.Base64.__default.IsUnpaddedBase64String((s).Take(_55_finalBlockStart))) && ((Std.Base64.__default.Is1Padding((s).Drop(_55_finalBlockStart))) || (Std.Base64.__default.Is2Padding((s).Drop(_55_finalBlockStart))))));
    }
    public static Dafny.ISequence<byte> DecodeValid(Dafny.ISequence<Dafny.Rune> s) {
      if ((s).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        BigInteger _56_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
        Dafny.ISequence<Dafny.Rune> _57_prefix = (s).Take(_56_finalBlockStart);
        Dafny.ISequence<Dafny.Rune> _58_suffix = (s).Drop(_56_finalBlockStart);
        if (Std.Base64.__default.Is1Padding(_58_suffix)) {
          return Dafny.Sequence<byte>.Concat(Std.Base64.__default.DecodeUnpadded(_57_prefix), Std.Base64.__default.Decode1Padding(_58_suffix));
        } else if (Std.Base64.__default.Is2Padding(_58_suffix)) {
          return Dafny.Sequence<byte>.Concat(Std.Base64.__default.DecodeUnpadded(_57_prefix), Std.Base64.__default.Decode2Padding(_58_suffix));
        } else {
          return Std.Base64.__default.DecodeUnpadded(s);
        }
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>> DecodeBV(Dafny.ISequence<Dafny.Rune> s) {
      if (Std.Base64.__default.IsBase64String(s)) {
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Success(Std.Base64.__default.DecodeValid(s));
      } else {
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The encoding is malformed"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> EncodeBV(Dafny.ISequence<byte> b) {
      if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))).Sign == 0) {
        return Std.Base64.__default.EncodeUnpadded(b);
      } else if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))) == (BigInteger.One)) {
        Dafny.ISequence<Dafny.Rune> _59_s1 = Std.Base64.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (BigInteger.One)));
        Dafny.ISequence<Dafny.Rune> _60_s2 = Std.Base64.__default.Encode2Padding((b).Drop((new BigInteger((b).Count)) - (BigInteger.One)));
        return Dafny.Sequence<Dafny.Rune>.Concat(_59_s1, _60_s2);
      } else {
        Dafny.ISequence<Dafny.Rune> _61_s1 = Std.Base64.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (new BigInteger(2))));
        Dafny.ISequence<Dafny.Rune> _62_s2 = Std.Base64.__default.Encode1Padding((b).Drop((new BigInteger((b).Count)) - (new BigInteger(2))));
        return Dafny.Sequence<Dafny.Rune>.Concat(_61_s1, _62_s2);
      }
    }
    public static Dafny.ISequence<byte> UInt8sToBVs(Dafny.ISequence<byte> u) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim2 = new BigInteger((u).Count);
        var arr2 = new byte[Dafny.Helpers.ToIntChecked(dim2, "array size exceeds memory limit")];
        for (int i2 = 0; i2 < dim2; i2++) {
          var _63_i = (BigInteger) i2;
          arr2[(int)(_63_i)] = (byte)((u).Select(_63_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr2);
      }))();
    }
    public static Dafny.ISequence<byte> BVsToUInt8s(Dafny.ISequence<byte> b) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim3 = new BigInteger((b).Count);
        var arr3 = new byte[Dafny.Helpers.ToIntChecked(dim3, "array size exceeds memory limit")];
        for (int i3 = 0; i3 < dim3; i3++) {
          var _64_i = (BigInteger) i3;
          arr3[(int)(_64_i)] = (byte)((b).Select(_64_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr3);
      }))();
    }
    public static Dafny.ISequence<Dafny.Rune> Encode(Dafny.ISequence<byte> u) {
      return Std.Base64.__default.EncodeBV(Std.Base64.__default.UInt8sToBVs(u));
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>> Decode(Dafny.ISequence<Dafny.Rune> s) {
      if (Std.Base64.__default.IsBase64String(s)) {
        Dafny.ISequence<byte> _65_b = Std.Base64.__default.DecodeValid(s);
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Success(Std.Base64.__default.BVsToUInt8s(_65_b));
      } else {
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The encoding is malformed"));
      }
    }
  }
} // end of namespace Std.Base64
namespace Std.Relations {

} // end of namespace Std.Relations
namespace Std.Math {

  public partial class __default {
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger Min3(BigInteger a, BigInteger b, BigInteger c)
    {
      return Std.Math.__default.Min(a, Std.Math.__default.Min(b, c));
    }
    public static BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
    public static BigInteger Max3(BigInteger a, BigInteger b, BigInteger c)
    {
      return Std.Math.__default.Max(a, Std.Math.__default.Max(b, c));
    }
    public static BigInteger Abs(BigInteger a) {
      if ((a).Sign == -1) {
        return (BigInteger.Zero) - (a);
      } else {
        return a;
      }
    }
  }
} // end of namespace Std.Math
namespace Std.Collections.Seq {

  public partial class __default {
    public static __T First<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select(BigInteger.Zero);
    }
    public static Dafny.ISequence<__T> DropFirst<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Drop(BigInteger.One);
    }
    public static __T Last<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static Dafny.ISequence<__T> DropLast<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static __T[] ToArray<__T>(Dafny.ISequence<__T> xs)
    {
      __T[] a = new __T[0];
      Func<BigInteger, __T> _init2 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_66_xs) => ((System.Func<BigInteger, __T>)((_67_i) => {
        return (_66_xs).Select(_67_i);
      })))(xs);
      __T[] _nw2 = new __T[Dafny.Helpers.ToIntChecked(new BigInteger((xs).Count), "array size exceeds memory limit")];
      for (var _i0_2 = 0; _i0_2 < new BigInteger(_nw2.Length); _i0_2++) {
        _nw2[(int)(_i0_2)] = _init2(_i0_2);
      }
      a = _nw2;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> xs) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_68_xs) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_68_xs).Elements) {
          __T _69_x = (__T)_compr_0;
          if ((_68_xs).Contains(_69_x)) {
            _coll0.Add(_69_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(xs);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      BigInteger _70___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_70___accumulator);
      } else {
        _70___accumulator = (_70___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in0 = (xs).Drop(BigInteger.One);
        __T _in1 = v;
        xs = _in0;
        v = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Option<BigInteger>.create_None();
      } else if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return Std.Wrappers.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Std.Wrappers._IOption<BigInteger> _71_o_k = Std.Collections.Seq.__default.IndexOfOption<__T>((xs).Drop(BigInteger.One), v);
        if ((_71_o_k).is_Some) {
          return Std.Wrappers.Option<BigInteger>.create_Some(((_71_o_k).dtor_value) + (BigInteger.One));
        } else {
          return Std.Wrappers.Option<BigInteger>.create_None();
        }
      }
    }
    public static BigInteger LastIndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)), v)) {
        return (new BigInteger((xs).Count)) - (BigInteger.One);
      } else {
        Dafny.ISequence<__T> _in2 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in3 = v;
        xs = _in2;
        v = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Option<BigInteger>.create_None();
      } else if (object.Equals((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)), v)) {
        return Std.Wrappers.Option<BigInteger>.create_Some((new BigInteger((xs).Count)) - (BigInteger.One));
      } else {
        Dafny.ISequence<__T> _in4 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in5 = v;
        xs = _in4;
        v = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Remove<__T>(Dafny.ISequence<__T> xs, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat((xs).Take(pos), (xs).Drop((pos) + (BigInteger.One)));
    }
    public static Dafny.ISequence<__T> RemoveValue<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      if (!(xs).Contains(v)) {
        return xs;
      } else {
        BigInteger _72_i = Std.Collections.Seq.__default.IndexOf<__T>(xs, v);
        return Dafny.Sequence<__T>.Concat((xs).Take(_72_i), (xs).Drop((_72_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> xs, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((xs).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (xs).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> xs) {
      Dafny.ISequence<__T> _73___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Dafny.Sequence<__T>.Concat(_73___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _73___accumulator = Dafny.Sequence<__T>.Concat(_73___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in6 = (xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One));
        xs = _in6;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _74___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_74___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _74___accumulator = Dafny.Sequence<__T>.Concat(_74___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in7 = v;
        BigInteger _in8 = (length) - (BigInteger.One);
        v = _in7;
        length = _in8;
        goto TAIL_CALL_START;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System._ITuple2<__A, __B>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Std.Collections.Seq.__default.Unzip<__A, __B>(Std.Collections.Seq.__default.DropLast<_System._ITuple2<__A, __B>>(xs));
        Dafny.ISequence<__A> _75_a = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<__B> _76_b = _let_tmp_rhs0.dtor__1;
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_75_a, Dafny.Sequence<__A>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__0)), Dafny.Sequence<__B>.Concat(_76_b, Dafny.Sequence<__B>.FromElements((Std.Collections.Seq.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System._ITuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> xs, Dafny.ISequence<__B> ys)
    {
      Dafny.ISequence<_System._ITuple2<__A, __B>> _77___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(), _77___accumulator);
      } else {
        _77___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(_System.Tuple2<__A, __B>.create(Std.Collections.Seq.__default.Last<__A>(xs), Std.Collections.Seq.__default.Last<__B>(ys))), _77___accumulator);
        Dafny.ISequence<__A> _in9 = Std.Collections.Seq.__default.DropLast<__A>(xs);
        Dafny.ISequence<__B> _in10 = Std.Collections.Seq.__default.DropLast<__B>(ys);
        xs = _in9;
        ys = _in10;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Max(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Std.Math.__default.Max((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.Max((xs).Drop(BigInteger.One)));
      }
    }
    public static BigInteger Min(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Std.Math.__default.Min((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.Min((xs).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _78___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_78___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _78___accumulator = Dafny.Sequence<__T>.Concat(_78___accumulator, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in11 = (xs).Drop(BigInteger.One);
        xs = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _79___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _79___accumulator);
      } else {
        _79___accumulator = Dafny.Sequence<__T>.Concat(Std.Collections.Seq.__default.Last<Dafny.ISequence<__T>>(xs), _79___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in12 = Std.Collections.Seq.__default.DropLast<Dafny.ISequence<__T>>(xs);
        xs = _in12;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__R> _80___accumulator = Dafny.Sequence<__R>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__R>.Concat(_80___accumulator, Dafny.Sequence<__R>.FromElements());
      } else {
        _80___accumulator = Dafny.Sequence<__R>.Concat(_80___accumulator, Dafny.Sequence<__R>.FromElements(Dafny.Helpers.Id<Func<__T, __R>>(f)((xs).Select(BigInteger.Zero))));
        Func<__T, __R> _in13 = f;
        Dafny.ISequence<__T> _in14 = (xs).Drop(BigInteger.One);
        f = _in13;
        xs = _in14;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Std.Wrappers._IResult<__R, __E>> f, Dafny.ISequence<__T> xs)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Std.Wrappers._IResult<__R, __E> _81_valueOrError0 = Dafny.Helpers.Id<Func<__T, Std.Wrappers._IResult<__R, __E>>>(f)((xs).Select(BigInteger.Zero));
        if ((_81_valueOrError0).IsFailure()) {
          return (_81_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _82_head = (_81_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__R>, __E> _83_valueOrError1 = Std.Collections.Seq.__default.MapWithResult<__T, __R, __E>(f, (xs).Drop(BigInteger.One));
          if ((_83_valueOrError1).IsFailure()) {
            return (_83_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _84_tail = (_83_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_82_head), _84_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__T> _85___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_85___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _85___accumulator = Dafny.Sequence<__T>.Concat(_85___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((xs).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in15 = f;
        Dafny.ISequence<__T> _in16 = (xs).Drop(BigInteger.One);
        f = _in15;
        xs = _in16;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> xs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in17 = f;
        __A _in18 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in19 = (xs).Drop(BigInteger.One);
        f = _in17;
        init = _in18;
        xs = _in19;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldRight<__A, __T>(Func<__T, __A, __A> f, Dafny.ISequence<__T> xs, __A init)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        return Dafny.Helpers.Id<Func<__T, __A, __A>>(f)((xs).Select(BigInteger.Zero), Std.Collections.Seq.__default.FoldRight<__A, __T>(f, (xs).Drop(BigInteger.One), init));
      }
    }
    public static Dafny.ISequence<__T> SetToSeq<__T>(Dafny.ISet<__T> s)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      xs = Dafny.Sequence<__T>.FromElements();
      Dafny.ISet<__T> _86_left;
      _86_left = s;
      while (!(_86_left).Equals(Dafny.Set<__T>.FromElements())) {
        __T _87_x;
        foreach (__T _assign_such_that_0 in (_86_left).Elements) {
          _87_x = (__T)_assign_such_that_0;
          if ((_86_left).Contains(_87_x)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 7122)");
      after__ASSIGN_SUCH_THAT_0: ;
        _86_left = Dafny.Set<__T>.Difference(_86_left, Dafny.Set<__T>.FromElements(_87_x));
        xs = Dafny.Sequence<__T>.Concat(xs, Dafny.Sequence<__T>.FromElements(_87_x));
      }
      return xs;
    }
    public static Dafny.ISequence<__T> SetToSortedSeq<__T>(Dafny.ISet<__T> s, Func<__T, __T, bool> R)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      Dafny.ISequence<__T> _out0;
      _out0 = Std.Collections.Seq.__default.SetToSeq<__T>(s);
      xs = _out0;
      xs = Std.Collections.Seq.__default.MergeSortBy<__T>(R, xs);
      return xs;
    }
    public static Dafny.ISequence<__T> MergeSortBy<__T>(Func<__T, __T, bool> lessThanOrEq, Dafny.ISequence<__T> a)
    {
      if ((new BigInteger((a).Count)) <= (BigInteger.One)) {
        return a;
      } else {
        BigInteger _88_splitIndex = Dafny.Helpers.EuclideanDivision(new BigInteger((a).Count), new BigInteger(2));
        Dafny.ISequence<__T> _89_left = (a).Take(_88_splitIndex);
        Dafny.ISequence<__T> _90_right = (a).Drop(_88_splitIndex);
        Dafny.ISequence<__T> _91_leftSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _89_left);
        Dafny.ISequence<__T> _92_rightSorted = Std.Collections.Seq.__default.MergeSortBy<__T>(lessThanOrEq, _90_right);
        return Std.Collections.Seq.__default.MergeSortedWith<__T>(_91_leftSorted, _92_rightSorted, lessThanOrEq);
      }
    }
    public static Dafny.ISequence<__T> MergeSortedWith<__T>(Dafny.ISequence<__T> left, Dafny.ISequence<__T> right, Func<__T, __T, bool> lessThanOrEq)
    {
      Dafny.ISequence<__T> _93___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((left).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_93___accumulator, right);
      } else if ((new BigInteger((right).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_93___accumulator, left);
      } else if (Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThanOrEq)((left).Select(BigInteger.Zero), (right).Select(BigInteger.Zero))) {
        _93___accumulator = Dafny.Sequence<__T>.Concat(_93___accumulator, Dafny.Sequence<__T>.FromElements((left).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in20 = (left).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in21 = right;
        Func<__T, __T, bool> _in22 = lessThanOrEq;
        left = _in20;
        right = _in21;
        lessThanOrEq = _in22;
        goto TAIL_CALL_START;
      } else {
        _93___accumulator = Dafny.Sequence<__T>.Concat(_93___accumulator, Dafny.Sequence<__T>.FromElements((right).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in23 = left;
        Dafny.ISequence<__T> _in24 = (right).Drop(BigInteger.One);
        Func<__T, __T, bool> _in25 = lessThanOrEq;
        left = _in23;
        right = _in24;
        lessThanOrEq = _in25;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Collections.Seq
namespace Std.Collections.Array {

  public partial class __default {
    public static Std.Wrappers._IOption<BigInteger> BinarySearch<__T>(__T[] a, __T key, Func<__T, __T, bool> less)
    {
      Std.Wrappers._IOption<BigInteger> r = Std.Wrappers.Option<BigInteger>.Default();
      BigInteger _94_lo;
      BigInteger _95_hi;
      BigInteger _rhs0 = BigInteger.Zero;
      BigInteger _rhs1 = new BigInteger((a).Length);
      _94_lo = _rhs0;
      _95_hi = _rhs1;
      while ((_94_lo) < (_95_hi)) {
        BigInteger _96_mid;
        _96_mid = Dafny.Helpers.EuclideanDivision((_94_lo) + (_95_hi), new BigInteger(2));
        if (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)(key, (a)[(int)(_96_mid)])) {
          _95_hi = _96_mid;
        } else if (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)((a)[(int)(_96_mid)], key)) {
          _94_lo = (_96_mid) + (BigInteger.One);
        } else {
          r = Std.Wrappers.Option<BigInteger>.create_Some(_96_mid);
          return r;
        }
      }
      r = Std.Wrappers.Option<BigInteger>.create_None();
      return r;
      return r;
    }
  }
} // end of namespace Std.Collections.Array
namespace Std.Collections.Imap {

  public partial class __default {
    public static Std.Wrappers._IOption<__Y> Get<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      if ((m).Contains(x)) {
        return Std.Wrappers.Option<__Y>.create_Some(Dafny.Map<__X, __Y>.Select(m,x));
      } else {
        return Std.Wrappers.Option<__Y>.create_None();
      }
    }
  }
} // end of namespace Std.Collections.Imap
namespace Std.Functions {

} // end of namespace Std.Functions
namespace Std.Collections.Iset {

} // end of namespace Std.Collections.Iset
namespace Std.Collections.Map {

  public partial class __default {
    public static Std.Wrappers._IOption<__Y> Get<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      if ((m).Contains(x)) {
        return Std.Wrappers.Option<__Y>.create_Some(Dafny.Map<__X, __Y>.Select(m,x));
      } else {
        return Std.Wrappers.Option<__Y>.create_None();
      }
    }
    public static Dafny.IMap<__X,__Y> ToImap<__X, __Y>(Dafny.IMap<__X,__Y> m) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<__X,__Y>, Dafny.IMap<__X,__Y>>>((_97_m) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll1 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_1 in (_97_m).Keys.Elements) {
          __X _98_x = (__X)_compr_1;
          if ((_97_m).Contains(_98_x)) {
            _coll1.Add(new Dafny.Pair<__X,__Y>(_98_x, Dafny.Map<__X, __Y>.Select(_97_m,_98_x)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll1);
      }))())(m);
    }
    public static Dafny.IMap<__X,__Y> RemoveKeys<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.ISet<__X> xs)
    {
      return Dafny.Map<__X, __Y>.Subtract(m, xs);
    }
    public static Dafny.IMap<__X,__Y> Remove<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      Dafny.IMap<__X,__Y> _99_m_k = Dafny.Helpers.Id<Func<Dafny.IMap<__X,__Y>, __X, Dafny.IMap<__X,__Y>>>((_100_m, _101_x) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll2 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_2 in (_100_m).Keys.Elements) {
          __X _102_x_k = (__X)_compr_2;
          if (((_100_m).Contains(_102_x_k)) && (!object.Equals(_102_x_k, _101_x))) {
            _coll2.Add(new Dafny.Pair<__X,__Y>(_102_x_k, Dafny.Map<__X, __Y>.Select(_100_m,_102_x_k)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll2);
      }))())(m, x);
      return _99_m_k;
    }
    public static Dafny.IMap<__X,__Y> Restrict<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.ISet<__X> xs)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Dafny.IMap<__X,__Y>, Dafny.IMap<__X,__Y>>>((_103_xs, _104_m) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll3 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_3 in (_103_xs).Elements) {
          __X _105_x = (__X)_compr_3;
          if (((_103_xs).Contains(_105_x)) && ((_104_m).Contains(_105_x))) {
            _coll3.Add(new Dafny.Pair<__X,__Y>(_105_x, Dafny.Map<__X, __Y>.Select(_104_m,_105_x)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll3);
      }))())(xs, m);
    }
    public static Dafny.IMap<__X,__Y> Union<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.IMap<__X,__Y> m_k)
    {
      return Dafny.Map<__X, __Y>.Merge(m, m_k);
    }
  }
} // end of namespace Std.Collections.Map
namespace Std.Collections.Set {

  public partial class __default {
    public static __T ExtractFromSingleton<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_0 =>  {
        __T _106_x = default(__T);
        foreach (__T _assign_such_that_1 in (s).Elements) {
          _106_x = (__T)_assign_such_that_1;
          if ((s).Contains(_106_x)) {
            goto after__ASSIGN_SUCH_THAT_1;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 7299)");
      after__ASSIGN_SUCH_THAT_1: ;
        return _106_x;
      }
      );
    }
    public static Dafny.ISet<__Y> Map<__X, __Y>(Func<__X, __Y> f, Dafny.ISet<__X> xs)
    {
      Dafny.ISet<__Y> _107_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, __Y>, Dafny.ISet<__Y>>>((_108_xs, _109_f) => ((System.Func<Dafny.ISet<__Y>>)(() => {
        var _coll4 = new System.Collections.Generic.List<__Y>();
        foreach (__X _compr_4 in (_108_xs).Elements) {
          __X _110_x = (__X)_compr_4;
          if ((_108_xs).Contains(_110_x)) {
            _coll4.Add(Dafny.Helpers.Id<Func<__X, __Y>>(_109_f)(_110_x));
          }
        }
        return Dafny.Set<__Y>.FromCollection(_coll4);
      }))())(xs, f);
      return _107_ys;
    }
    public static Dafny.ISet<__X> Filter<__X>(Func<__X, bool> f, Dafny.ISet<__X> xs)
    {
      Dafny.ISet<__X> _111_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, bool>, Dafny.ISet<__X>>>((_112_xs, _113_f) => ((System.Func<Dafny.ISet<__X>>)(() => {
        var _coll5 = new System.Collections.Generic.List<__X>();
        foreach (__X _compr_5 in (_112_xs).Elements) {
          __X _114_x = (__X)_compr_5;
          if (((_112_xs).Contains(_114_x)) && (Dafny.Helpers.Id<Func<__X, bool>>(_113_f)(_114_x))) {
            _coll5.Add(_114_x);
          }
        }
        return Dafny.Set<__X>.FromCollection(_coll5);
      }))())(xs, f);
      return _111_ys;
    }
    public static Dafny.ISet<BigInteger> SetRange(BigInteger a, BigInteger b)
    {
      Dafny.ISet<BigInteger> _115___accumulator = Dafny.Set<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((a) == (b)) {
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.FromElements(), _115___accumulator);
      } else {
        _115___accumulator = Dafny.Set<BigInteger>.Union(_115___accumulator, Dafny.Set<BigInteger>.FromElements(a));
        BigInteger _in26 = (a) + (BigInteger.One);
        BigInteger _in27 = b;
        a = _in26;
        b = _in27;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISet<BigInteger> SetRangeZeroBound(BigInteger n) {
      return Std.Collections.Set.__default.SetRange(BigInteger.Zero, n);
    }
  }
} // end of namespace Std.Collections.Set
namespace Std.Collections {

} // end of namespace Std.Collections
namespace Std.DynamicArray {


  public partial class DynamicArray<A> {
    public DynamicArray() {
      this.size = BigInteger.Zero;
      this.capacity = BigInteger.Zero;
      this.data = new A[0];
    }
    public BigInteger size {get; set;}
    public BigInteger capacity {get; set;}
    public A[] data {get; set;}
    public void __ctor()
    {
      (this).size = BigInteger.Zero;
      (this).capacity = BigInteger.Zero;
      A[] _nw3 = new A[Dafny.Helpers.ToIntChecked(BigInteger.Zero, "array size exceeds memory limit")];
      (this).data = _nw3;
    }
    public A At(BigInteger index) {
      return (this.data)[(int)(index)];
    }
    public void Put(BigInteger index, A element)
    {
      A[] _arr0 = this.data;
      _arr0[(int)((index))] = element;
    }
    public void Ensure(BigInteger reserved, A defaultValue)
    {
      BigInteger _116_newCapacity;
      _116_newCapacity = this.capacity;
      while ((reserved) > ((_116_newCapacity) - (this.size))) {
        _116_newCapacity = (this).DefaultNewCapacity(_116_newCapacity);
      }
      if ((_116_newCapacity) > (this.capacity)) {
        (this).Realloc(defaultValue, _116_newCapacity);
      }
    }
    public void PopFast()
    {
      (this).size = (this.size) - (BigInteger.One);
    }
    public void PushFast(A element)
    {
      A[] _arr1 = this.data;
      BigInteger _index5 = this.size;
      _arr1[(int)(_index5)] = element;
      (this).size = (this.size) + (BigInteger.One);
    }
    public void Push(A element)
    {
      if ((this.size) == (this.capacity)) {
        (this).ReallocDefault(element);
      }
      (this).PushFast(element);
    }
    public void Realloc(A defaultValue, BigInteger newCapacity)
    {
      A[] _117_oldData;
      BigInteger _118_oldCapacity;
      A[] _rhs2 = this.data;
      BigInteger _rhs3 = this.capacity;
      _117_oldData = _rhs2;
      _118_oldCapacity = _rhs3;
      Func<BigInteger, A> _init3 = Dafny.Helpers.Id<Func<A, Func<BigInteger, A>>>((_119_defaultValue) => ((System.Func<BigInteger, A>)((_120___v0) => {
        return _119_defaultValue;
      })))(defaultValue);
      A[] _nw4 = new A[Dafny.Helpers.ToIntChecked(newCapacity, "array size exceeds memory limit")];
      for (var _i0_3 = 0; _i0_3 < new BigInteger(_nw4.Length); _i0_3++) {
        _nw4[(int)(_i0_3)] = _init3(_i0_3);
      }
      A[] _rhs4 = _nw4;
      BigInteger _rhs5 = newCapacity;
      Std.DynamicArray.DynamicArray<A> _lhs0 = this;
      Std.DynamicArray.DynamicArray<A> _lhs1 = this;
      _lhs0.data = _rhs4;
      _lhs1.capacity = _rhs5;
      (this).CopyFrom(_117_oldData, _118_oldCapacity);
    }
    public BigInteger DefaultNewCapacity(BigInteger capacity) {
      if ((capacity).Sign == 0) {
        return new BigInteger(8);
      } else {
        return (new BigInteger(2)) * (capacity);
      }
    }
    public void ReallocDefault(A defaultValue)
    {
      (this).Realloc(defaultValue, (this).DefaultNewCapacity(this.capacity));
    }
    public void CopyFrom(A[] newData, BigInteger count)
    {
      foreach (BigInteger _guard_loop_0 in Dafny.Helpers.IntegerRange(BigInteger.Zero, count)) {
        BigInteger _121_index = (BigInteger)_guard_loop_0;
        if ((true) && (((_121_index).Sign != -1) && ((_121_index) < (count)))) {
          A[] _arr2 = this.data;
          _arr2[(int)((_121_index))] = (newData)[(int)(_121_index)];
        }
      }
    }
  }
} // end of namespace Std.DynamicArray
namespace Std.FileIO {

  public partial class __default {
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>> ReadBytesFromFile(Dafny.ISequence<Dafny.Rune> path)
    {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>> res = Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.Default(Dafny.Sequence<byte>.Empty);
      bool _122_isError;
      Dafny.ISequence<byte> _123_bytesRead;
      Dafny.ISequence<Dafny.Rune> _124_errorMsg;
      bool _out1;
      Dafny.ISequence<byte> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      Std.CSharpFileIOInternalExterns.__default.INTERNAL__ReadBytesFromFile(path, out _out1, out _out2, out _out3);
      _122_isError = _out1;
      _123_bytesRead = _out2;
      _124_errorMsg = _out3;
      res = ((_122_isError) ? (Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Failure(_124_errorMsg)) : (Std.Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<Dafny.Rune>>.create_Success(_123_bytesRead)));
      return res;
      return res;
    }
    public static Std.Wrappers._IResult<_System._ITuple0, Dafny.ISequence<Dafny.Rune>> WriteBytesToFile(Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<byte> bytes)
    {
      Std.Wrappers._IResult<_System._ITuple0, Dafny.ISequence<Dafny.Rune>> res = Std.Wrappers.Result<_System._ITuple0, Dafny.ISequence<Dafny.Rune>>.Default(_System.Tuple0.Default());
      bool _125_isError;
      Dafny.ISequence<Dafny.Rune> _126_errorMsg;
      bool _out4;
      Dafny.ISequence<Dafny.Rune> _out5;
      Std.CSharpFileIOInternalExterns.__default.INTERNAL__WriteBytesToFile(path, bytes, out _out4, out _out5);
      _125_isError = _out4;
      _126_errorMsg = _out5;
      res = ((_125_isError) ? (Std.Wrappers.Result<_System._ITuple0, Dafny.ISequence<Dafny.Rune>>.create_Failure(_126_errorMsg)) : (Std.Wrappers.Result<_System._ITuple0, Dafny.ISequence<Dafny.Rune>>.create_Success(_System.Tuple0.create())));
      return res;
      return res;
    }
  }
} // end of namespace Std.FileIO
namespace Std.Arithmetic.GeneralInternals {

} // end of namespace Std.Arithmetic.GeneralInternals
namespace Std.Arithmetic.MulInternalsNonlinear {

} // end of namespace Std.Arithmetic.MulInternalsNonlinear
namespace Std.Arithmetic.MulInternals {

  public partial class __default {
    public static BigInteger MulPos(BigInteger x, BigInteger y)
    {
      BigInteger _127___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == 0) {
        return (BigInteger.Zero) + (_127___accumulator);
      } else {
        _127___accumulator = (_127___accumulator) + (y);
        BigInteger _in28 = (x) - (BigInteger.One);
        BigInteger _in29 = y;
        x = _in28;
        y = _in29;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger MulRecursive(BigInteger x, BigInteger y)
    {
      if ((x).Sign != -1) {
        return Std.Arithmetic.MulInternals.__default.MulPos(x, y);
      } else {
        return (new BigInteger(-1)) * (Std.Arithmetic.MulInternals.__default.MulPos((new BigInteger(-1)) * (x), y));
      }
    }
  }
} // end of namespace Std.Arithmetic.MulInternals
namespace Std.Arithmetic.Mul {

} // end of namespace Std.Arithmetic.Mul
namespace Std.Arithmetic.ModInternalsNonlinear {

} // end of namespace Std.Arithmetic.ModInternalsNonlinear
namespace Std.Arithmetic.DivInternalsNonlinear {

} // end of namespace Std.Arithmetic.DivInternalsNonlinear
namespace Std.Arithmetic.ModInternals {

  public partial class __default {
    public static BigInteger ModRecursive(BigInteger x, BigInteger d)
    {
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        BigInteger _in30 = (d) + (x);
        BigInteger _in31 = d;
        x = _in30;
        d = _in31;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return x;
      } else {
        BigInteger _in32 = (x) - (d);
        BigInteger _in33 = d;
        x = _in32;
        d = _in33;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.ModInternals
namespace Std.Arithmetic.DivInternals {

  public partial class __default {
    public static BigInteger DivPos(BigInteger x, BigInteger d)
    {
      BigInteger _128___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        _128___accumulator = (_128___accumulator) + (new BigInteger(-1));
        BigInteger _in34 = (x) + (d);
        BigInteger _in35 = d;
        x = _in34;
        d = _in35;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return (BigInteger.Zero) + (_128___accumulator);
      } else {
        _128___accumulator = (_128___accumulator) + (BigInteger.One);
        BigInteger _in36 = (x) - (d);
        BigInteger _in37 = d;
        x = _in36;
        d = _in37;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger DivRecursive(BigInteger x, BigInteger d)
    {
      if ((d).Sign == 1) {
        return Std.Arithmetic.DivInternals.__default.DivPos(x, d);
      } else {
        return (new BigInteger(-1)) * (Std.Arithmetic.DivInternals.__default.DivPos(x, (new BigInteger(-1)) * (d)));
      }
    }
  }
} // end of namespace Std.Arithmetic.DivInternals
namespace Std.Arithmetic.DivMod {

  public partial class __default {
    public static bool MultiplesVanish(BigInteger a, BigInteger b, BigInteger m)
    {
      return (Dafny.Helpers.EuclideanModulus(((m) * (a)) + (b), m)) == (Dafny.Helpers.EuclideanModulus(b, m));
    }
  }
} // end of namespace Std.Arithmetic.DivMod
namespace Std.Arithmetic.Power {

  public partial class __default {
    public static BigInteger Pow(BigInteger b, BigInteger e)
    {
      BigInteger _129___accumulator = BigInteger.One;
    TAIL_CALL_START: ;
      if ((e).Sign == 0) {
        return (BigInteger.One) * (_129___accumulator);
      } else {
        _129___accumulator = (_129___accumulator) * (b);
        BigInteger _in38 = b;
        BigInteger _in39 = (e) - (BigInteger.One);
        b = _in38;
        e = _in39;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Power
namespace Std.Arithmetic.Logarithm {

  public partial class __default {
    public static BigInteger Log(BigInteger @base, BigInteger pow)
    {
      BigInteger _130___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((pow) < (@base)) {
        return (BigInteger.Zero) + (_130___accumulator);
      } else {
        _130___accumulator = (_130___accumulator) + (BigInteger.One);
        BigInteger _in40 = @base;
        BigInteger _in41 = Dafny.Helpers.EuclideanDivision(pow, @base);
        @base = _in40;
        pow = _in41;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Logarithm
namespace Std.Arithmetic.Power2 {

  public partial class __default {
    public static BigInteger Pow2(BigInteger e) {
      return Std.Arithmetic.Power.__default.Pow(new BigInteger(2), e);
    }
  }
} // end of namespace Std.Arithmetic.Power2
namespace Std.Arithmetic {

} // end of namespace Std.Arithmetic
namespace Std.Strings.HexConversion {

  public partial class __default {
    public static BigInteger BASE() {
      return Std.Strings.HexConversion.__default.@base;
    }
    public static Dafny.ISequence<Dafny.Rune> OfDigits(Dafny.ISequence<BigInteger> digits) {
      Dafny.ISequence<Dafny.Rune> _131___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(), _131___accumulator);
      } else {
        _131___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.HexConversion.__default.chars).Select((digits).Select(BigInteger.Zero))), _131___accumulator);
        Dafny.ISequence<BigInteger> _in42 = (digits).Drop(BigInteger.One);
        digits = _in42;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> OfNat(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.HexConversion.__default.chars).Select(BigInteger.Zero));
      } else {
        return Std.Strings.HexConversion.__default.OfDigits(Std.Strings.HexConversion.__default.FromNat(n));
      }
    }
    public static bool OfNumberStr(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      return !(!(str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.Strings.HexConversion.__default.chars).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_132_str) => Dafny.Helpers.Quantifier<Dafny.Rune>(((_132_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_1) => {
        Dafny.Rune _133_c = (Dafny.Rune)_forall_var_1;
        return !(((_132_str).Drop(BigInteger.One)).Contains(_133_c)) || ((Std.Strings.HexConversion.__default.chars).Contains(_133_c));
      }))))(str)));
    }
    public static bool ToNumberStr(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      return !(!(str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.Strings.HexConversion.__default.charToDigit).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_134_str) => Dafny.Helpers.Quantifier<Dafny.Rune>(((_134_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_2) => {
        Dafny.Rune _135_c = (Dafny.Rune)_forall_var_2;
        return !(((_134_str).Drop(BigInteger.One)).Contains(_135_c)) || ((Std.Strings.HexConversion.__default.charToDigit).Contains(_135_c));
      }))))(str)));
    }
    public static Dafny.ISequence<Dafny.Rune> OfInt(BigInteger n, Dafny.Rune minus)
    {
      if ((n).Sign != -1) {
        return Std.Strings.HexConversion.__default.OfNat(n);
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(minus), Std.Strings.HexConversion.__default.OfNat((BigInteger.Zero) - (n)));
      }
    }
    public static BigInteger ToNat(Dafny.ISequence<Dafny.Rune> str) {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((Std.Strings.HexConversion.__default.ToNat((str).Take((new BigInteger((str).Count)) - (BigInteger.One)))) * (Std.Strings.HexConversion.__default.@base)) + (Dafny.Map<Dafny.Rune, BigInteger>.Select(Std.Strings.HexConversion.__default.charToDigit,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      if (Dafny.Sequence<Dafny.Rune>.IsPrefixOf(Dafny.Sequence<Dafny.Rune>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (Std.Strings.HexConversion.__default.ToNat((str).Drop(BigInteger.One)));
      } else {
        return Std.Strings.HexConversion.__default.ToNat(str);
      }
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Std.Strings.HexConversion.__default.ToNatRight(Std.Collections.Seq.__default.DropFirst<BigInteger>(xs))) * (Std.Strings.HexConversion.__default.BASE())) + (Std.Collections.Seq.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _136___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_136___accumulator);
      } else {
        _136___accumulator = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) * (Std.Arithmetic.Power.__default.Pow(Std.Strings.HexConversion.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_136___accumulator);
        Dafny.ISequence<BigInteger> _in43 = Std.Collections.Seq.__default.DropLast<BigInteger>(xs);
        xs = _in43;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _137___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_137___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _137___accumulator = Dafny.Sequence<BigInteger>.Concat(_137___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Std.Strings.HexConversion.__default.BASE())));
        BigInteger _in44 = Dafny.Helpers.EuclideanDivision(n, Std.Strings.HexConversion.__default.BASE());
        n = _in44;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in45 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in46 = n;
        xs = _in45;
        n = _in46;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _138_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Std.Strings.HexConversion.__default.SeqExtend(xs, _138_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Std.Strings.HexConversion.__default.SeqExtend(Std.Strings.HexConversion.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _139_xs = Std.Strings.HexConversion.__default.FromNatWithLen(BigInteger.Zero, len);
      return _139_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs1 = Std.Strings.HexConversion.__default.SeqAdd(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _140_zs_k = _let_tmp_rhs1.dtor__0;
        BigInteger _141_cin = _let_tmp_rhs1.dtor__1;
        BigInteger _142_sum = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) + (Std.Collections.Seq.__default.Last<BigInteger>(ys))) + (_141_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs2 = (((_142_sum) < (Std.Strings.HexConversion.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_142_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_142_sum) - (Std.Strings.HexConversion.__default.BASE()), BigInteger.One)));
        BigInteger _143_sum__out = _let_tmp_rhs2.dtor__0;
        BigInteger _144_cout = _let_tmp_rhs2.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_140_zs_k, Dafny.Sequence<BigInteger>.FromElements(_143_sum__out)), _144_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs3 = Std.Strings.HexConversion.__default.SeqSub(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _145_zs = _let_tmp_rhs3.dtor__0;
        BigInteger _146_cin = _let_tmp_rhs3.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs4 = (((Std.Collections.Seq.__default.Last<BigInteger>(xs)) >= ((Std.Collections.Seq.__default.Last<BigInteger>(ys)) + (_146_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Std.Collections.Seq.__default.Last<BigInteger>(xs)) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_146_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Std.Strings.HexConversion.__default.BASE()) + (Std.Collections.Seq.__default.Last<BigInteger>(xs))) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_146_cin), BigInteger.One)));
        BigInteger _147_diff__out = _let_tmp_rhs4.dtor__0;
        BigInteger _148_cout = _let_tmp_rhs4.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_145_zs, Dafny.Sequence<BigInteger>.FromElements(_147_diff__out)), _148_cout);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> HEX__DIGITS { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789ABCDEF");
    } }
    public static Dafny.ISequence<Dafny.Rune> chars { get {
      return Std.Strings.HexConversion.__default.HEX__DIGITS;
    } }
    public static BigInteger @base { get {
      return new BigInteger((Std.Strings.HexConversion.__default.chars).Count);
    } }
    public static Dafny.IMap<Dafny.Rune,BigInteger> charToDigit { get {
      return Dafny.Map<Dafny.Rune, BigInteger>.FromElements(new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('0'), BigInteger.Zero), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('1'), BigInteger.One), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('2'), new BigInteger(2)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('3'), new BigInteger(3)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('4'), new BigInteger(4)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('5'), new BigInteger(5)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('6'), new BigInteger(6)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('7'), new BigInteger(7)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('8'), new BigInteger(8)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('9'), new BigInteger(9)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('a'), new BigInteger(10)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('b'), new BigInteger(11)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('c'), new BigInteger(12)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('d'), new BigInteger(13)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('e'), new BigInteger(14)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('f'), new BigInteger(15)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('A'), new BigInteger(10)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('B'), new BigInteger(11)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('C'), new BigInteger(12)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('D'), new BigInteger(13)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('E'), new BigInteger(14)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('F'), new BigInteger(15)));
    } }
  }

  public partial class CharSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class digit {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.Strings.HexConversion
namespace Std.Strings.DecimalConversion {

  public partial class __default {
    public static BigInteger BASE() {
      return Std.Strings.DecimalConversion.__default.@base;
    }
    public static Dafny.ISequence<Dafny.Rune> OfDigits(Dafny.ISequence<BigInteger> digits) {
      Dafny.ISequence<Dafny.Rune> _149___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(), _149___accumulator);
      } else {
        _149___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.DecimalConversion.__default.chars).Select((digits).Select(BigInteger.Zero))), _149___accumulator);
        Dafny.ISequence<BigInteger> _in47 = (digits).Drop(BigInteger.One);
        digits = _in47;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> OfNat(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.FromElements((Std.Strings.DecimalConversion.__default.chars).Select(BigInteger.Zero));
      } else {
        return Std.Strings.DecimalConversion.__default.OfDigits(Std.Strings.DecimalConversion.__default.FromNat(n));
      }
    }
    public static bool OfNumberStr(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      return !(!(str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.Strings.DecimalConversion.__default.chars).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_150_str) => Dafny.Helpers.Quantifier<Dafny.Rune>(((_150_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_3) => {
        Dafny.Rune _151_c = (Dafny.Rune)_forall_var_3;
        return !(((_150_str).Drop(BigInteger.One)).Contains(_151_c)) || ((Std.Strings.DecimalConversion.__default.chars).Contains(_151_c));
      }))))(str)));
    }
    public static bool ToNumberStr(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      return !(!(str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.Strings.DecimalConversion.__default.charToDigit).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, bool>>((_152_str) => Dafny.Helpers.Quantifier<Dafny.Rune>(((_152_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_4) => {
        Dafny.Rune _153_c = (Dafny.Rune)_forall_var_4;
        return !(((_152_str).Drop(BigInteger.One)).Contains(_153_c)) || ((Std.Strings.DecimalConversion.__default.charToDigit).Contains(_153_c));
      }))))(str)));
    }
    public static Dafny.ISequence<Dafny.Rune> OfInt(BigInteger n, Dafny.Rune minus)
    {
      if ((n).Sign != -1) {
        return Std.Strings.DecimalConversion.__default.OfNat(n);
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements(minus), Std.Strings.DecimalConversion.__default.OfNat((BigInteger.Zero) - (n)));
      }
    }
    public static BigInteger ToNat(Dafny.ISequence<Dafny.Rune> str) {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((Std.Strings.DecimalConversion.__default.ToNat((str).Take((new BigInteger((str).Count)) - (BigInteger.One)))) * (Std.Strings.DecimalConversion.__default.@base)) + (Dafny.Map<Dafny.Rune, BigInteger>.Select(Std.Strings.DecimalConversion.__default.charToDigit,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune minus)
    {
      if (Dafny.Sequence<Dafny.Rune>.IsPrefixOf(Dafny.Sequence<Dafny.Rune>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (Std.Strings.DecimalConversion.__default.ToNat((str).Drop(BigInteger.One)));
      } else {
        return Std.Strings.DecimalConversion.__default.ToNat(str);
      }
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Std.Strings.DecimalConversion.__default.ToNatRight(Std.Collections.Seq.__default.DropFirst<BigInteger>(xs))) * (Std.Strings.DecimalConversion.__default.BASE())) + (Std.Collections.Seq.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _154___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_154___accumulator);
      } else {
        _154___accumulator = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) * (Std.Arithmetic.Power.__default.Pow(Std.Strings.DecimalConversion.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_154___accumulator);
        Dafny.ISequence<BigInteger> _in48 = Std.Collections.Seq.__default.DropLast<BigInteger>(xs);
        xs = _in48;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _155___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_155___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _155___accumulator = Dafny.Sequence<BigInteger>.Concat(_155___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Std.Strings.DecimalConversion.__default.BASE())));
        BigInteger _in49 = Dafny.Helpers.EuclideanDivision(n, Std.Strings.DecimalConversion.__default.BASE());
        n = _in49;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in50 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in51 = n;
        xs = _in50;
        n = _in51;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _156_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Std.Strings.DecimalConversion.__default.SeqExtend(xs, _156_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Std.Strings.DecimalConversion.__default.SeqExtend(Std.Strings.DecimalConversion.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _157_xs = Std.Strings.DecimalConversion.__default.FromNatWithLen(BigInteger.Zero, len);
      return _157_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs5 = Std.Strings.DecimalConversion.__default.SeqAdd(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _158_zs_k = _let_tmp_rhs5.dtor__0;
        BigInteger _159_cin = _let_tmp_rhs5.dtor__1;
        BigInteger _160_sum = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) + (Std.Collections.Seq.__default.Last<BigInteger>(ys))) + (_159_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs6 = (((_160_sum) < (Std.Strings.DecimalConversion.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_160_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_160_sum) - (Std.Strings.DecimalConversion.__default.BASE()), BigInteger.One)));
        BigInteger _161_sum__out = _let_tmp_rhs6.dtor__0;
        BigInteger _162_cout = _let_tmp_rhs6.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_158_zs_k, Dafny.Sequence<BigInteger>.FromElements(_161_sum__out)), _162_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs7 = Std.Strings.DecimalConversion.__default.SeqSub(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _163_zs = _let_tmp_rhs7.dtor__0;
        BigInteger _164_cin = _let_tmp_rhs7.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs8 = (((Std.Collections.Seq.__default.Last<BigInteger>(xs)) >= ((Std.Collections.Seq.__default.Last<BigInteger>(ys)) + (_164_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Std.Collections.Seq.__default.Last<BigInteger>(xs)) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_164_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Std.Strings.DecimalConversion.__default.BASE()) + (Std.Collections.Seq.__default.Last<BigInteger>(xs))) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_164_cin), BigInteger.One)));
        BigInteger _165_diff__out = _let_tmp_rhs8.dtor__0;
        BigInteger _166_cout = _let_tmp_rhs8.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_163_zs, Dafny.Sequence<BigInteger>.FromElements(_165_diff__out)), _166_cout);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> DIGITS { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789");
    } }
    public static Dafny.ISequence<Dafny.Rune> chars { get {
      return Std.Strings.DecimalConversion.__default.DIGITS;
    } }
    public static BigInteger @base { get {
      return new BigInteger((Std.Strings.DecimalConversion.__default.chars).Count);
    } }
    public static Dafny.IMap<Dafny.Rune,BigInteger> charToDigit { get {
      return Dafny.Map<Dafny.Rune, BigInteger>.FromElements(new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('0'), BigInteger.Zero), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('1'), BigInteger.One), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('2'), new BigInteger(2)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('3'), new BigInteger(3)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('4'), new BigInteger(4)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('5'), new BigInteger(5)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('6'), new BigInteger(6)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('7'), new BigInteger(7)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('8'), new BigInteger(8)), new Dafny.Pair<Dafny.Rune, BigInteger>(new Dafny.Rune('9'), new BigInteger(9)));
    } }
  }

  public partial class CharSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class digit {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.Strings.DecimalConversion
namespace Std.Strings.CharStrEscaping {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> Escape(Dafny.ISequence<Dafny.Rune> str, Dafny.ISet<Dafny.Rune> mustEscape, Dafny.Rune escape)
    {
      Dafny.ISequence<Dafny.Rune> _167___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_167___accumulator, str);
      } else if ((mustEscape).Contains((str).Select(BigInteger.Zero))) {
        _167___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_167___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements(escape, (str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in52 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in53 = mustEscape;
        Dafny.Rune _in54 = escape;
        str = _in52;
        mustEscape = _in53;
        escape = _in54;
        goto TAIL_CALL_START;
      } else {
        _167___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_167___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in55 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in56 = mustEscape;
        Dafny.Rune _in57 = escape;
        str = _in55;
        mustEscape = _in56;
        escape = _in57;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> Unescape(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune escape)
    {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(str);
      } else if (((str).Select(BigInteger.Zero)) == (escape)) {
        if ((new BigInteger((str).Count)) > (BigInteger.One)) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _168_valueOrError0 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(new BigInteger(2)), escape);
          if ((_168_valueOrError0).IsFailure()) {
            return (_168_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
          } else {
            Dafny.ISequence<Dafny.Rune> _169_tl = (_168_valueOrError0).Extract();
            return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.One)), _169_tl));
          }
        } else {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
        }
      } else {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _170_valueOrError1 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(BigInteger.One), escape);
        if ((_170_valueOrError1).IsFailure()) {
          return (_170_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
        } else {
          Dafny.ISequence<Dafny.Rune> _171_tl = (_170_valueOrError1).Extract();
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)), _171_tl));
        }
      }
    }
  }
} // end of namespace Std.Strings.CharStrEscaping
namespace Std.Strings {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> OfNat(BigInteger n) {
      return Std.Strings.DecimalConversion.__default.OfNat(n);
    }
    public static Dafny.ISequence<Dafny.Rune> OfInt(BigInteger n) {
      return Std.Strings.DecimalConversion.__default.OfInt(n, new Dafny.Rune('-'));
    }
    public static BigInteger ToNat(Dafny.ISequence<Dafny.Rune> str) {
      return Std.Strings.DecimalConversion.__default.ToNat(str);
    }
    public static BigInteger ToInt(Dafny.ISequence<Dafny.Rune> str) {
      return Std.Strings.DecimalConversion.__default.ToInt(str, new Dafny.Rune('-'));
    }
    public static Dafny.ISequence<Dafny.Rune> EscapeQuotes(Dafny.ISequence<Dafny.Rune> str) {
      return Std.Strings.CharStrEscaping.__default.Escape(str, Dafny.Set<Dafny.Rune>.FromElements(new Dafny.Rune('\"'), new Dafny.Rune('\'')), new Dafny.Rune('\\'));
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> UnescapeQuotes(Dafny.ISequence<Dafny.Rune> str) {
      return Std.Strings.CharStrEscaping.__default.Unescape(str, new Dafny.Rune('\\'));
    }
    public static Dafny.ISequence<Dafny.Rune> OfBool(bool b) {
      if (b) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
      }
    }
    public static Dafny.ISequence<Dafny.Rune> OfChar(Dafny.Rune c) {
      return Dafny.Sequence<Dafny.Rune>.FromElements(c);
    }
    public static Dafny.ISequence<Dafny.Rune> Join(Dafny.ISequence<Dafny.Rune> sep, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> strs)
    {
      Dafny.ISequence<Dafny.Rune> _172___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((strs).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_172___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if ((new BigInteger((strs).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_172___accumulator, (strs).Select(BigInteger.Zero));
      } else {
        _172___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_172___accumulator, Dafny.Sequence<Dafny.Rune>.Concat((strs).Select(BigInteger.Zero), sep));
        Dafny.ISequence<Dafny.Rune> _in58 = sep;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in59 = (strs).Drop(BigInteger.One);
        sep = _in58;
        strs = _in59;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> Concat(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> strs) {
      Dafny.ISequence<Dafny.Rune> _173___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((strs).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_173___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else {
        _173___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_173___accumulator, (strs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in60 = (strs).Drop(BigInteger.One);
        strs = _in60;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Strings
namespace Std.Unicode.Base {

  public partial class __default {
    public static bool IsInAssignedPlane(uint i) {
      byte _174_plane = (byte)((i) >> ((int)((byte)(16))));
      return (Std.Unicode.Base.__default.ASSIGNED__PLANES).Contains(_174_plane);
    }
    public static uint HIGH__SURROGATE__MIN { get {
      return 55296U;
    } }
    public static uint HIGH__SURROGATE__MAX { get {
      return 56319U;
    } }
    public static uint LOW__SURROGATE__MIN { get {
      return 56320U;
    } }
    public static uint LOW__SURROGATE__MAX { get {
      return 57343U;
    } }
    public static Dafny.ISet<byte> ASSIGNED__PLANES { get {
      return Dafny.Set<byte>.FromElements((byte)(0), (byte)(1), (byte)(2), (byte)(3), (byte)(14), (byte)(15), (byte)(16));
    } }
  }

  public partial class CodePoint {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class HighSurrogateCodePoint {
    private static readonly uint Witness = Std.Unicode.Base.__default.HIGH__SURROGATE__MIN;
    public static uint Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(Std.Unicode.Base.HighSurrogateCodePoint.Default());
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class LowSurrogateCodePoint {
    private static readonly uint Witness = Std.Unicode.Base.__default.LOW__SURROGATE__MIN;
    public static uint Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(Std.Unicode.Base.LowSurrogateCodePoint.Default());
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ScalarValue {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class AssignedCodePoint {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.Unicode.Base
namespace Std.Unicode.Utf8EncodingForm {

  public partial class __default {
    public static bool IsMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        bool _175_b = Std.Unicode.Utf8EncodingForm.__default.IsWellFormedSingleCodeUnitSequence(s);
        return _175_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(2))) {
        bool _176_b = Std.Unicode.Utf8EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _176_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(3))) {
        bool _177_b = Std.Unicode.Utf8EncodingForm.__default.IsWellFormedTripleCodeUnitSequence(s);
        return _177_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(4))) {
        bool _178_b = Std.Unicode.Utf8EncodingForm.__default.IsWellFormedQuadrupleCodeUnitSequence(s);
        return _178_b;
      } else {
        return false;
      }
    }
    public static bool IsWellFormedSingleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _179_firstByte = (s).Select(BigInteger.Zero);
      return (true) && ((((byte)(0)) <= (_179_firstByte)) && ((_179_firstByte) <= ((byte)(127))));
    }
    public static bool IsWellFormedDoubleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _180_firstByte = (s).Select(BigInteger.Zero);
      byte _181_secondByte = (s).Select(BigInteger.One);
      return ((((byte)(194)) <= (_180_firstByte)) && ((_180_firstByte) <= ((byte)(223)))) && ((((byte)(128)) <= (_181_secondByte)) && ((_181_secondByte) <= ((byte)(191))));
    }
    public static bool IsWellFormedTripleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _182_firstByte = (s).Select(BigInteger.Zero);
      byte _183_secondByte = (s).Select(BigInteger.One);
      byte _184_thirdByte = (s).Select(new BigInteger(2));
      return ((((((_182_firstByte) == ((byte)(224))) && ((((byte)(160)) <= (_183_secondByte)) && ((_183_secondByte) <= ((byte)(191))))) || (((((byte)(225)) <= (_182_firstByte)) && ((_182_firstByte) <= ((byte)(236)))) && ((((byte)(128)) <= (_183_secondByte)) && ((_183_secondByte) <= ((byte)(191)))))) || (((_182_firstByte) == ((byte)(237))) && ((((byte)(128)) <= (_183_secondByte)) && ((_183_secondByte) <= ((byte)(159)))))) || (((((byte)(238)) <= (_182_firstByte)) && ((_182_firstByte) <= ((byte)(239)))) && ((((byte)(128)) <= (_183_secondByte)) && ((_183_secondByte) <= ((byte)(191)))))) && ((((byte)(128)) <= (_184_thirdByte)) && ((_184_thirdByte) <= ((byte)(191))));
    }
    public static bool IsWellFormedQuadrupleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _185_firstByte = (s).Select(BigInteger.Zero);
      byte _186_secondByte = (s).Select(BigInteger.One);
      byte _187_thirdByte = (s).Select(new BigInteger(2));
      byte _188_fourthByte = (s).Select(new BigInteger(3));
      return ((((((_185_firstByte) == ((byte)(240))) && ((((byte)(144)) <= (_186_secondByte)) && ((_186_secondByte) <= ((byte)(191))))) || (((((byte)(241)) <= (_185_firstByte)) && ((_185_firstByte) <= ((byte)(243)))) && ((((byte)(128)) <= (_186_secondByte)) && ((_186_secondByte) <= ((byte)(191)))))) || (((_185_firstByte) == ((byte)(244))) && ((((byte)(128)) <= (_186_secondByte)) && ((_186_secondByte) <= ((byte)(143)))))) && ((((byte)(128)) <= (_187_thirdByte)) && ((_187_thirdByte) <= ((byte)(191))))) && ((((byte)(128)) <= (_188_fourthByte)) && ((_188_fourthByte) <= ((byte)(191))));
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<byte>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> s) {
      if (((new BigInteger((s).Count)) >= (BigInteger.One)) && (Std.Unicode.Utf8EncodingForm.__default.IsWellFormedSingleCodeUnitSequence((s).Take(BigInteger.One)))) {
        return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_Some((s).Take(BigInteger.One));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (Std.Unicode.Utf8EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence((s).Take(new BigInteger(2))))) {
        return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(2)));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(3))) && (Std.Unicode.Utf8EncodingForm.__default.IsWellFormedTripleCodeUnitSequence((s).Take(new BigInteger(3))))) {
        return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(3)));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(4))) && (Std.Unicode.Utf8EncodingForm.__default.IsWellFormedQuadrupleCodeUnitSequence((s).Take(new BigInteger(4))))) {
        return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(4)));
      } else {
        return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_None();
      }
    }
    public static Dafny.ISequence<byte> EncodeScalarValue(uint v) {
      if ((v) <= (127U)) {
        return Std.Unicode.Utf8EncodingForm.__default.EncodeScalarValueSingleByte(v);
      } else if ((v) <= (2047U)) {
        return Std.Unicode.Utf8EncodingForm.__default.EncodeScalarValueDoubleByte(v);
      } else if ((v) <= (65535U)) {
        return Std.Unicode.Utf8EncodingForm.__default.EncodeScalarValueTripleByte(v);
      } else {
        return Std.Unicode.Utf8EncodingForm.__default.EncodeScalarValueQuadrupleByte(v);
      }
    }
    public static Dafny.ISequence<byte> EncodeScalarValueSingleByte(uint v) {
      byte _189_x = (byte)((v) & (127U));
      byte _190_firstByte = (byte)(_189_x);
      return Dafny.Sequence<byte>.FromElements(_190_firstByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueDoubleByte(uint v) {
      byte _191_x = (byte)((v) & (63U));
      byte _192_y = (byte)(((v) & (1984U)) >> ((int)((byte)(6))));
      byte _193_firstByte = (byte)(((byte)(192)) | ((byte)(_192_y)));
      byte _194_secondByte = (byte)(((byte)(128)) | ((byte)(_191_x)));
      return Dafny.Sequence<byte>.FromElements(_193_firstByte, _194_secondByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueTripleByte(uint v) {
      byte _195_x = (byte)((v) & (63U));
      byte _196_y = (byte)(((v) & (4032U)) >> ((int)((byte)(6))));
      byte _197_z = (byte)(((v) & (61440U)) >> ((int)((byte)(12))));
      byte _198_firstByte = (byte)(((byte)(224)) | ((byte)(_197_z)));
      byte _199_secondByte = (byte)(((byte)(128)) | ((byte)(_196_y)));
      byte _200_thirdByte = (byte)(((byte)(128)) | ((byte)(_195_x)));
      return Dafny.Sequence<byte>.FromElements(_198_firstByte, _199_secondByte, _200_thirdByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueQuadrupleByte(uint v) {
      byte _201_x = (byte)((v) & (63U));
      byte _202_y = (byte)(((v) & (4032U)) >> ((int)((byte)(6))));
      byte _203_z = (byte)(((v) & (61440U)) >> ((int)((byte)(12))));
      byte _204_u2 = (byte)(((v) & (196608U)) >> ((int)((byte)(16))));
      byte _205_u1 = (byte)(((v) & (1835008U)) >> ((int)((byte)(18))));
      byte _206_firstByte = (byte)(((byte)(240)) | ((byte)(_205_u1)));
      byte _207_secondByte = (byte)(((byte)(((byte)(128)) | (unchecked((byte)(((byte)(((byte)(_204_u2)) << ((int)((byte)(4)))))))))) | ((byte)(_203_z)));
      byte _208_thirdByte = (byte)(((byte)(128)) | ((byte)(_202_y)));
      byte _209_fourthByte = (byte)(((byte)(128)) | ((byte)(_201_x)));
      return Dafny.Sequence<byte>.FromElements(_206_firstByte, _207_secondByte, _208_thirdByte, _209_fourthByte);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> m) {
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m);
      } else if ((new BigInteger((m).Count)) == (new BigInteger(2))) {
        return Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m);
      } else if ((new BigInteger((m).Count)) == (new BigInteger(3))) {
        return Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m);
      } else {
        return Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m);
      }
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(Dafny.ISequence<byte> m) {
      byte _210_firstByte = (m).Select(BigInteger.Zero);
      byte _211_x = (byte)(_210_firstByte);
      return (uint)(_211_x);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(Dafny.ISequence<byte> m) {
      byte _212_firstByte = (m).Select(BigInteger.Zero);
      byte _213_secondByte = (m).Select(BigInteger.One);
      uint _214_y = (uint)((byte)((_212_firstByte) & ((byte)(31))));
      uint _215_x = (uint)((byte)((_213_secondByte) & ((byte)(63))));
      return (unchecked((uint)(((_214_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU))) | ((uint)(_215_x));
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(Dafny.ISequence<byte> m) {
      byte _216_firstByte = (m).Select(BigInteger.Zero);
      byte _217_secondByte = (m).Select(BigInteger.One);
      byte _218_thirdByte = (m).Select(new BigInteger(2));
      uint _219_z = (uint)((byte)((_216_firstByte) & ((byte)(15))));
      uint _220_y = (uint)((byte)((_217_secondByte) & ((byte)(63))));
      uint _221_x = (uint)((byte)((_218_thirdByte) & ((byte)(63))));
      return ((unchecked((uint)(((_219_z) << ((int)((byte)(12)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_220_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU)))) | ((uint)(_221_x));
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(Dafny.ISequence<byte> m) {
      byte _222_firstByte = (m).Select(BigInteger.Zero);
      byte _223_secondByte = (m).Select(BigInteger.One);
      byte _224_thirdByte = (m).Select(new BigInteger(2));
      byte _225_fourthByte = (m).Select(new BigInteger(3));
      uint _226_u1 = (uint)((byte)((_222_firstByte) & ((byte)(7))));
      uint _227_u2 = (uint)((byte)(((byte)((_223_secondByte) & ((byte)(48)))) >> ((int)((byte)(4)))));
      uint _228_z = (uint)((byte)((_223_secondByte) & ((byte)(15))));
      uint _229_y = (uint)((byte)((_224_thirdByte) & ((byte)(63))));
      uint _230_x = (uint)((byte)((_225_fourthByte) & ((byte)(63))));
      return ((((unchecked((uint)(((_226_u1) << ((int)((byte)(18)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_227_u2) << ((int)((byte)(16)))) & (uint)0xFFFFFFU)))) | (unchecked((uint)(((_228_z) << ((int)((byte)(12)))) & (uint)0xFFFFFFU)))) | (unchecked((uint)(((_229_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU)))) | ((uint)(_230_x));
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> PartitionCodeUnitSequenceChecked(Dafny.ISequence<byte> s)
    {
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.Default();
      if ((s).Equals(Dafny.Sequence<byte>.FromElements())) {
        maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_Some(Dafny.Sequence<Dafny.ISequence<byte>>.FromElements());
        return maybeParts;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _231_result;
      _231_result = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements();
      Dafny.ISequence<byte> _232_rest;
      _232_rest = s;
      while ((new BigInteger((_232_rest).Count)).Sign == 1) {
        Dafny.ISequence<byte> _233_prefix;
        Std.Wrappers._IOption<Dafny.ISequence<byte>> _234_valueOrError0 = Std.Wrappers.Option<Dafny.ISequence<byte>>.Default();
        _234_valueOrError0 = Std.Unicode.Utf8EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_232_rest);
        if ((_234_valueOrError0).IsFailure()) {
          maybeParts = (_234_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<byte>>>();
          return maybeParts;
        }
        _233_prefix = (_234_valueOrError0).Extract();
        _231_result = Dafny.Sequence<Dafny.ISequence<byte>>.Concat(_231_result, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(_233_prefix));
        _232_rest = (_232_rest).Drop(new BigInteger((_233_prefix).Count));
      }
      maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_Some(_231_result);
      return maybeParts;
      return maybeParts;
    }
    public static Dafny.ISequence<Dafny.ISequence<byte>> PartitionCodeUnitSequence(Dafny.ISequence<byte> s) {
      return (Std.Unicode.Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    }
    public static bool IsWellFormedCodeUnitSequence(Dafny.ISequence<byte> s) {
      return (Std.Unicode.Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    }
    public static Dafny.ISequence<byte> EncodeScalarSequence(Dafny.ISequence<uint> vs)
    {
      Dafny.ISequence<byte> s = Std.Unicode.Utf8EncodingForm.WellFormedCodeUnitSeq.Default();
      s = Dafny.Sequence<byte>.FromElements();
      BigInteger _lo0 = BigInteger.Zero;
      for (BigInteger _235_i = new BigInteger((vs).Count); _lo0 < _235_i; ) {
        _235_i--;
        Dafny.ISequence<byte> _236_next;
        _236_next = Std.Unicode.Utf8EncodingForm.__default.EncodeScalarValue((vs).Select(_235_i));
        s = Dafny.Sequence<byte>.Concat(_236_next, s);
      }
      return s;
    }
    public static Dafny.ISequence<uint> DecodeCodeUnitSequence(Dafny.ISequence<byte> s) {
      Dafny.ISequence<Dafny.ISequence<byte>> _237_parts = Std.Unicode.Utf8EncodingForm.__default.PartitionCodeUnitSequence(s);
      Dafny.ISequence<uint> _238_vs = Std.Collections.Seq.__default.Map<Dafny.ISequence<byte>, uint>(Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _237_parts);
      return _238_vs;
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<uint>> DecodeCodeUnitSequenceChecked(Dafny.ISequence<byte> s)
    {
      Std.Wrappers._IOption<Dafny.ISequence<uint>> maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.Default();
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _239_maybeParts;
      _239_maybeParts = Std.Unicode.Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_239_maybeParts).is_None) {
        maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.create_None();
        return maybeVs;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _240_parts;
      _240_parts = (_239_maybeParts).dtor_value;
      Dafny.ISequence<uint> _241_vs;
      _241_vs = Std.Collections.Seq.__default.Map<Dafny.ISequence<byte>, uint>(Std.Unicode.Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _240_parts);
      maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.create_Some(_241_vs);
      return maybeVs;
      return maybeVs;
    }
  }

  public partial class WellFormedCodeUnitSeq {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Std.Unicode.Utf8EncodingForm.WellFormedCodeUnitSeq.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class MinimalWellFormedCodeUnitSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.Unicode.Utf8EncodingForm
namespace Std.Unicode.Utf16EncodingForm {

  public partial class __default {
    public static bool IsMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return Std.Unicode.Utf16EncodingForm.__default.IsWellFormedSingleCodeUnitSequence(s);
      } else if ((new BigInteger((s).Count)) == (new BigInteger(2))) {
        bool _242_b = Std.Unicode.Utf16EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _242_b;
      } else {
        return false;
      }
    }
    public static bool IsWellFormedSingleCodeUnitSequence(Dafny.ISequence<ushort> s) {
      ushort _243_firstWord = (s).Select(BigInteger.Zero);
      return ((((ushort)(0)) <= (_243_firstWord)) && ((_243_firstWord) <= ((ushort)(55295)))) || ((((ushort)(57344)) <= (_243_firstWord)) && ((_243_firstWord) <= ((ushort)(65535))));
    }
    public static bool IsWellFormedDoubleCodeUnitSequence(Dafny.ISequence<ushort> s) {
      ushort _244_firstWord = (s).Select(BigInteger.Zero);
      ushort _245_secondWord = (s).Select(BigInteger.One);
      return ((((ushort)(55296)) <= (_244_firstWord)) && ((_244_firstWord) <= ((ushort)(56319)))) && ((((ushort)(56320)) <= (_245_secondWord)) && ((_245_secondWord) <= ((ushort)(57343))));
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<ushort>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> s) {
      if (((new BigInteger((s).Count)) >= (BigInteger.One)) && (Std.Unicode.Utf16EncodingForm.__default.IsWellFormedSingleCodeUnitSequence((s).Take(BigInteger.One)))) {
        return Std.Wrappers.Option<Dafny.ISequence<ushort>>.create_Some((s).Take(BigInteger.One));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (Std.Unicode.Utf16EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence((s).Take(new BigInteger(2))))) {
        return Std.Wrappers.Option<Dafny.ISequence<ushort>>.create_Some((s).Take(new BigInteger(2)));
      } else {
        return Std.Wrappers.Option<Dafny.ISequence<ushort>>.create_None();
      }
    }
    public static Dafny.ISequence<ushort> EncodeScalarValue(uint v) {
      if ((((0U) <= (v)) && ((v) <= (55295U))) || (((57344U) <= (v)) && ((v) <= (65535U)))) {
        return Std.Unicode.Utf16EncodingForm.__default.EncodeScalarValueSingleWord(v);
      } else {
        return Std.Unicode.Utf16EncodingForm.__default.EncodeScalarValueDoubleWord(v);
      }
    }
    public static Dafny.ISequence<ushort> EncodeScalarValueSingleWord(uint v) {
      ushort _246_firstWord = (ushort)(v);
      return Dafny.Sequence<ushort>.FromElements(_246_firstWord);
    }
    public static Dafny.ISequence<ushort> EncodeScalarValueDoubleWord(uint v) {
      ushort _247_x2 = (ushort)((v) & (1023U));
      byte _248_x1 = (byte)(((v) & (64512U)) >> ((int)((byte)(10))));
      byte _249_u = (byte)(((v) & (2031616U)) >> ((int)((byte)(16))));
      byte _250_w = (byte)(unchecked((byte)(((byte)((_249_u) - ((byte)(1)))) & (byte)0x1F)));
      ushort _251_firstWord = (ushort)(((ushort)(((ushort)(55296)) | (unchecked((ushort)(((ushort)(((ushort)(_250_w)) << ((int)((byte)(6)))))))))) | ((ushort)(_248_x1)));
      ushort _252_secondWord = (ushort)(((ushort)(56320)) | ((ushort)(_247_x2)));
      return Dafny.Sequence<ushort>.FromElements(_251_firstWord, _252_secondWord);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> m) {
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Std.Unicode.Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
      } else {
        return Std.Unicode.Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
      }
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(Dafny.ISequence<ushort> m) {
      ushort _253_firstWord = (m).Select(BigInteger.Zero);
      ushort _254_x = (ushort)(_253_firstWord);
      return (uint)(_254_x);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(Dafny.ISequence<ushort> m) {
      ushort _255_firstWord = (m).Select(BigInteger.Zero);
      ushort _256_secondWord = (m).Select(BigInteger.One);
      uint _257_x2 = (uint)((ushort)((_256_secondWord) & ((ushort)(1023))));
      uint _258_x1 = (uint)((ushort)((_255_firstWord) & ((ushort)(63))));
      uint _259_w = (uint)((ushort)(((ushort)((_255_firstWord) & ((ushort)(960)))) >> ((int)((byte)(6)))));
      uint _260_u = (uint)(unchecked((uint)(((_259_w) + (1U)) & (uint)0xFFFFFFU)));
      uint _261_v = ((unchecked((uint)(((_260_u) << ((int)((byte)(16)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_258_x1) << ((int)((byte)(10)))) & (uint)0xFFFFFFU)))) | ((uint)(_257_x2));
      return _261_v;
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> PartitionCodeUnitSequenceChecked(Dafny.ISequence<ushort> s)
    {
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.Default();
      if ((s).Equals(Dafny.Sequence<ushort>.FromElements())) {
        maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.create_Some(Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements());
        return maybeParts;
      }
      Dafny.ISequence<Dafny.ISequence<ushort>> _262_result;
      _262_result = Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements();
      Dafny.ISequence<ushort> _263_rest;
      _263_rest = s;
      while ((new BigInteger((_263_rest).Count)).Sign == 1) {
        Dafny.ISequence<ushort> _264_prefix;
        Std.Wrappers._IOption<Dafny.ISequence<ushort>> _265_valueOrError0 = Std.Wrappers.Option<Dafny.ISequence<ushort>>.Default();
        _265_valueOrError0 = Std.Unicode.Utf16EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_263_rest);
        if ((_265_valueOrError0).IsFailure()) {
          maybeParts = (_265_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<ushort>>>();
          return maybeParts;
        }
        _264_prefix = (_265_valueOrError0).Extract();
        _262_result = Dafny.Sequence<Dafny.ISequence<ushort>>.Concat(_262_result, Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements(_264_prefix));
        _263_rest = (_263_rest).Drop(new BigInteger((_264_prefix).Count));
      }
      maybeParts = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.create_Some(_262_result);
      return maybeParts;
      return maybeParts;
    }
    public static Dafny.ISequence<Dafny.ISequence<ushort>> PartitionCodeUnitSequence(Dafny.ISequence<ushort> s) {
      return (Std.Unicode.Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    }
    public static bool IsWellFormedCodeUnitSequence(Dafny.ISequence<ushort> s) {
      return (Std.Unicode.Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    }
    public static Dafny.ISequence<ushort> EncodeScalarSequence(Dafny.ISequence<uint> vs)
    {
      Dafny.ISequence<ushort> s = Std.Unicode.Utf16EncodingForm.WellFormedCodeUnitSeq.Default();
      s = Dafny.Sequence<ushort>.FromElements();
      BigInteger _lo1 = BigInteger.Zero;
      for (BigInteger _266_i = new BigInteger((vs).Count); _lo1 < _266_i; ) {
        _266_i--;
        Dafny.ISequence<ushort> _267_next;
        _267_next = Std.Unicode.Utf16EncodingForm.__default.EncodeScalarValue((vs).Select(_266_i));
        s = Dafny.Sequence<ushort>.Concat(_267_next, s);
      }
      return s;
    }
    public static Dafny.ISequence<uint> DecodeCodeUnitSequence(Dafny.ISequence<ushort> s) {
      Dafny.ISequence<Dafny.ISequence<ushort>> _268_parts = Std.Unicode.Utf16EncodingForm.__default.PartitionCodeUnitSequence(s);
      Dafny.ISequence<uint> _269_vs = Std.Collections.Seq.__default.Map<Dafny.ISequence<ushort>, uint>(Std.Unicode.Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _268_parts);
      return _269_vs;
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<uint>> DecodeCodeUnitSequenceChecked(Dafny.ISequence<ushort> s)
    {
      Std.Wrappers._IOption<Dafny.ISequence<uint>> maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.Default();
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> _270_maybeParts;
      _270_maybeParts = Std.Unicode.Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_270_maybeParts).is_None) {
        maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.create_None();
        return maybeVs;
      }
      Dafny.ISequence<Dafny.ISequence<ushort>> _271_parts;
      _271_parts = (_270_maybeParts).dtor_value;
      Dafny.ISequence<uint> _272_vs;
      _272_vs = Std.Collections.Seq.__default.Map<Dafny.ISequence<ushort>, uint>(Std.Unicode.Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _271_parts);
      maybeVs = Std.Wrappers.Option<Dafny.ISequence<uint>>.create_Some(_272_vs);
      return maybeVs;
      return maybeVs;
    }
  }

  public partial class WellFormedCodeUnitSeq {
    private static readonly Dafny.ISequence<ushort> Witness = Dafny.Sequence<ushort>.FromElements();
    public static Dafny.ISequence<ushort> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<ushort>>(Std.Unicode.Utf16EncodingForm.WellFormedCodeUnitSeq.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class MinimalWellFormedCodeUnitSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<ushort>>(Dafny.Sequence<ushort>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.Unicode.Utf16EncodingForm
namespace Std.Unicode.UnicodeStringsWithUnicodeChar {

  public partial class __default {
    public static uint CharAsUnicodeScalarValue(Dafny.Rune c) {
      return (uint)((c).Value);
    }
    public static Dafny.Rune CharFromUnicodeScalarValue(uint sv) {
      return new Dafny.Rune((int)(new BigInteger(sv)));
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<byte>> ToUTF8Checked(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<uint> _273_asCodeUnits = Std.Collections.Seq.__default.Map<Dafny.Rune, uint>(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      Dafny.ISequence<byte> _274_asUtf8CodeUnits = Std.Unicode.Utf8EncodingForm.__default.EncodeScalarSequence(_273_asCodeUnits);
      Dafny.ISequence<byte> _275_asBytes = Std.Collections.Seq.__default.Map<byte, byte>(((System.Func<byte, byte>)((_276_cu) => {
        return (byte)(_276_cu);
      })), _274_asUtf8CodeUnits);
      return Std.Wrappers.Option<Dafny.ISequence<byte>>.create_Some(_275_asBytes);
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> FromUTF8Checked(Dafny.ISequence<byte> bs) {
      Dafny.ISequence<byte> _277_asCodeUnits = Std.Collections.Seq.__default.Map<byte, byte>(((System.Func<byte, byte>)((_278_c) => {
        return (byte)(_278_c);
      })), bs);
      Std.Wrappers._IOption<Dafny.ISequence<uint>> _279_valueOrError0 = Std.Unicode.Utf8EncodingForm.__default.DecodeCodeUnitSequenceChecked(_277_asCodeUnits);
      if ((_279_valueOrError0).IsFailure()) {
        return (_279_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
      } else {
        Dafny.ISequence<uint> _280_utf32 = (_279_valueOrError0).Extract();
        Dafny.ISequence<Dafny.Rune> _281_asChars = Std.Collections.Seq.__default.Map<uint, Dafny.Rune>(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _280_utf32);
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_281_asChars);
      }
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<ushort>> ToUTF16Checked(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<uint> _282_asCodeUnits = Std.Collections.Seq.__default.Map<Dafny.Rune, uint>(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      Dafny.ISequence<ushort> _283_asUtf16CodeUnits = Std.Unicode.Utf16EncodingForm.__default.EncodeScalarSequence(_282_asCodeUnits);
      Dafny.ISequence<ushort> _284_asBytes = Std.Collections.Seq.__default.Map<ushort, ushort>(((System.Func<ushort, ushort>)((_285_cu) => {
        return (ushort)(_285_cu);
      })), _283_asUtf16CodeUnits);
      return Std.Wrappers.Option<Dafny.ISequence<ushort>>.create_Some(_284_asBytes);
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> FromUTF16Checked(Dafny.ISequence<ushort> bs) {
      Dafny.ISequence<ushort> _286_asCodeUnits = Std.Collections.Seq.__default.Map<ushort, ushort>(((System.Func<ushort, ushort>)((_287_c) => {
        return (ushort)(_287_c);
      })), bs);
      Std.Wrappers._IOption<Dafny.ISequence<uint>> _288_valueOrError0 = Std.Unicode.Utf16EncodingForm.__default.DecodeCodeUnitSequenceChecked(_286_asCodeUnits);
      if ((_288_valueOrError0).IsFailure()) {
        return (_288_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
      } else {
        Dafny.ISequence<uint> _289_utf32 = (_288_valueOrError0).Extract();
        Dafny.ISequence<Dafny.Rune> _290_asChars = Std.Collections.Seq.__default.Map<uint, Dafny.Rune>(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _289_utf32);
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_290_asChars);
      }
    }
    public static Dafny.ISequence<byte> ASCIIToUTF8(Dafny.ISequence<Dafny.Rune> s) {
      return Std.Collections.Seq.__default.Map<Dafny.Rune, byte>(((System.Func<Dafny.Rune, byte>)((_291_c) => {
        return (byte)((_291_c).Value);
      })), s);
    }
    public static Dafny.ISequence<ushort> ASCIIToUTF16(Dafny.ISequence<Dafny.Rune> s) {
      return Std.Collections.Seq.__default.Map<Dafny.Rune, ushort>(((System.Func<Dafny.Rune, ushort>)((_292_c) => {
        return (ushort)((_292_c).Value);
      })), s);
    }
  }
} // end of namespace Std.Unicode.UnicodeStringsWithUnicodeChar
namespace Std.Unicode.Utf8EncodingScheme {

  public partial class __default {
    public static Dafny.ISequence<byte> Serialize(Dafny.ISequence<byte> s) {
      return Std.Collections.Seq.__default.Map<byte, byte>(((System.Func<byte, byte>)((_293_c) => {
        return (byte)(_293_c);
      })), s);
    }
    public static Dafny.ISequence<byte> Deserialize(Dafny.ISequence<byte> b) {
      return Std.Collections.Seq.__default.Map<byte, byte>(((System.Func<byte, byte>)((_294_b) => {
        return (byte)(_294_b);
      })), b);
    }
  }
} // end of namespace Std.Unicode.Utf8EncodingScheme
namespace Std.Unicode {

} // end of namespace Std.Unicode
namespace Std.CSharpFileIOInternalExterns {

} // end of namespace Std.CSharpFileIOInternalExterns
namespace Std.JSON.Values {

  public partial class __default {
    public static Std.JSON.Values._IDecimal Int(BigInteger n) {
      return Std.JSON.Values.Decimal.create(n, BigInteger.Zero);
    }
  }

  public interface _IDecimal {
    bool is_Decimal { get; }
    BigInteger dtor_n { get; }
    BigInteger dtor_e10 { get; }
    _IDecimal DowncastClone();
  }
  public class Decimal : _IDecimal {
    public readonly BigInteger _n;
    public readonly BigInteger _e10;
    public Decimal(BigInteger n, BigInteger e10) {
      this._n = n;
      this._e10 = e10;
    }
    public _IDecimal DowncastClone() {
      if (this is _IDecimal dt) { return dt; }
      return new Decimal(_n, _e10);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.Decimal;
      return oth != null && this._n == oth._n && this._e10 == oth._e10;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._n));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._e10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.Decimal.Decimal";
      s += "(";
      s += Dafny.Helpers.ToString(this._n);
      s += ", ";
      s += Dafny.Helpers.ToString(this._e10);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Values._IDecimal theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static Std.JSON.Values._IDecimal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Values._IDecimal> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Values._IDecimal>(Std.JSON.Values.Decimal.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Values._IDecimal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecimal create(BigInteger n, BigInteger e10) {
      return new Decimal(n, e10);
    }
    public static _IDecimal create_Decimal(BigInteger n, BigInteger e10) {
      return create(n, e10);
    }
    public bool is_Decimal { get { return true; } }
    public BigInteger dtor_n {
      get {
        return this._n;
      }
    }
    public BigInteger dtor_e10 {
      get {
        return this._e10;
      }
    }
  }

  public interface _IJSON {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    bool dtor_b { get; }
    Dafny.ISequence<Dafny.Rune> dtor_str { get; }
    Std.JSON.Values._IDecimal dtor_num { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> dtor_obj { get; }
    Dafny.ISequence<Std.JSON.Values._IJSON> dtor_arr { get; }
    _IJSON DowncastClone();
  }
  public abstract class JSON : _IJSON {
    public JSON() {
    }
    private static readonly Std.JSON.Values._IJSON theDefault = create_Null();
    public static Std.JSON.Values._IJSON Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Values._IJSON> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Values._IJSON>(Std.JSON.Values.JSON.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Values._IJSON> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IJSON create_Null() {
      return new JSON_Null();
    }
    public static _IJSON create_Bool(bool b) {
      return new JSON_Bool(b);
    }
    public static _IJSON create_String(Dafny.ISequence<Dafny.Rune> str) {
      return new JSON_String(str);
    }
    public static _IJSON create_Number(Std.JSON.Values._IDecimal num) {
      return new JSON_Number(num);
    }
    public static _IJSON create_Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> obj) {
      return new JSON_Object(obj);
    }
    public static _IJSON create_Array(Dafny.ISequence<Std.JSON.Values._IJSON> arr) {
      return new JSON_Array(arr);
    }
    public bool is_Null { get { return this is JSON_Null; } }
    public bool is_Bool { get { return this is JSON_Bool; } }
    public bool is_String { get { return this is JSON_String; } }
    public bool is_Number { get { return this is JSON_Number; } }
    public bool is_Object { get { return this is JSON_Object; } }
    public bool is_Array { get { return this is JSON_Array; } }
    public bool dtor_b {
      get {
        var d = this;
        return ((JSON_Bool)d)._b;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_str {
      get {
        var d = this;
        return ((JSON_String)d)._str;
      }
    }
    public Std.JSON.Values._IDecimal dtor_num {
      get {
        var d = this;
        return ((JSON_Number)d)._num;
      }
    }
    public Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> dtor_obj {
      get {
        var d = this;
        return ((JSON_Object)d)._obj;
      }
    }
    public Dafny.ISequence<Std.JSON.Values._IJSON> dtor_arr {
      get {
        var d = this;
        return ((JSON_Array)d)._arr;
      }
    }
    public abstract _IJSON DowncastClone();
  }
  public class JSON_Null : JSON {
    public JSON_Null() : base() {
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Null();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_Null;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.Null";
      return s;
    }
  }
  public class JSON_Bool : JSON {
    public readonly bool _b;
    public JSON_Bool(bool b) : base() {
      this._b = b;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Bool(_b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_Bool;
      return oth != null && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class JSON_String : JSON {
    public readonly Dafny.ISequence<Dafny.Rune> _str;
    public JSON_String(Dafny.ISequence<Dafny.Rune> str) : base() {
      this._str = str;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_String(_str);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_String;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.String";
      s += "(";
      s += this._str.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class JSON_Number : JSON {
    public readonly Std.JSON.Values._IDecimal _num;
    public JSON_Number(Std.JSON.Values._IDecimal num) : base() {
      this._num = num;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Number(_num);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_Number;
      return oth != null && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
  }
  public class JSON_Object : JSON {
    public readonly Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _obj;
    public JSON_Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> obj) : base() {
      this._obj = obj;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Object(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_Object;
      return oth != null && object.Equals(this._obj, oth._obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }
  public class JSON_Array : JSON {
    public readonly Dafny.ISequence<Std.JSON.Values._IJSON> _arr;
    public JSON_Array(Dafny.ISequence<Std.JSON.Values._IJSON> arr) : base() {
      this._arr = arr;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Array(_arr);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Values.JSON_Array;
      return oth != null && object.Equals(this._arr, oth._arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Values.JSON.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._arr);
      s += ")";
      return s;
    }
  }
} // end of namespace Std.JSON.Values
namespace Std.JSON.Errors {


  public interface _IDeserializationError {
    bool is_UnterminatedSequence { get; }
    bool is_UnsupportedEscape { get; }
    bool is_EscapeAtEOS { get; }
    bool is_EmptyNumber { get; }
    bool is_ExpectingEOF { get; }
    bool is_IntOverflow { get; }
    bool is_ReachedEOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_InvalidUnicode { get; }
    Dafny.ISequence<Dafny.Rune> dtor_str { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    _IDeserializationError DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class DeserializationError : _IDeserializationError {
    public DeserializationError() {
    }
    private static readonly Std.JSON.Errors._IDeserializationError theDefault = create_UnterminatedSequence();
    public static Std.JSON.Errors._IDeserializationError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Errors._IDeserializationError> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Errors._IDeserializationError>(Std.JSON.Errors.DeserializationError.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Errors._IDeserializationError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeserializationError create_UnterminatedSequence() {
      return new DeserializationError_UnterminatedSequence();
    }
    public static _IDeserializationError create_UnsupportedEscape(Dafny.ISequence<Dafny.Rune> str) {
      return new DeserializationError_UnsupportedEscape(str);
    }
    public static _IDeserializationError create_EscapeAtEOS() {
      return new DeserializationError_EscapeAtEOS();
    }
    public static _IDeserializationError create_EmptyNumber() {
      return new DeserializationError_EmptyNumber();
    }
    public static _IDeserializationError create_ExpectingEOF() {
      return new DeserializationError_ExpectingEOF();
    }
    public static _IDeserializationError create_IntOverflow() {
      return new DeserializationError_IntOverflow();
    }
    public static _IDeserializationError create_ReachedEOF() {
      return new DeserializationError_ReachedEOF();
    }
    public static _IDeserializationError create_ExpectingByte(byte expected, short b) {
      return new DeserializationError_ExpectingByte(expected, b);
    }
    public static _IDeserializationError create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new DeserializationError_ExpectingAnyByte(expected__sq, b);
    }
    public static _IDeserializationError create_InvalidUnicode() {
      return new DeserializationError_InvalidUnicode();
    }
    public bool is_UnterminatedSequence { get { return this is DeserializationError_UnterminatedSequence; } }
    public bool is_UnsupportedEscape { get { return this is DeserializationError_UnsupportedEscape; } }
    public bool is_EscapeAtEOS { get { return this is DeserializationError_EscapeAtEOS; } }
    public bool is_EmptyNumber { get { return this is DeserializationError_EmptyNumber; } }
    public bool is_ExpectingEOF { get { return this is DeserializationError_ExpectingEOF; } }
    public bool is_IntOverflow { get { return this is DeserializationError_IntOverflow; } }
    public bool is_ReachedEOF { get { return this is DeserializationError_ReachedEOF; } }
    public bool is_ExpectingByte { get { return this is DeserializationError_ExpectingByte; } }
    public bool is_ExpectingAnyByte { get { return this is DeserializationError_ExpectingAnyByte; } }
    public bool is_InvalidUnicode { get { return this is DeserializationError_InvalidUnicode; } }
    public Dafny.ISequence<Dafny.Rune> dtor_str {
      get {
        var d = this;
        return ((DeserializationError_UnsupportedEscape)d)._str;
      }
    }
    public byte dtor_expected {
      get {
        var d = this;
        return ((DeserializationError_ExpectingByte)d)._expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is DeserializationError_ExpectingByte) { return ((DeserializationError_ExpectingByte)d)._b; }
        return ((DeserializationError_ExpectingAnyByte)d)._b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((DeserializationError_ExpectingAnyByte)d)._expected__sq;
      }
    }
    public abstract _IDeserializationError DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      Std.JSON.Errors._IDeserializationError _source10 = this;
      if (_source10.is_UnterminatedSequence) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unterminated sequence");
      } else if (_source10.is_UnsupportedEscape) {
        Dafny.ISequence<Dafny.Rune> _295___mcc_h0 = _source10.dtor_str;
        Dafny.ISequence<Dafny.Rune> _296_str = _295___mcc_h0;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported escape sequence: "), _296_str);
      } else if (_source10.is_EscapeAtEOS) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Escape character at end of string");
      } else if (_source10.is_EmptyNumber) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Number must contain at least one digit");
      } else if (_source10.is_ExpectingEOF) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expecting EOF");
      } else if (_source10.is_IntOverflow) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Input length does not fit in a 32-bit counter");
      } else if (_source10.is_ReachedEOF) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Reached EOF");
      } else if (_source10.is_ExpectingByte) {
        byte _297___mcc_h1 = _source10.dtor_expected;
        short _298___mcc_h2 = _source10.dtor_b;
        short _299_b = _298___mcc_h2;
        byte _300_b0 = _297___mcc_h1;
        Dafny.ISequence<Dafny.Rune> _301_c = (((_299_b) > ((short)(0))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_299_b)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("EOF")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expecting '"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_300_b0)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("', read ")), _301_c);
      } else if (_source10.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _302___mcc_h3 = _source10.dtor_expected__sq;
        short _303___mcc_h4 = _source10.dtor_b;
        short _304_b = _303___mcc_h4;
        Dafny.ISequence<byte> _305_bs0 = _302___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _306_c = (((_304_b) > ((short)(0))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_304_b)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("EOF")));
        Dafny.ISequence<Dafny.Rune> _307_c0s = ((System.Func<Dafny.ISequence<Dafny.Rune>>) (() => {
          BigInteger dim4 = new BigInteger((_305_bs0).Count);
          var arr4 = new Dafny.Rune[Dafny.Helpers.ToIntChecked(dim4, "array size exceeds memory limit")];
          for (int i4 = 0; i4 < dim4; i4++) {
            var _308_idx = (BigInteger) i4;
            arr4[(int)(_308_idx)] = new Dafny.Rune((int)((_305_bs0).Select(_308_idx)));
          }
          return Dafny.Sequence<Dafny.Rune>.FromArray(arr4);
        }))();
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expecting one of '"), _307_c0s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("', read ")), _306_c);
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid Unicode sequence");
      }
    }
  }
  public class DeserializationError_UnterminatedSequence : DeserializationError {
    public DeserializationError_UnterminatedSequence() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_UnterminatedSequence();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_UnterminatedSequence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.UnterminatedSequence";
      return s;
    }
  }
  public class DeserializationError_UnsupportedEscape : DeserializationError {
    public readonly Dafny.ISequence<Dafny.Rune> _str;
    public DeserializationError_UnsupportedEscape(Dafny.ISequence<Dafny.Rune> str) : base() {
      this._str = str;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_UnsupportedEscape(_str);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_UnsupportedEscape;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.UnsupportedEscape";
      s += "(";
      s += this._str.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_EscapeAtEOS : DeserializationError {
    public DeserializationError_EscapeAtEOS() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_EscapeAtEOS();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_EscapeAtEOS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.EscapeAtEOS";
      return s;
    }
  }
  public class DeserializationError_EmptyNumber : DeserializationError {
    public DeserializationError_EmptyNumber() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_EmptyNumber();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_EmptyNumber;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.EmptyNumber";
      return s;
    }
  }
  public class DeserializationError_ExpectingEOF : DeserializationError {
    public DeserializationError_ExpectingEOF() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingEOF();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_ExpectingEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.ExpectingEOF";
      return s;
    }
  }
  public class DeserializationError_IntOverflow : DeserializationError {
    public DeserializationError_IntOverflow() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_IntOverflow();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_IntOverflow;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.IntOverflow";
      return s;
    }
  }
  public class DeserializationError_ReachedEOF : DeserializationError {
    public DeserializationError_ReachedEOF() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ReachedEOF();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_ReachedEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.ReachedEOF";
      return s;
    }
  }
  public class DeserializationError_ExpectingByte : DeserializationError {
    public readonly byte _expected;
    public readonly short _b;
    public DeserializationError_ExpectingByte(byte expected, short b) : base() {
      this._expected = expected;
      this._b = b;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingByte(_expected, _b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_ExpectingByte;
      return oth != null && this._expected == oth._expected && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_ExpectingAnyByte : DeserializationError {
    public readonly Dafny.ISequence<byte> _expected__sq;
    public readonly short _b;
    public DeserializationError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) : base() {
      this._expected__sq = expected__sq;
      this._b = b;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingAnyByte(_expected__sq, _b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_ExpectingAnyByte;
      return oth != null && object.Equals(this._expected__sq, oth._expected__sq) && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_InvalidUnicode : DeserializationError {
    public DeserializationError_InvalidUnicode() : base() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_InvalidUnicode();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.DeserializationError_InvalidUnicode;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.DeserializationError.InvalidUnicode";
      return s;
    }
  }

  public interface _ISerializationError {
    bool is_OutOfMemory { get; }
    bool is_IntTooLarge { get; }
    bool is_StringTooLong { get; }
    bool is_InvalidUnicode { get; }
    BigInteger dtor_i { get; }
    Dafny.ISequence<Dafny.Rune> dtor_s { get; }
    _ISerializationError DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class SerializationError : _ISerializationError {
    public SerializationError() {
    }
    private static readonly Std.JSON.Errors._ISerializationError theDefault = create_OutOfMemory();
    public static Std.JSON.Errors._ISerializationError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Errors._ISerializationError> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Errors._ISerializationError>(Std.JSON.Errors.SerializationError.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Errors._ISerializationError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISerializationError create_OutOfMemory() {
      return new SerializationError_OutOfMemory();
    }
    public static _ISerializationError create_IntTooLarge(BigInteger i) {
      return new SerializationError_IntTooLarge(i);
    }
    public static _ISerializationError create_StringTooLong(Dafny.ISequence<Dafny.Rune> s) {
      return new SerializationError_StringTooLong(s);
    }
    public static _ISerializationError create_InvalidUnicode() {
      return new SerializationError_InvalidUnicode();
    }
    public bool is_OutOfMemory { get { return this is SerializationError_OutOfMemory; } }
    public bool is_IntTooLarge { get { return this is SerializationError_IntTooLarge; } }
    public bool is_StringTooLong { get { return this is SerializationError_StringTooLong; } }
    public bool is_InvalidUnicode { get { return this is SerializationError_InvalidUnicode; } }
    public BigInteger dtor_i {
      get {
        var d = this;
        return ((SerializationError_IntTooLarge)d)._i;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_s {
      get {
        var d = this;
        return ((SerializationError_StringTooLong)d)._s;
      }
    }
    public abstract _ISerializationError DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      Std.JSON.Errors._ISerializationError _source11 = this;
      if (_source11.is_OutOfMemory) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Out of memory");
      } else if (_source11.is_IntTooLarge) {
        BigInteger _309___mcc_h0 = _source11.dtor_i;
        BigInteger _310_i = _309___mcc_h0;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Integer too large: "), Std.Strings.__default.OfInt(_310_i));
      } else if (_source11.is_StringTooLong) {
        Dafny.ISequence<Dafny.Rune> _311___mcc_h1 = _source11.dtor_s;
        Dafny.ISequence<Dafny.Rune> _312_s = _311___mcc_h1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("String too long: "), _312_s);
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Invalid Unicode sequence");
      }
    }
  }
  public class SerializationError_OutOfMemory : SerializationError {
    public SerializationError_OutOfMemory() : base() {
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_OutOfMemory();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.SerializationError_OutOfMemory;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.SerializationError.OutOfMemory";
      return s;
    }
  }
  public class SerializationError_IntTooLarge : SerializationError {
    public readonly BigInteger _i;
    public SerializationError_IntTooLarge(BigInteger i) : base() {
      this._i = i;
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_IntTooLarge(_i);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.SerializationError_IntTooLarge;
      return oth != null && this._i == oth._i;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.SerializationError.IntTooLarge";
      s += "(";
      s += Dafny.Helpers.ToString(this._i);
      s += ")";
      return s;
    }
  }
  public class SerializationError_StringTooLong : SerializationError {
    public readonly Dafny.ISequence<Dafny.Rune> _s;
    public SerializationError_StringTooLong(Dafny.ISequence<Dafny.Rune> s) : base() {
      this._s = s;
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_StringTooLong(_s);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.SerializationError_StringTooLong;
      return oth != null && object.Equals(this._s, oth._s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Errors.SerializationError.StringTooLong";
      ss += "(";
      ss += this._s.ToVerbatimString(true);
      ss += ")";
      return ss;
    }
  }
  public class SerializationError_InvalidUnicode : SerializationError {
    public SerializationError_InvalidUnicode() : base() {
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_InvalidUnicode();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Errors.SerializationError_InvalidUnicode;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Errors.SerializationError.InvalidUnicode";
      return s;
    }
  }
} // end of namespace Std.JSON.Errors
namespace Std.JSON.Spec {

  public partial class __default {
    public static Dafny.ISequence<ushort> EscapeUnicode(ushort c) {
      Dafny.ISequence<Dafny.Rune> _313_sStr = Std.Strings.HexConversion.__default.OfNat(new BigInteger(c));
      Dafny.ISequence<ushort> _314_s = Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_313_sStr);
      return Dafny.Sequence<ushort>.Concat(_314_s, ((System.Func<Dafny.ISequence<ushort>>) (() => {
        BigInteger dim5 = (new BigInteger(4)) - (new BigInteger((_314_s).Count));
        var arr5 = new ushort[Dafny.Helpers.ToIntChecked(dim5, "array size exceeds memory limit")];
        for (int i5 = 0; i5 < dim5; i5++) {
          var _315___v8 = (BigInteger) i5;
          arr5[(int)(_315___v8)] = (ushort)((new Dafny.Rune(' ')).Value);
        }
        return Dafny.Sequence<ushort>.FromArray(arr5);
      }))());
    }
    public static Dafny.ISequence<ushort> Escape(Dafny.ISequence<ushort> str, BigInteger start)
    {
      Dafny.ISequence<ushort> _316___accumulator = Dafny.Sequence<ushort>.FromElements();
    TAIL_CALL_START: ;
      var _pat_let_tv0 = str;
      var _pat_let_tv1 = start;
      if ((start) >= (new BigInteger((str).Count))) {
        return Dafny.Sequence<ushort>.Concat(_316___accumulator, Dafny.Sequence<ushort>.FromElements());
      } else {
        _316___accumulator = Dafny.Sequence<ushort>.Concat(_316___accumulator, ((((str).Select(start)) == ((ushort)(34))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\\""))) : (((((str).Select(start)) == ((ushort)(92))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\\\"))) : (((((str).Select(start)) == ((ushort)(8))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\b"))) : (((((str).Select(start)) == ((ushort)(12))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\f"))) : (((((str).Select(start)) == ((ushort)(10))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\n"))) : (((((str).Select(start)) == ((ushort)(13))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\r"))) : (((((str).Select(start)) == ((ushort)(9))) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\t"))) : (Dafny.Helpers.Let<ushort, Dafny.ISequence<ushort>>((str).Select(start), _pat_let1_0 => Dafny.Helpers.Let<ushort, Dafny.ISequence<ushort>>(_pat_let1_0, _317_c => (((_317_c) < ((ushort)(31))) ? (Dafny.Sequence<ushort>.Concat(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\u")), Std.JSON.Spec.__default.EscapeUnicode(_317_c))) : (Dafny.Sequence<ushort>.FromElements((_pat_let_tv0).Select(_pat_let_tv1)))))))))))))))))))));
        Dafny.ISequence<ushort> _in61 = str;
        BigInteger _in62 = (start) + (BigInteger.One);
        str = _in61;
        start = _in62;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> EscapeToUTF8(Dafny.ISequence<Dafny.Rune> str, BigInteger start)
    {
      Std.Wrappers._IResult<Dafny.ISequence<ushort>, Std.JSON.Errors._ISerializationError> _318_valueOrError0 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(str)).ToResult<Std.JSON.Errors._ISerializationError>(Std.JSON.Errors.SerializationError.create_InvalidUnicode());
      if ((_318_valueOrError0).IsFailure()) {
        return (_318_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<ushort> _319_utf16 = (_318_valueOrError0).Extract();
        Dafny.ISequence<ushort> _320_escaped = Std.JSON.Spec.__default.Escape(_319_utf16, BigInteger.Zero);
        Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Std.JSON.Errors._ISerializationError> _321_valueOrError1 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_320_escaped)).ToResult<Std.JSON.Errors._ISerializationError>(Std.JSON.Errors.SerializationError.create_InvalidUnicode());
        if ((_321_valueOrError1).IsFailure()) {
          return (_321_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<Dafny.Rune> _322_utf32 = (_321_valueOrError1).Extract();
          return (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF8Checked(_322_utf32)).ToResult<Std.JSON.Errors._ISerializationError>(Std.JSON.Errors.SerializationError.create_InvalidUnicode());
        }
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> String(Dafny.ISequence<Dafny.Rune> str) {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _323_valueOrError0 = Std.JSON.Spec.__default.EscapeToUTF8(str, BigInteger.Zero);
      if ((_323_valueOrError0).IsFailure()) {
        return (_323_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _324_inBytes = (_323_valueOrError0).Extract();
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), _324_inBytes), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""))));
      }
    }
    public static Dafny.ISequence<byte> IntToBytes(BigInteger n) {
      Dafny.ISequence<Dafny.Rune> _325_s = Std.Strings.__default.OfInt(n);
      return Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_325_s);
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Number(Std.JSON.Values._IDecimal dec) {
      return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Std.JSON.Spec.__default.IntToBytes((dec).dtor_n), ((((dec).dtor_e10).Sign == 0) ? (Dafny.Sequence<byte>.FromElements()) : (Dafny.Sequence<byte>.Concat(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("e")), Std.JSON.Spec.__default.IntToBytes((dec).dtor_e10))))));
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> KeyValue(_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON> kv) {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _326_valueOrError0 = Std.JSON.Spec.__default.String((kv).dtor__0);
      if ((_326_valueOrError0).IsFailure()) {
        return (_326_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _327_key = (_326_valueOrError0).Extract();
        Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _328_valueOrError1 = Std.JSON.Spec.__default.JSON((kv).dtor__1);
        if ((_328_valueOrError1).IsFailure()) {
          return (_328_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<byte> _329_value = (_328_valueOrError1).Extract();
          return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_327_key, Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(":"))), _329_value));
        }
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Join(Dafny.ISequence<byte> sep, Dafny.ISequence<Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>> items)
    {
      if ((new BigInteger((items).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.FromElements());
      } else {
        Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _330_valueOrError0 = (items).Select(BigInteger.Zero);
        if ((_330_valueOrError0).IsFailure()) {
          return (_330_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<byte> _331_first = (_330_valueOrError0).Extract();
          if ((new BigInteger((items).Count)) == (BigInteger.One)) {
            return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(_331_first);
          } else {
            Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _332_valueOrError1 = Std.JSON.Spec.__default.Join(sep, (items).Drop(BigInteger.One));
            if ((_332_valueOrError1).IsFailure()) {
              return (_332_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
            } else {
              Dafny.ISequence<byte> _333_rest = (_332_valueOrError1).Extract();
              return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_331_first, sep), _333_rest));
            }
          }
        }
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> obj) {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _334_valueOrError0 = Std.JSON.Spec.__default.Join(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",")), ((System.Func<Dafny.ISequence<Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>>>) (() => {
        BigInteger dim6 = new BigInteger((obj).Count);
        var arr6 = new Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>[Dafny.Helpers.ToIntChecked(dim6, "array size exceeds memory limit")];
        for (int i6 = 0; i6 < dim6; i6++) {
          var _335_i = (BigInteger) i6;
          arr6[(int)(_335_i)] = Std.JSON.Spec.__default.KeyValue((obj).Select(_335_i));
        }
        return Dafny.Sequence<Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>>.FromArray(arr6);
      }))());
      if ((_334_valueOrError0).IsFailure()) {
        return (_334_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _336_middle = (_334_valueOrError0).Extract();
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _336_middle), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"))));
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Array(Dafny.ISequence<Std.JSON.Values._IJSON> arr) {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _337_valueOrError0 = Std.JSON.Spec.__default.Join(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",")), ((System.Func<Dafny.ISequence<Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>>>) (() => {
        BigInteger dim7 = new BigInteger((arr).Count);
        var arr7 = new Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>[Dafny.Helpers.ToIntChecked(dim7, "array size exceeds memory limit")];
        for (int i7 = 0; i7 < dim7; i7++) {
          var _338_i = (BigInteger) i7;
          arr7[(int)(_338_i)] = Std.JSON.Spec.__default.JSON((arr).Select(_338_i));
        }
        return Dafny.Sequence<Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>>.FromArray(arr7);
      }))());
      if ((_337_valueOrError0).IsFailure()) {
        return (_337_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _339_middle = (_337_valueOrError0).Extract();
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), _339_middle), Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"))));
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> JSON(Std.JSON.Values._IJSON js) {
      Std.JSON.Values._IJSON _source12 = js;
      if (_source12.is_Null) {
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null")));
      } else if (_source12.is_Bool) {
        bool _340___mcc_h0 = _source12.dtor_b;
        bool _341_b = _340___mcc_h0;
        return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success(((_341_b) ? (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"))) : (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))));
      } else if (_source12.is_String) {
        Dafny.ISequence<Dafny.Rune> _342___mcc_h1 = _source12.dtor_str;
        Dafny.ISequence<Dafny.Rune> _343_str = _342___mcc_h1;
        return Std.JSON.Spec.__default.String(_343_str);
      } else if (_source12.is_Number) {
        Std.JSON.Values._IDecimal _344___mcc_h2 = _source12.dtor_num;
        Std.JSON.Values._IDecimal _345_dec = _344___mcc_h2;
        return Std.JSON.Spec.__default.Number(_345_dec);
      } else if (_source12.is_Object) {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _346___mcc_h3 = _source12.dtor_obj;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _347_obj = _346___mcc_h3;
        return Std.JSON.Spec.__default.Object(_347_obj);
      } else {
        Dafny.ISequence<Std.JSON.Values._IJSON> _348___mcc_h4 = _source12.dtor_arr;
        Dafny.ISequence<Std.JSON.Values._IJSON> _349_arr = _348___mcc_h4;
        return Std.JSON.Spec.__default.Array(_349_arr);
      }
    }
  }
} // end of namespace Std.JSON.Spec
namespace Std.JSON.Utils.Views.Core {

  public partial class __default {
    public static bool Adjacent(Std.JSON.Utils.Views.Core._IView__ lv, Std.JSON.Utils.Views.Core._IView__ rv)
    {
      return (((lv).dtor_end) == ((rv).dtor_beg)) && (((lv).dtor_s).Equals((rv).dtor_s));
    }
    public static Std.JSON.Utils.Views.Core._IView__ Merge(Std.JSON.Utils.Views.Core._IView__ lv, Std.JSON.Utils.Views.Core._IView__ rv)
    {
      Std.JSON.Utils.Views.Core._IView__ _350_dt__update__tmp_h0 = lv;
      uint _351_dt__update_hend_h0 = (rv).dtor_end;
      return Std.JSON.Utils.Views.Core.View__.create((_350_dt__update__tmp_h0).dtor_s, (_350_dt__update__tmp_h0).dtor_beg, _351_dt__update_hend_h0);
    }
  }

  public partial class View {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Utils.Views.Core.View.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IView__ {
    bool is_View { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_end { get; }
    _IView__ DowncastClone();
    bool Empty_q { get; }
    uint Length();
    Dafny.ISequence<byte> Bytes();
    bool Byte_q(byte c);
    bool Char_q(Dafny.Rune c);
    byte At(uint idx);
    short Peek();
    void CopyTo(byte[] dest, uint start);
  }
  public class View__ : _IView__ {
    public readonly Dafny.ISequence<byte> _s;
    public readonly uint _beg;
    public readonly uint _end;
    public View__(Dafny.ISequence<byte> s, uint beg, uint end) {
      this._s = s;
      this._beg = beg;
      this._end = end;
    }
    public _IView__ DowncastClone() {
      if (this is _IView__ dt) { return dt; }
      return new View__(_s, _beg, _end);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Views.Core.View__;
      return oth != null && object.Equals(this._s, oth._s) && this._beg == oth._beg && this._end == oth._end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Core.View_.View";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._end);
      ss += ")";
      return ss;
    }
    private static readonly Std.JSON.Utils.Views.Core._IView__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0);
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Utils.Views.Core.View__.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IView__ create(Dafny.ISequence<byte> s, uint beg, uint end) {
      return new View__(s, beg, end);
    }
    public static _IView__ create_View(Dafny.ISequence<byte> s, uint beg, uint end) {
      return create(s, beg, end);
    }
    public bool is_View { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this._s;
      }
    }
    public uint dtor_beg {
      get {
        return this._beg;
      }
    }
    public uint dtor_end {
      get {
        return this._end;
      }
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public static Std.JSON.Utils.Views.Core._IView__ OfBytes(Dafny.ISequence<byte> bs) {
      return Std.JSON.Utils.Views.Core.View__.create(bs, (uint)(0U), (uint)(bs).LongCount);
    }
    public static Dafny.ISequence<byte> OfString(Dafny.ISequence<Dafny.Rune> s) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim8 = new BigInteger((s).Count);
        var arr8 = new byte[Dafny.Helpers.ToIntChecked(dim8, "array size exceeds memory limit")];
        for (int i8 = 0; i8 < dim8; i8++) {
          var _352_i = (BigInteger) i8;
          arr8[(int)(_352_i)] = (byte)(((s).Select(_352_i)).Value);
        }
        return Dafny.Sequence<byte>.FromArray(arr8);
      }))();
    }
    public bool Byte_q(byte c)
    {
      bool _hresult = false;
      _hresult = (((this).Length()) == (1U)) && (((this).At(0U)) == (c));
      return _hresult;
      return _hresult;
    }
    public bool Char_q(Dafny.Rune c) {
      return (this).Byte_q((byte)((c).Value));
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public short Peek() {
      if ((this).Empty_q) {
        return (short)(-1);
      } else {
        return (short)((this).At(0U));
      }
    }
    public void CopyTo(byte[] dest, uint start)
    {
      uint _hi0 = (this).Length();
      for (uint _353_idx = 0U; _353_idx < _hi0; _353_idx++) {
        uint _index6 = (start) + (_353_idx);
        (dest)[(int)(_index6)] = ((this).dtor_s).Select(((this).dtor_beg) + (_353_idx));
      }
    }
    public static Std.JSON.Utils.Views.Core._IView__ Empty { get {
      return Std.JSON.Utils.Views.Core.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    } }
    public bool Empty_q { get {
      return ((this).dtor_beg) == ((this).dtor_end);
    } }
  }
} // end of namespace Std.JSON.Utils.Views.Core
namespace Std.JSON.Utils.Views.Writers {


  public interface _IChain {
    bool is_Empty { get; }
    bool is_Chain { get; }
    Std.JSON.Utils.Views.Writers._IChain dtor_previous { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_v { get; }
    _IChain DowncastClone();
    BigInteger Length();
    BigInteger Count();
    Dafny.ISequence<byte> Bytes();
    Std.JSON.Utils.Views.Writers._IChain Append(Std.JSON.Utils.Views.Core._IView__ v_k);
    void CopyTo(byte[] dest, uint end);
  }
  public abstract class Chain : _IChain {
    public Chain() {
    }
    private static readonly Std.JSON.Utils.Views.Writers._IChain theDefault = create_Empty();
    public static Std.JSON.Utils.Views.Writers._IChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IChain> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IChain>(Std.JSON.Utils.Views.Writers.Chain.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IChain create_Empty() {
      return new Chain_Empty();
    }
    public static _IChain create_Chain(Std.JSON.Utils.Views.Writers._IChain previous, Std.JSON.Utils.Views.Core._IView__ v) {
      return new Chain_Chain(previous, v);
    }
    public bool is_Empty { get { return this is Chain_Empty; } }
    public bool is_Chain { get { return this is Chain_Chain; } }
    public Std.JSON.Utils.Views.Writers._IChain dtor_previous {
      get {
        var d = this;
        return ((Chain_Chain)d)._previous;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_v {
      get {
        var d = this;
        return ((Chain_Chain)d)._v;
      }
    }
    public abstract _IChain DowncastClone();
    public BigInteger Length() {
      BigInteger _354___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_354___accumulator);
      } else {
        _354___accumulator = (new BigInteger(((_this).dtor_v).Length())) + (_354___accumulator);
        Std.JSON.Utils.Views.Writers._IChain _in63 = (_this).dtor_previous;
        _this = _in63;
        ;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger Count() {
      BigInteger _355___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_355___accumulator);
      } else {
        _355___accumulator = (BigInteger.One) + (_355___accumulator);
        Std.JSON.Utils.Views.Writers._IChain _in64 = (_this).dtor_previous;
        _this = _in64;
        ;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      Dafny.ISequence<byte> _356___accumulator = Dafny.Sequence<byte>.FromElements();
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _356___accumulator);
      } else {
        _356___accumulator = Dafny.Sequence<byte>.Concat(((_this).dtor_v).Bytes(), _356___accumulator);
        Std.JSON.Utils.Views.Writers._IChain _in65 = (_this).dtor_previous;
        _this = _in65;
        ;
        goto TAIL_CALL_START;
      }
    }
    public Std.JSON.Utils.Views.Writers._IChain Append(Std.JSON.Utils.Views.Core._IView__ v_k) {
      if (((this).is_Chain) && (Std.JSON.Utils.Views.Core.__default.Adjacent((this).dtor_v, v_k))) {
        return Std.JSON.Utils.Views.Writers.Chain.create_Chain((this).dtor_previous, Std.JSON.Utils.Views.Core.__default.Merge((this).dtor_v, v_k));
      } else {
        return Std.JSON.Utils.Views.Writers.Chain.create_Chain(this, v_k);
      }
    }
    public void CopyTo(byte[] dest, uint end)
    {
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Chain) {
        uint _357_end;
        _357_end = (end) - (((_this).dtor_v).Length());
        ((_this).dtor_v).CopyTo(dest, _357_end);
        Std.JSON.Utils.Views.Writers._IChain _in66 = (_this).dtor_previous;
        byte[] _in67 = dest;
        uint _in68 = _357_end;
        _this = _in66;
        ;
        dest = _in67;
        end = _in68;
        goto TAIL_CALL_START;
      }
    }
  }
  public class Chain_Empty : Chain {
    public Chain_Empty() : base() {
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Views.Writers.Chain_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Writers.Chain.Empty";
      return s;
    }
  }
  public class Chain_Chain : Chain {
    public readonly Std.JSON.Utils.Views.Writers._IChain _previous;
    public readonly Std.JSON.Utils.Views.Core._IView__ _v;
    public Chain_Chain(Std.JSON.Utils.Views.Writers._IChain previous, Std.JSON.Utils.Views.Core._IView__ v) : base() {
      this._previous = previous;
      this._v = v;
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Chain(_previous, _v);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Views.Writers.Chain_Chain;
      return oth != null && object.Equals(this._previous, oth._previous) && object.Equals(this._v, oth._v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._previous));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Writers.Chain.Chain";
      s += "(";
      s += Dafny.Helpers.ToString(this._previous);
      s += ", ";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
  }

  public partial class Writer {
    private static readonly Std.JSON.Utils.Views.Writers._IWriter__ Witness = Std.JSON.Utils.Views.Writers.Writer__.create(0U, Std.JSON.Utils.Views.Writers.Chain.create_Empty());
    public static Std.JSON.Utils.Views.Writers._IWriter__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__>(Std.JSON.Utils.Views.Writers.Writer.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IWriter__ {
    bool is_Writer { get; }
    uint dtor_length { get; }
    Std.JSON.Utils.Views.Writers._IChain dtor_chain { get; }
    _IWriter__ DowncastClone();
    bool Empty_q { get; }
    bool Unsaturated_q { get; }
    Dafny.ISequence<byte> Bytes();
    Std.JSON.Utils.Views.Writers._IWriter__ Append(Std.JSON.Utils.Views.Core._IView__ v_k);
    Std.JSON.Utils.Views.Writers._IWriter__ Then(Func<Std.JSON.Utils.Views.Writers._IWriter__, Std.JSON.Utils.Views.Writers._IWriter__> fn);
    void CopyTo(byte[] dest);
    byte[] ToArray();
  }
  public class Writer__ : _IWriter__ {
    public readonly uint _length;
    public readonly Std.JSON.Utils.Views.Writers._IChain _chain;
    public Writer__(uint length, Std.JSON.Utils.Views.Writers._IChain chain) {
      this._length = length;
      this._chain = chain;
    }
    public _IWriter__ DowncastClone() {
      if (this is _IWriter__ dt) { return dt; }
      return new Writer__(_length, _chain);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Views.Writers.Writer__;
      return oth != null && this._length == oth._length && object.Equals(this._chain, oth._chain);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._chain));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Writers.Writer_.Writer";
      s += "(";
      s += Dafny.Helpers.ToString(this._length);
      s += ", ";
      s += Dafny.Helpers.ToString(this._chain);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Utils.Views.Writers._IWriter__ theDefault = create(0, Std.JSON.Utils.Views.Writers.Chain.Default());
    public static Std.JSON.Utils.Views.Writers._IWriter__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__>(Std.JSON.Utils.Views.Writers.Writer__.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Writers._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWriter__ create(uint length, Std.JSON.Utils.Views.Writers._IChain chain) {
      return new Writer__(length, chain);
    }
    public static _IWriter__ create_Writer(uint length, Std.JSON.Utils.Views.Writers._IChain chain) {
      return create(length, chain);
    }
    public bool is_Writer { get { return true; } }
    public uint dtor_length {
      get {
        return this._length;
      }
    }
    public Std.JSON.Utils.Views.Writers._IChain dtor_chain {
      get {
        return this._chain;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_chain).Bytes();
    }
    public static uint SaturatedAddU32(uint a, uint b)
    {
      if ((a) <= ((Std.BoundedInts.__default.UINT32__MAX) - (b))) {
        return (a) + (b);
      } else {
        return Std.BoundedInts.__default.UINT32__MAX;
      }
    }
    public Std.JSON.Utils.Views.Writers._IWriter__ Append(Std.JSON.Utils.Views.Core._IView__ v_k) {
      return Std.JSON.Utils.Views.Writers.Writer__.create(Std.JSON.Utils.Views.Writers.Writer__.SaturatedAddU32((this).dtor_length, (v_k).Length()), ((this).dtor_chain).Append(v_k));
    }
    public Std.JSON.Utils.Views.Writers._IWriter__ Then(Func<Std.JSON.Utils.Views.Writers._IWriter__, Std.JSON.Utils.Views.Writers._IWriter__> fn) {
      return Dafny.Helpers.Id<Func<Std.JSON.Utils.Views.Writers._IWriter__, Std.JSON.Utils.Views.Writers._IWriter__>>(fn)(this);
    }
    public void CopyTo(byte[] dest)
    {
      ((this).dtor_chain).CopyTo(dest, (this).dtor_length);
    }
    public byte[] ToArray()
    {
      byte[] bs = new byte[0];
      Func<BigInteger, byte> _init4 = ((System.Func<BigInteger, byte>)((_358_i) => {
        return (byte)(0);
      }));
      byte[] _nw5 = new byte[Dafny.Helpers.ToIntChecked((this).dtor_length, "array size exceeds memory limit")];
      for (var _i0_4 = 0; _i0_4 < new BigInteger(_nw5.Length); _i0_4++) {
        _nw5[(int)(_i0_4)] = _init4(_i0_4);
      }
      bs = _nw5;
      (this).CopyTo(bs);
      return bs;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Empty { get {
      return Std.JSON.Utils.Views.Writers.Writer__.create(0U, Std.JSON.Utils.Views.Writers.Chain.create_Empty());
    } }
    public bool Unsaturated_q { get {
      return ((this).dtor_length) != (Std.BoundedInts.__default.UINT32__MAX);
    } }
    public bool Empty_q { get {
      return ((this).dtor_chain).is_Empty;
    } }
  }
} // end of namespace Std.JSON.Utils.Views.Writers
namespace Std.JSON.Utils.Views {

} // end of namespace Std.JSON.Utils.Views
namespace Std.JSON.Utils.Lexers.Core {


  public interface _ILexerResult<out T, out R> {
    bool is_Accept { get; }
    bool is_Reject { get; }
    bool is_Partial { get; }
    R dtor_err { get; }
    T dtor_st { get; }
    _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public abstract class LexerResult<T, R> : _ILexerResult<T, R> {
    public LexerResult() {
    }
    public static Std.JSON.Utils.Lexers.Core._ILexerResult<T, R> Default() {
      return create_Accept();
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Lexers.Core._ILexerResult<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Lexers.Core._ILexerResult<T, R>>(Std.JSON.Utils.Lexers.Core.LexerResult<T, R>.Default());
    }
    public static _ILexerResult<T, R> create_Accept() {
      return new LexerResult_Accept<T, R>();
    }
    public static _ILexerResult<T, R> create_Reject(R err) {
      return new LexerResult_Reject<T, R>(err);
    }
    public static _ILexerResult<T, R> create_Partial(T st) {
      return new LexerResult_Partial<T, R>(st);
    }
    public bool is_Accept { get { return this is LexerResult_Accept<T, R>; } }
    public bool is_Reject { get { return this is LexerResult_Reject<T, R>; } }
    public bool is_Partial { get { return this is LexerResult_Partial<T, R>; } }
    public R dtor_err {
      get {
        var d = this;
        return ((LexerResult_Reject<T, R>)d)._err;
      }
    }
    public T dtor_st {
      get {
        var d = this;
        return ((LexerResult_Partial<T, R>)d)._st;
      }
    }
    public abstract _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class LexerResult_Accept<T, R> : LexerResult<T, R> {
    public LexerResult_Accept() : base() {
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Accept<__T, __R>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Core.LexerResult_Accept<T, R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Core.LexerResult.Accept";
      return s;
    }
  }
  public class LexerResult_Reject<T, R> : LexerResult<T, R> {
    public readonly R _err;
    public LexerResult_Reject(R err) : base() {
      this._err = err;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Reject<__T, __R>(converter1(_err));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Core.LexerResult_Reject<T, R>;
      return oth != null && object.Equals(this._err, oth._err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Core.LexerResult.Reject";
      s += "(";
      s += Dafny.Helpers.ToString(this._err);
      s += ")";
      return s;
    }
  }
  public class LexerResult_Partial<T, R> : LexerResult<T, R> {
    public readonly T _st;
    public LexerResult_Partial(T st) : base() {
      this._st = st;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Partial<__T, __R>(converter0(_st));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Core.LexerResult_Partial<T, R>;
      return oth != null && object.Equals(this._st, oth._st);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._st));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Core.LexerResult.Partial";
      s += "(";
      s += Dafny.Helpers.ToString(this._st);
      s += ")";
      return s;
    }
  }
} // end of namespace Std.JSON.Utils.Lexers.Core
namespace Std.JSON.Utils.Lexers.Strings {

  public partial class __default {
    public static Std.JSON.Utils.Lexers.Core._ILexerResult<bool, __R> StringBody<__R>(bool escaped, short @byte)
    {
      if ((@byte) == ((short)((new Dafny.Rune('\\')).Value))) {
        return Std.JSON.Utils.Lexers.Core.LexerResult<bool, __R>.create_Partial(!(escaped));
      } else if (((@byte) == ((short)((new Dafny.Rune('\"')).Value))) && (!(escaped))) {
        return Std.JSON.Utils.Lexers.Core.LexerResult<bool, __R>.create_Accept();
      } else {
        return Std.JSON.Utils.Lexers.Core.LexerResult<bool, __R>.create_Partial(false);
      }
    }
    public static Std.JSON.Utils.Lexers.Core._ILexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>> String(Std.JSON.Utils.Lexers.Strings._IStringLexerState st, short @byte)
    {
      Std.JSON.Utils.Lexers.Strings._IStringLexerState _source13 = st;
      if (_source13.is_Start) {
        if ((@byte) == ((short)((new Dafny.Rune('\"')).Value))) {
          return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Partial(Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(false));
        } else {
          return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Reject(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("String must start with double quote"));
        }
      } else if (_source13.is_Body) {
        bool _359___mcc_h0 = _source13.dtor_escaped;
        bool _360_escaped = _359___mcc_h0;
        if ((@byte) == ((short)((new Dafny.Rune('\\')).Value))) {
          return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Partial(Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(!(_360_escaped)));
        } else if (((@byte) == ((short)((new Dafny.Rune('\"')).Value))) && (!(_360_escaped))) {
          return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Partial(Std.JSON.Utils.Lexers.Strings.StringLexerState.create_End());
        } else {
          return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Partial(Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(false));
        }
      } else {
        return Std.JSON.Utils.Lexers.Core.LexerResult<Std.JSON.Utils.Lexers.Strings._IStringLexerState, Dafny.ISequence<Dafny.Rune>>.create_Accept();
      }
    }
    public static bool StringBodyLexerStart { get {
      return false;
    } }
    public static Std.JSON.Utils.Lexers.Strings._IStringLexerState StringLexerStart { get {
      return Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Start();
    } }
  }

  public interface _IStringLexerState {
    bool is_Start { get; }
    bool is_Body { get; }
    bool is_End { get; }
    bool dtor_escaped { get; }
    _IStringLexerState DowncastClone();
  }
  public abstract class StringLexerState : _IStringLexerState {
    public StringLexerState() {
    }
    private static readonly Std.JSON.Utils.Lexers.Strings._IStringLexerState theDefault = create_Start();
    public static Std.JSON.Utils.Lexers.Strings._IStringLexerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Lexers.Strings._IStringLexerState> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Lexers.Strings._IStringLexerState>(Std.JSON.Utils.Lexers.Strings.StringLexerState.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Lexers.Strings._IStringLexerState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStringLexerState create_Start() {
      return new StringLexerState_Start();
    }
    public static _IStringLexerState create_Body(bool escaped) {
      return new StringLexerState_Body(escaped);
    }
    public static _IStringLexerState create_End() {
      return new StringLexerState_End();
    }
    public bool is_Start { get { return this is StringLexerState_Start; } }
    public bool is_Body { get { return this is StringLexerState_Body; } }
    public bool is_End { get { return this is StringLexerState_End; } }
    public bool dtor_escaped {
      get {
        var d = this;
        return ((StringLexerState_Body)d)._escaped;
      }
    }
    public abstract _IStringLexerState DowncastClone();
  }
  public class StringLexerState_Start : StringLexerState {
    public StringLexerState_Start() : base() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Start();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Strings.StringLexerState_Start;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Strings.StringLexerState.Start";
      return s;
    }
  }
  public class StringLexerState_Body : StringLexerState {
    public readonly bool _escaped;
    public StringLexerState_Body(bool escaped) : base() {
      this._escaped = escaped;
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Body(_escaped);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Strings.StringLexerState_Body;
      return oth != null && this._escaped == oth._escaped;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._escaped));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Strings.StringLexerState.Body";
      s += "(";
      s += Dafny.Helpers.ToString(this._escaped);
      s += ")";
      return s;
    }
  }
  public class StringLexerState_End : StringLexerState {
    public StringLexerState_End() : base() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_End();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Lexers.Strings.StringLexerState_End;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Strings.StringLexerState.End";
      return s;
    }
  }
} // end of namespace Std.JSON.Utils.Lexers.Strings
namespace Std.JSON.Utils.Lexers {

} // end of namespace Std.JSON.Utils.Lexers
namespace Std.JSON.Utils.Cursors {


  public interface _ISplit<out T> {
    bool is_SP { get; }
    T dtor_t { get; }
    Std.JSON.Utils.Cursors._ICursor__ dtor_cs { get; }
    _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Split<T> : _ISplit<T> {
    public readonly T _t;
    public readonly Std.JSON.Utils.Cursors._ICursor__ _cs;
    public Split(T t, Std.JSON.Utils.Cursors._ICursor__ cs) {
      this._t = t;
      this._cs = cs;
    }
    public _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _ISplit<__T> dt) { return dt; }
      return new Split<__T>(converter0(_t), _cs);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.Split<T>;
      return oth != null && object.Equals(this._t, oth._t) && object.Equals(this._cs, oth._cs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors.Split.SP";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cs);
      s += ")";
      return s;
    }
    public static Std.JSON.Utils.Cursors._ISplit<T> Default(T _default_T) {
      return create(_default_T, Std.JSON.Utils.Cursors.FreshCursor.Default());
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ISplit<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ISplit<T>>(Std.JSON.Utils.Cursors.Split<T>.Default(_td_T.Default()));
    }
    public static _ISplit<T> create(T t, Std.JSON.Utils.Cursors._ICursor__ cs) {
      return new Split<T>(t, cs);
    }
    public static _ISplit<T> create_SP(T t, Std.JSON.Utils.Cursors._ICursor__ cs) {
      return create(t, cs);
    }
    public bool is_SP { get { return true; } }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public Std.JSON.Utils.Cursors._ICursor__ dtor_cs {
      get {
        return this._cs;
      }
    }
  }

  public partial class Cursor {
    private static readonly Std.JSON.Utils.Cursors._ICursor__ Witness = Std.JSON.Utils.Cursors.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Std.JSON.Utils.Cursors._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__>(Std.JSON.Utils.Cursors.Cursor.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class FreshCursor {
    private static readonly Std.JSON.Utils.Cursors._ICursor__ Witness = Std.JSON.Utils.Cursors.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Std.JSON.Utils.Cursors._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__>(Std.JSON.Utils.Cursors.FreshCursor.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICursorError<out R> {
    bool is_EOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_OtherError { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    R dtor_err { get; }
    _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
  }
  public abstract class CursorError<R> : _ICursorError<R> {
    public CursorError() {
    }
    public static Std.JSON.Utils.Cursors._ICursorError<R> Default() {
      return create_EOF();
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursorError<R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursorError<R>>(Std.JSON.Utils.Cursors.CursorError<R>.Default());
    }
    public static _ICursorError<R> create_EOF() {
      return new CursorError_EOF<R>();
    }
    public static _ICursorError<R> create_ExpectingByte(byte expected, short b) {
      return new CursorError_ExpectingByte<R>(expected, b);
    }
    public static _ICursorError<R> create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new CursorError_ExpectingAnyByte<R>(expected__sq, b);
    }
    public static _ICursorError<R> create_OtherError(R err) {
      return new CursorError_OtherError<R>(err);
    }
    public bool is_EOF { get { return this is CursorError_EOF<R>; } }
    public bool is_ExpectingByte { get { return this is CursorError_ExpectingByte<R>; } }
    public bool is_ExpectingAnyByte { get { return this is CursorError_ExpectingAnyByte<R>; } }
    public bool is_OtherError { get { return this is CursorError_OtherError<R>; } }
    public byte dtor_expected {
      get {
        var d = this;
        return ((CursorError_ExpectingByte<R>)d)._expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is CursorError_ExpectingByte<R>) { return ((CursorError_ExpectingByte<R>)d)._b; }
        return ((CursorError_ExpectingAnyByte<R>)d)._b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((CursorError_ExpectingAnyByte<R>)d)._expected__sq;
      }
    }
    public R dtor_err {
      get {
        var d = this;
        return ((CursorError_OtherError<R>)d)._err;
      }
    }
    public abstract _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
    public static Dafny.ISequence<Dafny.Rune> _ToString(Std.JSON.Utils.Cursors._ICursorError<R> _this, Func<R, Dafny.ISequence<Dafny.Rune>> pr) {
      Std.JSON.Utils.Cursors._ICursorError<R> _source14 = _this;
      if (_source14.is_EOF) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Reached EOF");
      } else if (_source14.is_ExpectingByte) {
        byte _361___mcc_h0 = _source14.dtor_expected;
        short _362___mcc_h1 = _source14.dtor_b;
        short _363_b = _362___mcc_h1;
        byte _364_b0 = _361___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _365_c = (((_363_b) > ((short)(0))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_363_b)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("EOF")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expecting '"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_364_b0)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("', read ")), _365_c);
      } else if (_source14.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _366___mcc_h2 = _source14.dtor_expected__sq;
        short _367___mcc_h3 = _source14.dtor_b;
        short _368_b = _367___mcc_h3;
        Dafny.ISequence<byte> _369_bs0 = _366___mcc_h2;
        Dafny.ISequence<Dafny.Rune> _370_c = (((_368_b) > ((short)(0))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune((int)(_368_b)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("EOF")));
        Dafny.ISequence<Dafny.Rune> _371_c0s = ((System.Func<Dafny.ISequence<Dafny.Rune>>) (() => {
          BigInteger dim9 = new BigInteger((_369_bs0).Count);
          var arr9 = new Dafny.Rune[Dafny.Helpers.ToIntChecked(dim9, "array size exceeds memory limit")];
          for (int i9 = 0; i9 < dim9; i9++) {
            var _372_idx = (BigInteger) i9;
            arr9[(int)(_372_idx)] = new Dafny.Rune((int)((_369_bs0).Select(_372_idx)));
          }
          return Dafny.Sequence<Dafny.Rune>.FromArray(arr9);
        }))();
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expecting one of '"), _371_c0s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("', read ")), _370_c);
      } else {
        R _373___mcc_h4 = _source14.dtor_err;
        R _374_err = _373___mcc_h4;
        return Dafny.Helpers.Id<Func<R, Dafny.ISequence<Dafny.Rune>>>(pr)(_374_err);
      }
    }
  }
  public class CursorError_EOF<R> : CursorError<R> {
    public CursorError_EOF() : base() {
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_EOF<__R>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.CursorError_EOF<R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors.CursorError.EOF";
      return s;
    }
  }
  public class CursorError_ExpectingByte<R> : CursorError<R> {
    public readonly byte _expected;
    public readonly short _b;
    public CursorError_ExpectingByte(byte expected, short b) : base() {
      this._expected = expected;
      this._b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingByte<__R>(_expected, _b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.CursorError_ExpectingByte<R>;
      return oth != null && this._expected == oth._expected && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors.CursorError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class CursorError_ExpectingAnyByte<R> : CursorError<R> {
    public readonly Dafny.ISequence<byte> _expected__sq;
    public readonly short _b;
    public CursorError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) : base() {
      this._expected__sq = expected__sq;
      this._b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingAnyByte<__R>(_expected__sq, _b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.CursorError_ExpectingAnyByte<R>;
      return oth != null && object.Equals(this._expected__sq, oth._expected__sq) && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors.CursorError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class CursorError_OtherError<R> : CursorError<R> {
    public readonly R _err;
    public CursorError_OtherError(R err) : base() {
      this._err = err;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_OtherError<__R>(converter0(_err));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.CursorError_OtherError<R>;
      return oth != null && object.Equals(this._err, oth._err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors.CursorError.OtherError";
      s += "(";
      s += Dafny.Helpers.ToString(this._err);
      s += ")";
      return s;
    }
  }

  public interface _ICursor__ {
    bool is_Cursor { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_point { get; }
    uint dtor_end { get; }
    _ICursor__ DowncastClone();
    bool BOF_q { get; }
    bool EOF_q { get; }
    Dafny.ISequence<byte> Bytes();
    Std.JSON.Utils.Views.Core._IView__ Prefix();
    Std.JSON.Utils.Cursors._ICursor__ Suffix();
    Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> Split();
    uint PrefixLength();
    uint SuffixLength();
    uint Length();
    byte At(uint idx);
    byte SuffixAt(uint idx);
    short Peek();
    bool LookingAt(Dafny.Rune c);
    Std.JSON.Utils.Cursors._ICursor__ Skip(uint n);
    Std.JSON.Utils.Cursors._ICursor__ Unskip(uint n);
    Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> Get<__R>(__R err);
    Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertByte<__R>(byte b);
    Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset);
    Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertChar<__R>(Dafny.Rune c0);
    Std.JSON.Utils.Cursors._ICursor__ SkipByte();
    Std.JSON.Utils.Cursors._ICursor__ SkipIf(Func<byte, bool> p);
    Std.JSON.Utils.Cursors._ICursor__ SkipWhile(Func<byte, bool> p);
    Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, Std.JSON.Utils.Lexers.Core._ILexerResult<__A, __R>> step, __A st);
  }
  public class Cursor__ : _ICursor__ {
    public readonly Dafny.ISequence<byte> _s;
    public readonly uint _beg;
    public readonly uint _point;
    public readonly uint _end;
    public Cursor__(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      this._s = s;
      this._beg = beg;
      this._point = point;
      this._end = end;
    }
    public _ICursor__ DowncastClone() {
      if (this is _ICursor__ dt) { return dt; }
      return new Cursor__(_s, _beg, _point, _end);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Cursors.Cursor__;
      return oth != null && object.Equals(this._s, oth._s) && this._beg == oth._beg && this._point == oth._point && this._end == oth._end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._point));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Cursors.Cursor_.Cursor";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._point);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._end);
      ss += ")";
      return ss;
    }
    private static readonly Std.JSON.Utils.Cursors._ICursor__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0, 0);
    public static Std.JSON.Utils.Cursors._ICursor__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__>(Std.JSON.Utils.Cursors.Cursor__.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Cursors._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICursor__ create(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return new Cursor__(s, beg, point, end);
    }
    public static _ICursor__ create_Cursor(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return create(s, beg, point, end);
    }
    public bool is_Cursor { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this._s;
      }
    }
    public uint dtor_beg {
      get {
        return this._beg;
      }
    }
    public uint dtor_point {
      get {
        return this._point;
      }
    }
    public uint dtor_end {
      get {
        return this._end;
      }
    }
    public static Std.JSON.Utils.Cursors._ICursor__ OfView(Std.JSON.Utils.Views.Core._IView__ v) {
      return Std.JSON.Utils.Cursors.Cursor__.create((v).dtor_s, (v).dtor_beg, (v).dtor_beg, (v).dtor_end);
    }
    public static Std.JSON.Utils.Cursors._ICursor__ OfBytes(Dafny.ISequence<byte> bs) {
      return Std.JSON.Utils.Cursors.Cursor__.create(bs, 0U, 0U, (uint)(bs).LongCount);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public Std.JSON.Utils.Views.Core._IView__ Prefix() {
      return Std.JSON.Utils.Views.Core.View__.create((this).dtor_s, (this).dtor_beg, (this).dtor_point);
    }
    public Std.JSON.Utils.Cursors._ICursor__ Suffix() {
      Std.JSON.Utils.Cursors._ICursor__ _375_dt__update__tmp_h0 = this;
      uint _376_dt__update_hbeg_h0 = (this).dtor_point;
      return Std.JSON.Utils.Cursors.Cursor__.create((_375_dt__update__tmp_h0).dtor_s, _376_dt__update_hbeg_h0, (_375_dt__update__tmp_h0).dtor_point, (_375_dt__update__tmp_h0).dtor_end);
    }
    public Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> Split() {
      return Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core._IView__>.create((this).Prefix(), (this).Suffix());
    }
    public uint PrefixLength() {
      return ((this).dtor_point) - ((this).dtor_beg);
    }
    public uint SuffixLength() {
      return ((this).dtor_end) - ((this).dtor_point);
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public byte SuffixAt(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_point) + (idx));
    }
    public short Peek() {
      if ((this).EOF_q) {
        return (short)(-1);
      } else {
        return (short)((this).SuffixAt(0U));
      }
    }
    public bool LookingAt(Dafny.Rune c) {
      return ((this).Peek()) == ((short)((c).Value));
    }
    public Std.JSON.Utils.Cursors._ICursor__ Skip(uint n) {
      Std.JSON.Utils.Cursors._ICursor__ _377_dt__update__tmp_h0 = this;
      uint _378_dt__update_hpoint_h0 = ((this).dtor_point) + (n);
      return Std.JSON.Utils.Cursors.Cursor__.create((_377_dt__update__tmp_h0).dtor_s, (_377_dt__update__tmp_h0).dtor_beg, _378_dt__update_hpoint_h0, (_377_dt__update__tmp_h0).dtor_end);
    }
    public Std.JSON.Utils.Cursors._ICursor__ Unskip(uint n) {
      Std.JSON.Utils.Cursors._ICursor__ _379_dt__update__tmp_h0 = this;
      uint _380_dt__update_hpoint_h0 = ((this).dtor_point) - (n);
      return Std.JSON.Utils.Cursors.Cursor__.create((_379_dt__update__tmp_h0).dtor_s, (_379_dt__update__tmp_h0).dtor_beg, _380_dt__update_hpoint_h0, (_379_dt__update__tmp_h0).dtor_end);
    }
    public Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> Get<__R>(__R err) {
      if ((this).EOF_q) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_OtherError(err));
      } else {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Success((this).Skip(1U));
      }
    }
    public Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertByte<__R>(byte b) {
      short _381_nxt = (this).Peek();
      if ((_381_nxt) == ((short)(b))) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Success((this).Skip(1U));
      } else {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_ExpectingByte(b, _381_nxt));
      }
    }
    public Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset)
    {
      _ICursor__ _this = this;
    TAIL_CALL_START: ;
      if ((offset) == ((uint)(bs).LongCount)) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Success(_this);
      } else {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> _382_valueOrError0 = (_this).AssertByte<__R>((byte)((bs).Select(offset)));
        if ((_382_valueOrError0).IsFailure()) {
          return (_382_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ICursor__>();
        } else {
          Std.JSON.Utils.Cursors._ICursor__ _383_ps = (_382_valueOrError0).Extract();
          Std.JSON.Utils.Cursors._ICursor__ _in69 = _383_ps;
          Dafny.ISequence<byte> _in70 = bs;
          uint _in71 = (offset) + (1U);
          _this = _in69;
          ;
          bs = _in70;
          offset = _in71;
          goto TAIL_CALL_START;
        }
      }
    }
    public Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> AssertChar<__R>(Dafny.Rune c0) {
      return (this).AssertByte<__R>((byte)((c0).Value));
    }
    public Std.JSON.Utils.Cursors._ICursor__ SkipByte() {
      if ((this).EOF_q) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Std.JSON.Utils.Cursors._ICursor__ SkipIf(Func<byte, bool> p) {
      if (((this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((this).SuffixAt(0U))))) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Std.JSON.Utils.Cursors._ICursor__ SkipWhile(Func<byte, bool> p)
    {
      Std.JSON.Utils.Cursors._ICursor__ ps = Std.JSON.Utils.Cursors.Cursor.Default();
      uint _384_point_k;
      _384_point_k = (this).dtor_point;
      uint _385_end;
      _385_end = (this).dtor_end;
      while (((_384_point_k) < (_385_end)) && (Dafny.Helpers.Id<Func<byte, bool>>(p)(((this).dtor_s).Select(_384_point_k)))) {
        _384_point_k = (_384_point_k) + (1U);
      }
      ps = Std.JSON.Utils.Cursors.Cursor__.create((this).dtor_s, (this).dtor_beg, _384_point_k, (this).dtor_end);
      return ps;
      return ps;
    }
    public Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, Std.JSON.Utils.Lexers.Core._ILexerResult<__A, __R>> step, __A st)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>> pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.Default(Std.JSON.Utils.Cursors.Cursor.Default());
      uint _386_point_k;
      _386_point_k = (this).dtor_point;
      uint _387_end;
      _387_end = (this).dtor_end;
      __A _388_st_k;
      _388_st_k = st;
      while (true) {
        bool _389_eof;
        _389_eof = (_386_point_k) == (_387_end);
        short _390_minusone;
        _390_minusone = (short)(-1);
        short _391_c;
        _391_c = ((_389_eof) ? (_390_minusone) : ((short)(((this).dtor_s).Select(_386_point_k))));
        Std.JSON.Utils.Lexers.Core._ILexerResult<__A, __R> _source15 = Dafny.Helpers.Id<Func<__A, short, Std.JSON.Utils.Lexers.Core._ILexerResult<__A, __R>>>(step)(_388_st_k, _391_c);
        if (_source15.is_Accept) {
          pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Success(Std.JSON.Utils.Cursors.Cursor__.create((this).dtor_s, (this).dtor_beg, _386_point_k, (this).dtor_end));
          return pr;
        } else if (_source15.is_Reject) {
          __R _392___mcc_h0 = _source15.dtor_err;
          __R _393_err = _392___mcc_h0;
          pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_OtherError(_393_err));
          return pr;
        } else {
          __A _394___mcc_h1 = _source15.dtor_st;
          __A _395_st_k_k = _394___mcc_h1;
          if (_389_eof) {
            pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_EOF());
            return pr;
          } else {
            _388_st_k = _395_st_k_k;
            _386_point_k = (_386_point_k) + (1U);
          }
        }
      }
      return pr;
    }
    public bool BOF_q { get {
      return ((this).dtor_point) == ((this).dtor_beg);
    } }
    public bool EOF_q { get {
      return ((this).dtor_point) == ((this).dtor_end);
    } }
  }
} // end of namespace Std.JSON.Utils.Cursors
namespace Std.JSON.Utils.Parsers {

  public partial class __default {
    public static Std.JSON.Utils.Parsers._IParser__<__T, __R> ParserWitness<__T, __R>() {
      return Std.JSON.Utils.Parsers.Parser__<__T, __R>.create(((System.Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>)((_396___v9) => {
  return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_EOF());
})));
    }
    public static Std.JSON.Utils.Parsers._ISubParser__<__T, __R> SubParserWitness<__T, __R>() {
      return Std.JSON.Utils.Parsers.SubParser__<__T, __R>.create(((System.Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>)((_397_cs) => {
  return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<__R>.create_EOF());
})));
    }
  }

  public partial class Parser<T, R> {
    public static Std.JSON.Utils.Parsers._IParser__<T, R> Default() {
      return Std.JSON.Utils.Parsers.__default.ParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._IParser__<T, R>>(Std.JSON.Utils.Parsers.Parser<T, R>.Default());
    }
  }

  public interface _IParser__<T, out R> {
    bool is_Parser { get; }
    Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> dtor_fn { get; }
    _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class Parser__<T, R> : _IParser__<T, R> {
    public readonly Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> _fn;
    public Parser__(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      this._fn = fn;
    }
    public _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IParser__<__T, __R> dt) { return dt; }
      return new Parser__<__T, __R>((_fn).DowncastClone<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>, Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>(Dafny.Helpers.Id<Std.JSON.Utils.Cursors._ICursor__>, Dafny.Helpers.CastConverter<Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Parsers.Parser__<T, R>;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers.Parser_.Parser";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    public static Std.JSON.Utils.Parsers._IParser__<T, R> Default(T _default_T) {
      return create(((Std.JSON.Utils.Cursors._ICursor__ x0) => Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>.Default(Std.JSON.Utils.Cursors.Split<T>.Default(_default_T))));
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._IParser__<T, R>>(Std.JSON.Utils.Parsers.Parser__<T, R>.Default(_td_T.Default()));
    }
    public static _IParser__<T, R> create(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      return new Parser__<T, R>(fn);
    }
    public static _IParser__<T, R> create_Parser(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      return create(fn);
    }
    public bool is_Parser { get { return true; } }
    public Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> dtor_fn {
      get {
        return this._fn;
      }
    }
  }

  public interface _ISubParser__<T, out R> {
    bool is_SubParser { get; }
    Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> dtor_fn { get; }
    _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class SubParser__<T, R> : _ISubParser__<T, R> {
    public readonly Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> _fn;
    public SubParser__(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      this._fn = fn;
    }
    public _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ISubParser__<__T, __R> dt) { return dt; }
      return new SubParser__<__T, __R>((_fn).DowncastClone<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>, Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>(Dafny.Helpers.Id<Std.JSON.Utils.Cursors._ICursor__>, Dafny.Helpers.CastConverter<Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Utils.Parsers.SubParser__<T, R>;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers.SubParser_.SubParser";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    public static Std.JSON.Utils.Parsers._ISubParser__<T, R> Default() {
      return create(((Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>>)null));
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<T, R>>(Std.JSON.Utils.Parsers.SubParser__<T, R>.Default());
    }
    public static _ISubParser__<T, R> create(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      return new SubParser__<T, R>(fn);
    }
    public static _ISubParser__<T, R> create_SubParser(Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> fn) {
      return create(fn);
    }
    public bool is_SubParser { get { return true; } }
    public Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<T>, Std.JSON.Utils.Cursors._ICursorError<R>>> dtor_fn {
      get {
        return this._fn;
      }
    }
  }

  public partial class SubParser<T, R> {
    public static Std.JSON.Utils.Parsers._ISubParser__<T, R> Default() {
      return Std.JSON.Utils.Parsers.__default.SubParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<T, R>>(Std.JSON.Utils.Parsers.SubParser<T, R>.Default());
    }
  }
} // end of namespace Std.JSON.Utils.Parsers
namespace Std.JSON.Utils {

} // end of namespace Std.JSON.Utils
namespace Std.JSON.Grammar {

  public partial class __default {
    public static bool Blank_q(byte b) {
      return ((((b) == ((byte)(32))) || ((b) == ((byte)(9)))) || ((b) == ((byte)(10)))) || ((b) == ((byte)(13)));
    }
    public static bool Digit_q(byte b) {
      return (((byte)((new Dafny.Rune('0')).Value)) <= (b)) && ((b) <= ((byte)((new Dafny.Rune('9')).Value)));
    }
    public static Dafny.ISequence<byte> NULL { get {
      return Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('n')).Value), (byte)((new Dafny.Rune('u')).Value), (byte)((new Dafny.Rune('l')).Value), (byte)((new Dafny.Rune('l')).Value));
    } }
    public static Dafny.ISequence<byte> TRUE { get {
      return Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('t')).Value), (byte)((new Dafny.Rune('r')).Value), (byte)((new Dafny.Rune('u')).Value), (byte)((new Dafny.Rune('e')).Value));
    } }
    public static Dafny.ISequence<byte> FALSE { get {
      return Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('f')).Value), (byte)((new Dafny.Rune('a')).Value), (byte)((new Dafny.Rune('l')).Value), (byte)((new Dafny.Rune('s')).Value), (byte)((new Dafny.Rune('e')).Value));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ DOUBLEQUOTE { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('\"')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ PERIOD { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('.')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ E { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('e')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ COLON { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune(':')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ COMMA { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune(',')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ LBRACE { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('{')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ RBRACE { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('}')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ LBRACKET { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('[')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ RBRACKET { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune(']')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ MINUS { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('-')).Value)));
    } }
    public static Std.JSON.Utils.Views.Core._IView__ EMPTY { get {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    } }
  }

  public partial class jchar {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('b')).Value)));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jchar.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jquote {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.DOUBLEQUOTE;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jquote.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jperiod {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.PERIOD;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jperiod.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class je {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.E;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.je.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcolon {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.COLON;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jcolon.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcomma {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.COMMA;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jcomma.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbrace {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.LBRACE;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jlbrace.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbrace {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.RBRACE;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jrbrace.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbracket {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.LBRACKET;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jlbracket.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbracket {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.RBRACKET;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jrbracket.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jminus {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.MINUS;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jminus.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jsign {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Grammar.__default.EMPTY;
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jsign.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jblanks {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jblanks.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IStructural<out T> {
    bool is_Structural { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_before { get; }
    T dtor_t { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_after { get; }
    _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Structural<T> : _IStructural<T> {
    public readonly Std.JSON.Utils.Views.Core._IView__ _before;
    public readonly T _t;
    public readonly Std.JSON.Utils.Views.Core._IView__ _after;
    public Structural(Std.JSON.Utils.Views.Core._IView__ before, T t, Std.JSON.Utils.Views.Core._IView__ after) {
      this._before = before;
      this._t = t;
      this._after = after;
    }
    public _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IStructural<__T> dt) { return dt; }
      return new Structural<__T>(_before, converter0(_t), _after);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Structural<T>;
      return oth != null && object.Equals(this._before, oth._before) && object.Equals(this._t, oth._t) && object.Equals(this._after, oth._after);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._before));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._after));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Structural.Structural";
      s += "(";
      s += Dafny.Helpers.ToString(this._before);
      s += ", ";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._after);
      s += ")";
      return s;
    }
    public static Std.JSON.Grammar._IStructural<T> Default(T _default_T) {
      return create(Std.JSON.Grammar.jblanks.Default(), _default_T, Std.JSON.Grammar.jblanks.Default());
    }
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._IStructural<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Std.JSON.Grammar._IStructural<T>>(Std.JSON.Grammar.Structural<T>.Default(_td_T.Default()));
    }
    public static _IStructural<T> create(Std.JSON.Utils.Views.Core._IView__ before, T t, Std.JSON.Utils.Views.Core._IView__ after) {
      return new Structural<T>(before, t, after);
    }
    public static _IStructural<T> create_Structural(Std.JSON.Utils.Views.Core._IView__ before, T t, Std.JSON.Utils.Views.Core._IView__ after) {
      return create(before, t, after);
    }
    public bool is_Structural { get { return true; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_before {
      get {
        return this._before;
      }
    }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_after {
      get {
        return this._after;
      }
    }
  }

  public interface _IMaybe<out T> {
    bool is_Empty { get; }
    bool is_NonEmpty { get; }
    T dtor_t { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() {
    }
    public static Std.JSON.Grammar._IMaybe<T> Default() {
      return create_Empty();
    }
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.JSON.Grammar._IMaybe<T>>(Std.JSON.Grammar.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Empty() {
      return new Maybe_Empty<T>();
    }
    public static _IMaybe<T> create_NonEmpty(T t) {
      return new Maybe_NonEmpty<T>(t);
    }
    public bool is_Empty { get { return this is Maybe_Empty<T>; } }
    public bool is_NonEmpty { get { return this is Maybe_NonEmpty<T>; } }
    public T dtor_t {
      get {
        var d = this;
        return ((Maybe_NonEmpty<T>)d)._t;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Empty<T> : Maybe<T> {
    public Maybe_Empty() : base() {
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Empty<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Maybe_Empty<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Maybe.Empty";
      return s;
    }
  }
  public class Maybe_NonEmpty<T> : Maybe<T> {
    public readonly T _t;
    public Maybe_NonEmpty(T t) : base() {
      this._t = t;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_NonEmpty<__T>(converter0(_t));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Maybe_NonEmpty<T>;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Maybe.NonEmpty";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }

  public interface _ISuffixed<out T, out S> {
    bool is_Suffixed { get; }
    T dtor_t { get; }
    Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> dtor_suffix { get; }
    _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1);
  }
  public class Suffixed<T, S> : _ISuffixed<T, S> {
    public readonly T _t;
    public readonly Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> _suffix;
    public Suffixed(T t, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> suffix) {
      this._t = t;
      this._suffix = suffix;
    }
    public _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1) {
      if (this is _ISuffixed<__T, __S> dt) { return dt; }
      return new Suffixed<__T, __S>(converter0(_t), (_suffix).DowncastClone<Std.JSON.Grammar._IStructural<__S>>(Dafny.Helpers.CastConverter<Std.JSON.Grammar._IStructural<S>, Std.JSON.Grammar._IStructural<__S>>));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Suffixed<T, S>;
      return oth != null && object.Equals(this._t, oth._t) && object.Equals(this._suffix, oth._suffix);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._suffix));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Suffixed.Suffixed";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._suffix);
      s += ")";
      return s;
    }
    public static Std.JSON.Grammar._ISuffixed<T, S> Default(T _default_T) {
      return create(_default_T, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<S>>.Default());
    }
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._ISuffixed<T, S>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Std.JSON.Grammar._ISuffixed<T, S>>(Std.JSON.Grammar.Suffixed<T, S>.Default(_td_T.Default()));
    }
    public static _ISuffixed<T, S> create(T t, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> suffix) {
      return new Suffixed<T, S>(t, suffix);
    }
    public static _ISuffixed<T, S> create_Suffixed(T t, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> suffix) {
      return create(t, suffix);
    }
    public bool is_Suffixed { get { return true; } }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<S>> dtor_suffix {
      get {
        return this._suffix;
      }
    }
  }

  public partial class SuffixedSequence<D, S> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>>> _TypeDescriptor(Dafny.TypeDescriptor<D> _td_D, Dafny.TypeDescriptor<S> _td_S) {
      return new Dafny.TypeDescriptor<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>>>(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<D, S>>.Empty);
    }
  }

  public interface _IBracketed<out L, out D, out S, out R> {
    bool is_Bracketed { get; }
    Std.JSON.Grammar._IStructural<L> dtor_l { get; }
    Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> dtor_data { get; }
    Std.JSON.Grammar._IStructural<R> dtor_r { get; }
    _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3);
  }
  public class Bracketed<L, D, S, R> : _IBracketed<L, D, S, R> {
    public readonly Std.JSON.Grammar._IStructural<L> _l;
    public readonly Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> _data;
    public readonly Std.JSON.Grammar._IStructural<R> _r;
    public Bracketed(Std.JSON.Grammar._IStructural<L> l, Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> data, Std.JSON.Grammar._IStructural<R> r) {
      this._l = l;
      this._data = data;
      this._r = r;
    }
    public _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3) {
      if (this is _IBracketed<__L, __D, __S, __R> dt) { return dt; }
      return new Bracketed<__L, __D, __S, __R>((_l).DowncastClone<__L>(Dafny.Helpers.CastConverter<L, __L>), (_data).DowncastClone<Std.JSON.Grammar._ISuffixed<__D, __S>>(Dafny.Helpers.CastConverter<Std.JSON.Grammar._ISuffixed<D, S>, Std.JSON.Grammar._ISuffixed<__D, __S>>), (_r).DowncastClone<__R>(Dafny.Helpers.CastConverter<R, __R>));
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Bracketed<L, D, S, R>;
      return oth != null && object.Equals(this._l, oth._l) && object.Equals(this._data, oth._data) && object.Equals(this._r, oth._r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._l));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Bracketed.Bracketed";
      s += "(";
      s += Dafny.Helpers.ToString(this._l);
      s += ", ";
      s += Dafny.Helpers.ToString(this._data);
      s += ", ";
      s += Dafny.Helpers.ToString(this._r);
      s += ")";
      return s;
    }
    public static Std.JSON.Grammar._IBracketed<L, D, S, R> Default(L _default_L, R _default_R) {
      return create(Std.JSON.Grammar.Structural<L>.Default(_default_L), Dafny.Sequence<Std.JSON.Grammar._ISuffixed<D, S>>.Empty, Std.JSON.Grammar.Structural<R>.Default(_default_R));
    }
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._IBracketed<L, D, S, R>> _TypeDescriptor(Dafny.TypeDescriptor<L> _td_L, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Std.JSON.Grammar._IBracketed<L, D, S, R>>(Std.JSON.Grammar.Bracketed<L, D, S, R>.Default(_td_L.Default(), _td_R.Default()));
    }
    public static _IBracketed<L, D, S, R> create(Std.JSON.Grammar._IStructural<L> l, Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> data, Std.JSON.Grammar._IStructural<R> r) {
      return new Bracketed<L, D, S, R>(l, data, r);
    }
    public static _IBracketed<L, D, S, R> create_Bracketed(Std.JSON.Grammar._IStructural<L> l, Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> data, Std.JSON.Grammar._IStructural<R> r) {
      return create(l, data, r);
    }
    public bool is_Bracketed { get { return true; } }
    public Std.JSON.Grammar._IStructural<L> dtor_l {
      get {
        return this._l;
      }
    }
    public Dafny.ISequence<Std.JSON.Grammar._ISuffixed<D, S>> dtor_data {
      get {
        return this._data;
      }
    }
    public Std.JSON.Grammar._IStructural<R> dtor_r {
      get {
        return this._r;
      }
    }
  }

  public partial class jnull {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Std.JSON.Grammar.__default.NULL);
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jnull.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jbool {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Std.JSON.Grammar.__default.TRUE);
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jbool.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jdigits {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jdigits.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnum {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('0')).Value)));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jnum.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jint {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('0')).Value)));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jint.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jstr {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.jstr.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _Ijstring {
    bool is_JString { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_lq { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_contents { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_rq { get; }
    _Ijstring DowncastClone();
  }
  public class jstring : _Ijstring {
    public readonly Std.JSON.Utils.Views.Core._IView__ _lq;
    public readonly Std.JSON.Utils.Views.Core._IView__ _contents;
    public readonly Std.JSON.Utils.Views.Core._IView__ _rq;
    public jstring(Std.JSON.Utils.Views.Core._IView__ lq, Std.JSON.Utils.Views.Core._IView__ contents, Std.JSON.Utils.Views.Core._IView__ rq) {
      this._lq = lq;
      this._contents = contents;
      this._rq = rq;
    }
    public _Ijstring DowncastClone() {
      if (this is _Ijstring dt) { return dt; }
      return new jstring(_lq, _contents, _rq);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.jstring;
      return oth != null && object.Equals(this._lq, oth._lq) && object.Equals(this._contents, oth._contents) && object.Equals(this._rq, oth._rq);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._contents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rq));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.jstring.JString";
      s += "(";
      s += Dafny.Helpers.ToString(this._lq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._contents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rq);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Grammar._Ijstring theDefault = create(Std.JSON.Grammar.jquote.Default(), Std.JSON.Grammar.jstr.Default(), Std.JSON.Grammar.jquote.Default());
    public static Std.JSON.Grammar._Ijstring Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._Ijstring> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._Ijstring>(Std.JSON.Grammar.jstring.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._Ijstring> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijstring create(Std.JSON.Utils.Views.Core._IView__ lq, Std.JSON.Utils.Views.Core._IView__ contents, Std.JSON.Utils.Views.Core._IView__ rq) {
      return new jstring(lq, contents, rq);
    }
    public static _Ijstring create_JString(Std.JSON.Utils.Views.Core._IView__ lq, Std.JSON.Utils.Views.Core._IView__ contents, Std.JSON.Utils.Views.Core._IView__ rq) {
      return create(lq, contents, rq);
    }
    public bool is_JString { get { return true; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_lq {
      get {
        return this._lq;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_contents {
      get {
        return this._contents;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_rq {
      get {
        return this._rq;
      }
    }
  }

  public interface _IjKeyValue {
    bool is_KeyValue { get; }
    Std.JSON.Grammar._Ijstring dtor_k { get; }
    Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> dtor_colon { get; }
    Std.JSON.Grammar._IValue dtor_v { get; }
    _IjKeyValue DowncastClone();
  }
  public class jKeyValue : _IjKeyValue {
    public readonly Std.JSON.Grammar._Ijstring _k;
    public readonly Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> _colon;
    public readonly Std.JSON.Grammar._IValue _v;
    public jKeyValue(Std.JSON.Grammar._Ijstring k, Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> colon, Std.JSON.Grammar._IValue v) {
      this._k = k;
      this._colon = colon;
      this._v = v;
    }
    public _IjKeyValue DowncastClone() {
      if (this is _IjKeyValue dt) { return dt; }
      return new jKeyValue(_k, _colon, _v);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.jKeyValue;
      return oth != null && object.Equals(this._k, oth._k) && object.Equals(this._colon, oth._colon) && object.Equals(this._v, oth._v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._k));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._colon));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.jKeyValue.KeyValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._k);
      s += ", ";
      s += Dafny.Helpers.ToString(this._colon);
      s += ", ";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Grammar._IjKeyValue theDefault = create(Std.JSON.Grammar.jstring.Default(), Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core._IView__>.Default(Std.JSON.Grammar.jcolon.Default()), Std.JSON.Grammar.Value.Default());
    public static Std.JSON.Grammar._IjKeyValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._IjKeyValue> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._IjKeyValue>(Std.JSON.Grammar.jKeyValue.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._IjKeyValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IjKeyValue create(Std.JSON.Grammar._Ijstring k, Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> colon, Std.JSON.Grammar._IValue v) {
      return new jKeyValue(k, colon, v);
    }
    public static _IjKeyValue create_KeyValue(Std.JSON.Grammar._Ijstring k, Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> colon, Std.JSON.Grammar._IValue v) {
      return create(k, colon, v);
    }
    public bool is_KeyValue { get { return true; } }
    public Std.JSON.Grammar._Ijstring dtor_k {
      get {
        return this._k;
      }
    }
    public Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> dtor_colon {
      get {
        return this._colon;
      }
    }
    public Std.JSON.Grammar._IValue dtor_v {
      get {
        return this._v;
      }
    }
  }

  public interface _Ijfrac {
    bool is_JFrac { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_period { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_num { get; }
    _Ijfrac DowncastClone();
  }
  public class jfrac : _Ijfrac {
    public readonly Std.JSON.Utils.Views.Core._IView__ _period;
    public readonly Std.JSON.Utils.Views.Core._IView__ _num;
    public jfrac(Std.JSON.Utils.Views.Core._IView__ period, Std.JSON.Utils.Views.Core._IView__ num) {
      this._period = period;
      this._num = num;
    }
    public _Ijfrac DowncastClone() {
      if (this is _Ijfrac dt) { return dt; }
      return new jfrac(_period, _num);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.jfrac;
      return oth != null && object.Equals(this._period, oth._period) && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._period));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.jfrac.JFrac";
      s += "(";
      s += Dafny.Helpers.ToString(this._period);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Grammar._Ijfrac theDefault = create(Std.JSON.Grammar.jperiod.Default(), Std.JSON.Grammar.jnum.Default());
    public static Std.JSON.Grammar._Ijfrac Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._Ijfrac> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._Ijfrac>(Std.JSON.Grammar.jfrac.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._Ijfrac> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijfrac create(Std.JSON.Utils.Views.Core._IView__ period, Std.JSON.Utils.Views.Core._IView__ num) {
      return new jfrac(period, num);
    }
    public static _Ijfrac create_JFrac(Std.JSON.Utils.Views.Core._IView__ period, Std.JSON.Utils.Views.Core._IView__ num) {
      return create(period, num);
    }
    public bool is_JFrac { get { return true; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_period {
      get {
        return this._period;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_num {
      get {
        return this._num;
      }
    }
  }

  public interface _Ijexp {
    bool is_JExp { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_e { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_sign { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_num { get; }
    _Ijexp DowncastClone();
  }
  public class jexp : _Ijexp {
    public readonly Std.JSON.Utils.Views.Core._IView__ _e;
    public readonly Std.JSON.Utils.Views.Core._IView__ _sign;
    public readonly Std.JSON.Utils.Views.Core._IView__ _num;
    public jexp(Std.JSON.Utils.Views.Core._IView__ e, Std.JSON.Utils.Views.Core._IView__ sign, Std.JSON.Utils.Views.Core._IView__ num) {
      this._e = e;
      this._sign = sign;
      this._num = num;
    }
    public _Ijexp DowncastClone() {
      if (this is _Ijexp dt) { return dt; }
      return new jexp(_e, _sign, _num);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.jexp;
      return oth != null && object.Equals(this._e, oth._e) && object.Equals(this._sign, oth._sign) && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._e));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sign));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.jexp.JExp";
      s += "(";
      s += Dafny.Helpers.ToString(this._e);
      s += ", ";
      s += Dafny.Helpers.ToString(this._sign);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Grammar._Ijexp theDefault = create(Std.JSON.Grammar.je.Default(), Std.JSON.Grammar.jsign.Default(), Std.JSON.Grammar.jnum.Default());
    public static Std.JSON.Grammar._Ijexp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._Ijexp> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._Ijexp>(Std.JSON.Grammar.jexp.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._Ijexp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijexp create(Std.JSON.Utils.Views.Core._IView__ e, Std.JSON.Utils.Views.Core._IView__ sign, Std.JSON.Utils.Views.Core._IView__ num) {
      return new jexp(e, sign, num);
    }
    public static _Ijexp create_JExp(Std.JSON.Utils.Views.Core._IView__ e, Std.JSON.Utils.Views.Core._IView__ sign, Std.JSON.Utils.Views.Core._IView__ num) {
      return create(e, sign, num);
    }
    public bool is_JExp { get { return true; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_e {
      get {
        return this._e;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_sign {
      get {
        return this._sign;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_num {
      get {
        return this._num;
      }
    }
  }

  public interface _Ijnumber {
    bool is_JNumber { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_minus { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_num { get; }
    Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> dtor_frac { get; }
    Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> dtor_exp { get; }
    _Ijnumber DowncastClone();
  }
  public class jnumber : _Ijnumber {
    public readonly Std.JSON.Utils.Views.Core._IView__ _minus;
    public readonly Std.JSON.Utils.Views.Core._IView__ _num;
    public readonly Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> _frac;
    public readonly Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> _exp;
    public jnumber(Std.JSON.Utils.Views.Core._IView__ minus, Std.JSON.Utils.Views.Core._IView__ num, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> frac, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> exp) {
      this._minus = minus;
      this._num = num;
      this._frac = frac;
      this._exp = exp;
    }
    public _Ijnumber DowncastClone() {
      if (this is _Ijnumber dt) { return dt; }
      return new jnumber(_minus, _num, _frac, _exp);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.jnumber;
      return oth != null && object.Equals(this._minus, oth._minus) && object.Equals(this._num, oth._num) && object.Equals(this._frac, oth._frac) && object.Equals(this._exp, oth._exp);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._minus));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._frac));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._exp));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.jnumber.JNumber";
      s += "(";
      s += Dafny.Helpers.ToString(this._minus);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ", ";
      s += Dafny.Helpers.ToString(this._frac);
      s += ", ";
      s += Dafny.Helpers.ToString(this._exp);
      s += ")";
      return s;
    }
    private static readonly Std.JSON.Grammar._Ijnumber theDefault = create(Std.JSON.Grammar.jminus.Default(), Std.JSON.Grammar.jnum.Default(), Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijfrac>.Default(), Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijexp>.Default());
    public static Std.JSON.Grammar._Ijnumber Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._Ijnumber> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._Ijnumber>(Std.JSON.Grammar.jnumber.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._Ijnumber> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijnumber create(Std.JSON.Utils.Views.Core._IView__ minus, Std.JSON.Utils.Views.Core._IView__ num, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> frac, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> exp) {
      return new jnumber(minus, num, frac, exp);
    }
    public static _Ijnumber create_JNumber(Std.JSON.Utils.Views.Core._IView__ minus, Std.JSON.Utils.Views.Core._IView__ num, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> frac, Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> exp) {
      return create(minus, num, frac, exp);
    }
    public bool is_JNumber { get { return true; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_minus {
      get {
        return this._minus;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_num {
      get {
        return this._num;
      }
    }
    public Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> dtor_frac {
      get {
        return this._frac;
      }
    }
    public Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> dtor_exp {
      get {
        return this._exp;
      }
    }
  }

  public interface _IValue {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_n { get; }
    Std.JSON.Utils.Views.Core._IView__ dtor_b { get; }
    Std.JSON.Grammar._Ijstring dtor_str { get; }
    Std.JSON.Grammar._Ijnumber dtor_num { get; }
    Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> dtor_obj { get; }
    Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> dtor_arr { get; }
    _IValue DowncastClone();
  }
  public abstract class Value : _IValue {
    public Value() {
    }
    private static readonly Std.JSON.Grammar._IValue theDefault = create_Null(Std.JSON.Grammar.jnull.Default());
    public static Std.JSON.Grammar._IValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Grammar._IValue> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Grammar._IValue>(Std.JSON.Grammar.Value.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Grammar._IValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IValue create_Null(Std.JSON.Utils.Views.Core._IView__ n) {
      return new Value_Null(n);
    }
    public static _IValue create_Bool(Std.JSON.Utils.Views.Core._IView__ b) {
      return new Value_Bool(b);
    }
    public static _IValue create_String(Std.JSON.Grammar._Ijstring str) {
      return new Value_String(str);
    }
    public static _IValue create_Number(Std.JSON.Grammar._Ijnumber num) {
      return new Value_Number(num);
    }
    public static _IValue create_Object(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj) {
      return new Value_Object(obj);
    }
    public static _IValue create_Array(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr) {
      return new Value_Array(arr);
    }
    public bool is_Null { get { return this is Value_Null; } }
    public bool is_Bool { get { return this is Value_Bool; } }
    public bool is_String { get { return this is Value_String; } }
    public bool is_Number { get { return this is Value_Number; } }
    public bool is_Object { get { return this is Value_Object; } }
    public bool is_Array { get { return this is Value_Array; } }
    public Std.JSON.Utils.Views.Core._IView__ dtor_n {
      get {
        var d = this;
        return ((Value_Null)d)._n;
      }
    }
    public Std.JSON.Utils.Views.Core._IView__ dtor_b {
      get {
        var d = this;
        return ((Value_Bool)d)._b;
      }
    }
    public Std.JSON.Grammar._Ijstring dtor_str {
      get {
        var d = this;
        return ((Value_String)d)._str;
      }
    }
    public Std.JSON.Grammar._Ijnumber dtor_num {
      get {
        var d = this;
        return ((Value_Number)d)._num;
      }
    }
    public Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> dtor_obj {
      get {
        var d = this;
        return ((Value_Object)d)._obj;
      }
    }
    public Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> dtor_arr {
      get {
        var d = this;
        return ((Value_Array)d)._arr;
      }
    }
    public abstract _IValue DowncastClone();
  }
  public class Value_Null : Value {
    public readonly Std.JSON.Utils.Views.Core._IView__ _n;
    public Value_Null(Std.JSON.Utils.Views.Core._IView__ n) : base() {
      this._n = n;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Null(_n);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_Null;
      return oth != null && object.Equals(this._n, oth._n);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this._n);
      s += ")";
      return s;
    }
  }
  public class Value_Bool : Value {
    public readonly Std.JSON.Utils.Views.Core._IView__ _b;
    public Value_Bool(Std.JSON.Utils.Views.Core._IView__ b) : base() {
      this._b = b;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Bool(_b);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_Bool;
      return oth != null && object.Equals(this._b, oth._b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class Value_String : Value {
    public readonly Std.JSON.Grammar._Ijstring _str;
    public Value_String(Std.JSON.Grammar._Ijstring str) : base() {
      this._str = str;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_String(_str);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_String;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.String";
      s += "(";
      s += Dafny.Helpers.ToString(this._str);
      s += ")";
      return s;
    }
  }
  public class Value_Number : Value {
    public readonly Std.JSON.Grammar._Ijnumber _num;
    public Value_Number(Std.JSON.Grammar._Ijnumber num) : base() {
      this._num = num;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Number(_num);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_Number;
      return oth != null && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
  }
  public class Value_Object : Value {
    public readonly Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _obj;
    public Value_Object(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj) : base() {
      this._obj = obj;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Object(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_Object;
      return oth != null && object.Equals(this._obj, oth._obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }
  public class Value_Array : Value {
    public readonly Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _arr;
    public Value_Array(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr) : base() {
      this._arr = arr;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Array(_arr);
    }
    public override bool Equals(object other) {
      var oth = other as Std.JSON.Grammar.Value_Array;
      return oth != null && object.Equals(this._arr, oth._arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Grammar.Value.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._arr);
      s += ")";
      return s;
    }
  }
} // end of namespace Std.JSON.Grammar
namespace Std.JSON.ByteStrConversion {

  public partial class __default {
    public static BigInteger BASE() {
      return Std.JSON.ByteStrConversion.__default.@base;
    }
    public static Dafny.ISequence<byte> OfDigits(Dafny.ISequence<BigInteger> digits) {
      Dafny.ISequence<byte> _398___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _398___accumulator);
      } else {
        _398___accumulator = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements((Std.JSON.ByteStrConversion.__default.chars).Select((digits).Select(BigInteger.Zero))), _398___accumulator);
        Dafny.ISequence<BigInteger> _in72 = (digits).Drop(BigInteger.One);
        digits = _in72;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> OfNat(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<byte>.FromElements((Std.JSON.ByteStrConversion.__default.chars).Select(BigInteger.Zero));
      } else {
        return Std.JSON.ByteStrConversion.__default.OfDigits(Std.JSON.ByteStrConversion.__default.FromNat(n));
      }
    }
    public static bool OfNumberStr(Dafny.ISequence<byte> str, byte minus)
    {
      return !(!(str).Equals(Dafny.Sequence<byte>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.JSON.ByteStrConversion.__default.chars).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<byte>, bool>>((_399_str) => Dafny.Helpers.Quantifier<byte>(((_399_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_5) => {
        byte _400_c = (byte)_forall_var_5;
        return !(((_399_str).Drop(BigInteger.One)).Contains(_400_c)) || ((Std.JSON.ByteStrConversion.__default.chars).Contains(_400_c));
      }))))(str)));
    }
    public static bool ToNumberStr(Dafny.ISequence<byte> str, byte minus)
    {
      return !(!(str).Equals(Dafny.Sequence<byte>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.JSON.ByteStrConversion.__default.charToDigit).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<byte>, bool>>((_401_str) => Dafny.Helpers.Quantifier<byte>(((_401_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_6) => {
        byte _402_c = (byte)_forall_var_6;
        return !(((_401_str).Drop(BigInteger.One)).Contains(_402_c)) || ((Std.JSON.ByteStrConversion.__default.charToDigit).Contains(_402_c));
      }))))(str)));
    }
    public static Dafny.ISequence<byte> OfInt(BigInteger n, byte minus)
    {
      if ((n).Sign != -1) {
        return Std.JSON.ByteStrConversion.__default.OfNat(n);
      } else {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(minus), Std.JSON.ByteStrConversion.__default.OfNat((BigInteger.Zero) - (n)));
      }
    }
    public static BigInteger ToNat(Dafny.ISequence<byte> str) {
      if ((str).Equals(Dafny.Sequence<byte>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((Std.JSON.ByteStrConversion.__default.ToNat((str).Take((new BigInteger((str).Count)) - (BigInteger.One)))) * (Std.JSON.ByteStrConversion.__default.@base)) + (Dafny.Map<byte, BigInteger>.Select(Std.JSON.ByteStrConversion.__default.charToDigit,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt(Dafny.ISequence<byte> str, byte minus)
    {
      if (Dafny.Sequence<byte>.IsPrefixOf(Dafny.Sequence<byte>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (Std.JSON.ByteStrConversion.__default.ToNat((str).Drop(BigInteger.One)));
      } else {
        return Std.JSON.ByteStrConversion.__default.ToNat(str);
      }
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Std.JSON.ByteStrConversion.__default.ToNatRight(Std.Collections.Seq.__default.DropFirst<BigInteger>(xs))) * (Std.JSON.ByteStrConversion.__default.BASE())) + (Std.Collections.Seq.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _403___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_403___accumulator);
      } else {
        _403___accumulator = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) * (Std.Arithmetic.Power.__default.Pow(Std.JSON.ByteStrConversion.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_403___accumulator);
        Dafny.ISequence<BigInteger> _in73 = Std.Collections.Seq.__default.DropLast<BigInteger>(xs);
        xs = _in73;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _404___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_404___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _404___accumulator = Dafny.Sequence<BigInteger>.Concat(_404___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Std.JSON.ByteStrConversion.__default.BASE())));
        BigInteger _in74 = Dafny.Helpers.EuclideanDivision(n, Std.JSON.ByteStrConversion.__default.BASE());
        n = _in74;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in75 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in76 = n;
        xs = _in75;
        n = _in76;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _405_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Std.JSON.ByteStrConversion.__default.SeqExtend(xs, _405_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Std.JSON.ByteStrConversion.__default.SeqExtend(Std.JSON.ByteStrConversion.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _406_xs = Std.JSON.ByteStrConversion.__default.FromNatWithLen(BigInteger.Zero, len);
      return _406_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs9 = Std.JSON.ByteStrConversion.__default.SeqAdd(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _407_zs_k = _let_tmp_rhs9.dtor__0;
        BigInteger _408_cin = _let_tmp_rhs9.dtor__1;
        BigInteger _409_sum = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) + (Std.Collections.Seq.__default.Last<BigInteger>(ys))) + (_408_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs10 = (((_409_sum) < (Std.JSON.ByteStrConversion.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_409_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_409_sum) - (Std.JSON.ByteStrConversion.__default.BASE()), BigInteger.One)));
        BigInteger _410_sum__out = _let_tmp_rhs10.dtor__0;
        BigInteger _411_cout = _let_tmp_rhs10.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_407_zs_k, Dafny.Sequence<BigInteger>.FromElements(_410_sum__out)), _411_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs11 = Std.JSON.ByteStrConversion.__default.SeqSub(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _412_zs = _let_tmp_rhs11.dtor__0;
        BigInteger _413_cin = _let_tmp_rhs11.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs12 = (((Std.Collections.Seq.__default.Last<BigInteger>(xs)) >= ((Std.Collections.Seq.__default.Last<BigInteger>(ys)) + (_413_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Std.Collections.Seq.__default.Last<BigInteger>(xs)) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_413_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Std.JSON.ByteStrConversion.__default.BASE()) + (Std.Collections.Seq.__default.Last<BigInteger>(xs))) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_413_cin), BigInteger.One)));
        BigInteger _414_diff__out = _let_tmp_rhs12.dtor__0;
        BigInteger _415_cout = _let_tmp_rhs12.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_412_zs, Dafny.Sequence<BigInteger>.FromElements(_414_diff__out)), _415_cout);
      }
    }
    public static Dafny.ISequence<byte> chars { get {
      return Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('0')).Value), (byte)((new Dafny.Rune('1')).Value), (byte)((new Dafny.Rune('2')).Value), (byte)((new Dafny.Rune('3')).Value), (byte)((new Dafny.Rune('4')).Value), (byte)((new Dafny.Rune('5')).Value), (byte)((new Dafny.Rune('6')).Value), (byte)((new Dafny.Rune('7')).Value), (byte)((new Dafny.Rune('8')).Value), (byte)((new Dafny.Rune('9')).Value));
    } }
    public static BigInteger @base { get {
      return new BigInteger((Std.JSON.ByteStrConversion.__default.chars).Count);
    } }
    public static Dafny.IMap<byte,BigInteger> charToDigit { get {
      return Dafny.Map<byte, BigInteger>.FromElements(new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('0')).Value), BigInteger.Zero), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('1')).Value), BigInteger.One), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('2')).Value), new BigInteger(2)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('3')).Value), new BigInteger(3)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('4')).Value), new BigInteger(4)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('5')).Value), new BigInteger(5)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('6')).Value), new BigInteger(6)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('7')).Value), new BigInteger(7)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('8')).Value), new BigInteger(8)), new Dafny.Pair<byte, BigInteger>((byte)((new Dafny.Rune('9')).Value), new BigInteger(9)));
    } }
  }

  public partial class CharSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class digit {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.ByteStrConversion
namespace Std.JSON.Serializer {

  public partial class __default {
    public static Std.JSON.Utils.Views.Core._IView__ Bool(bool b) {
      return Std.JSON.Utils.Views.Core.View__.OfBytes(((b) ? (Std.JSON.Grammar.__default.TRUE) : (Std.JSON.Grammar.__default.FALSE)));
    }
    public static Std.Wrappers._IOutcome<Std.JSON.Errors._ISerializationError> CheckLength<__T>(Dafny.ISequence<__T> s, Std.JSON.Errors._ISerializationError err)
    {
      return Std.Wrappers.Outcome<Std.JSON.Errors._ISerializationError>.Need((new BigInteger((s).Count)) < (Std.BoundedInts.__default.TWO__TO__THE__32), err);
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._Ijstring, Std.JSON.Errors._ISerializationError> String(Dafny.ISequence<Dafny.Rune> str) {
      Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> _416_valueOrError0 = Std.JSON.Spec.__default.EscapeToUTF8(str, BigInteger.Zero);
      if ((_416_valueOrError0).IsFailure()) {
        return (_416_valueOrError0).PropagateFailure<Std.JSON.Grammar._Ijstring>();
      } else {
        Dafny.ISequence<byte> _417_bs = (_416_valueOrError0).Extract();
        Std.Wrappers._IOutcome<Std.JSON.Errors._ISerializationError> _418_o = Std.JSON.Serializer.__default.CheckLength<byte>(_417_bs, Std.JSON.Errors.SerializationError.create_StringTooLong(str));
        if ((_418_o).is_Pass) {
          return Std.Wrappers.Result<Std.JSON.Grammar._Ijstring, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.jstring.create(Std.JSON.Grammar.__default.DOUBLEQUOTE, Std.JSON.Utils.Views.Core.View__.OfBytes(_417_bs), Std.JSON.Grammar.__default.DOUBLEQUOTE));
        } else {
          return Std.Wrappers.Result<Std.JSON.Grammar._Ijstring, Std.JSON.Errors._ISerializationError>.create_Failure((_418_o).dtor_error);
        }
      }
    }
    public static Std.JSON.Utils.Views.Core._IView__ Sign(BigInteger n) {
      return Std.JSON.Utils.Views.Core.View__.OfBytes((((n).Sign == -1) ? (Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('-')).Value))) : (Dafny.Sequence<byte>.FromElements())));
    }
    public static Dafny.ISequence<byte> Int_k(BigInteger n) {
      return Std.JSON.ByteStrConversion.__default.OfInt(n, Std.JSON.Serializer.__default.MINUS);
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError> Int(BigInteger n) {
      Dafny.ISequence<byte> _419_bs = Std.JSON.Serializer.__default.Int_k(n);
      Std.Wrappers._IOutcome<Std.JSON.Errors._ISerializationError> _420_o = Std.JSON.Serializer.__default.CheckLength<byte>(_419_bs, Std.JSON.Errors.SerializationError.create_IntTooLarge(n));
      if ((_420_o).is_Pass) {
        return Std.Wrappers.Result<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Utils.Views.Core.View__.OfBytes(_419_bs));
      } else {
        return Std.Wrappers.Result<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError>.create_Failure((_420_o).dtor_error);
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._Ijnumber, Std.JSON.Errors._ISerializationError> Number(Std.JSON.Values._IDecimal dec) {
      var _pat_let_tv2 = dec;
      var _pat_let_tv3 = dec;
      Std.JSON.Utils.Views.Core._IView__ _421_minus = Std.JSON.Serializer.__default.Sign((dec).dtor_n);
      Std.Wrappers._IResult<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError> _422_valueOrError0 = Std.JSON.Serializer.__default.Int(Std.Math.__default.Abs((dec).dtor_n));
      if ((_422_valueOrError0).IsFailure()) {
        return (_422_valueOrError0).PropagateFailure<Std.JSON.Grammar._Ijnumber>();
      } else {
        Std.JSON.Utils.Views.Core._IView__ _423_num = (_422_valueOrError0).Extract();
        Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> _424_frac = Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijfrac>.create_Empty();
        Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError> _425_valueOrError1 = ((((dec).dtor_e10).Sign == 0) ? (Std.Wrappers.Result<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijexp>.create_Empty())) : (Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)((new Dafny.Rune('e')).Value))), _pat_let2_0 => Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(_pat_let2_0, _426_e => Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(Std.JSON.Serializer.__default.Sign((_pat_let_tv2).dtor_e10), _pat_let3_0 => Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(_pat_let3_0, _427_sign => Dafny.Helpers.Let<Std.Wrappers._IResult<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError>, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(Std.JSON.Serializer.__default.Int(Std.Math.__default.Abs((_pat_let_tv3).dtor_e10)), _pat_let4_0 => Dafny.Helpers.Let<Std.Wrappers._IResult<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._ISerializationError>, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(_pat_let4_0, _428_valueOrError2 => (((_428_valueOrError2).IsFailure()) ? ((_428_valueOrError2).PropagateFailure<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>()) : (Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>((_428_valueOrError2).Extract(), _pat_let5_0 => Dafny.Helpers.Let<Std.JSON.Utils.Views.Core._IView__, Std.Wrappers._IResult<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>>(_pat_let5_0, _429_num => Std.Wrappers.Result<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijexp>.create_NonEmpty(Std.JSON.Grammar.jexp.create(_426_e, _427_sign, _429_num)))))))))))))));
        if ((_425_valueOrError1).IsFailure()) {
          return (_425_valueOrError1).PropagateFailure<Std.JSON.Grammar._Ijnumber>();
        } else {
          Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> _430_exp = (_425_valueOrError1).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._Ijnumber, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.jnumber.create(_421_minus, _423_num, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijfrac>.create_Empty(), _430_exp));
        }
      }
    }
    public static Std.JSON.Grammar._IStructural<__T> MkStructural<__T>(__T v) {
      return Std.JSON.Grammar.Structural<__T>.create(Std.JSON.Grammar.__default.EMPTY, v, Std.JSON.Grammar.__default.EMPTY);
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IjKeyValue, Std.JSON.Errors._ISerializationError> KeyValue(_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON> kv) {
      Std.Wrappers._IResult<Std.JSON.Grammar._Ijstring, Std.JSON.Errors._ISerializationError> _431_valueOrError0 = Std.JSON.Serializer.__default.String((kv).dtor__0);
      if ((_431_valueOrError0).IsFailure()) {
        return (_431_valueOrError0).PropagateFailure<Std.JSON.Grammar._IjKeyValue>();
      } else {
        Std.JSON.Grammar._Ijstring _432_k = (_431_valueOrError0).Extract();
        Std.Wrappers._IResult<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError> _433_valueOrError1 = Std.JSON.Serializer.__default.Value((kv).dtor__1);
        if ((_433_valueOrError1).IsFailure()) {
          return (_433_valueOrError1).PropagateFailure<Std.JSON.Grammar._IjKeyValue>();
        } else {
          Std.JSON.Grammar._IValue _434_v = (_433_valueOrError1).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._IjKeyValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.jKeyValue.create(_432_k, Std.JSON.Serializer.__default.COLON, _434_v));
        }
      }
    }
    public static Dafny.ISequence<Std.JSON.Grammar._ISuffixed<__D, __S>> MkSuffixedSequence<__D, __S>(Dafny.ISequence<__D> ds, Std.JSON.Grammar._IStructural<__S> suffix, BigInteger start)
    {
      Dafny.ISequence<Std.JSON.Grammar._ISuffixed<__D, __S>> _435___accumulator = Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.FromElements();
    TAIL_CALL_START: ;
      if ((start) >= (new BigInteger((ds).Count))) {
        return Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.Concat(_435___accumulator, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.FromElements());
      } else if ((start) == ((new BigInteger((ds).Count)) - (BigInteger.One))) {
        return Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.Concat(_435___accumulator, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.FromElements(Std.JSON.Grammar.Suffixed<__D, __S>.create((ds).Select(start), Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<__S>>.create_Empty())));
      } else {
        _435___accumulator = Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.Concat(_435___accumulator, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<__D, __S>>.FromElements(Std.JSON.Grammar.Suffixed<__D, __S>.create((ds).Select(start), Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<__S>>.create_NonEmpty(suffix))));
        Dafny.ISequence<__D> _in77 = ds;
        Std.JSON.Grammar._IStructural<__S> _in78 = suffix;
        BigInteger _in79 = (start) + (BigInteger.One);
        ds = _in77;
        suffix = _in78;
        start = _in79;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError> Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> obj) {
      Std.Wrappers._IResult<Dafny.ISequence<Std.JSON.Grammar._IjKeyValue>, Std.JSON.Errors._ISerializationError> _436_valueOrError0 = Std.Collections.Seq.__default.MapWithResult<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Grammar._IjKeyValue, Std.JSON.Errors._ISerializationError>(Dafny.Helpers.Id<Func<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>>, Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.Wrappers._IResult<Std.JSON.Grammar._IjKeyValue, Std.JSON.Errors._ISerializationError>>>>((_437_obj) => ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.Wrappers._IResult<Std.JSON.Grammar._IjKeyValue, Std.JSON.Errors._ISerializationError>>)((_438_v) => {
        return Std.JSON.Serializer.__default.KeyValue(_438_v);
      })))(obj), obj);
      if ((_436_valueOrError0).IsFailure()) {
        return (_436_valueOrError0).PropagateFailure<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Dafny.ISequence<Std.JSON.Grammar._IjKeyValue> _439_items = (_436_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>.create(Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.LBRACE), Std.JSON.Serializer.__default.MkSuffixedSequence<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>(_439_items, Std.JSON.Serializer.__default.COMMA, BigInteger.Zero), Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.RBRACE)));
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError> Array(Dafny.ISequence<Std.JSON.Values._IJSON> arr) {
      Std.Wrappers._IResult<Dafny.ISequence<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError> _440_valueOrError0 = Std.Collections.Seq.__default.MapWithResult<Std.JSON.Values._IJSON, Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>(Dafny.Helpers.Id<Func<Dafny.ISequence<Std.JSON.Values._IJSON>, Func<Std.JSON.Values._IJSON, Std.Wrappers._IResult<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>>>>((_441_arr) => ((System.Func<Std.JSON.Values._IJSON, Std.Wrappers._IResult<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>>)((_442_v) => {
        return Std.JSON.Serializer.__default.Value(_442_v);
      })))(arr), arr);
      if ((_440_valueOrError0).IsFailure()) {
        return (_440_valueOrError0).PropagateFailure<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Dafny.ISequence<Std.JSON.Grammar._IValue> _443_items = (_440_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>.create(Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.LBRACKET), Std.JSON.Serializer.__default.MkSuffixedSequence<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>(_443_items, Std.JSON.Serializer.__default.COMMA, BigInteger.Zero), Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.RBRACKET)));
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError> Value(Std.JSON.Values._IJSON js) {
      Std.JSON.Values._IJSON _source16 = js;
      if (_source16.is_Null) {
        return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_Null(Std.JSON.Utils.Views.Core.View__.OfBytes(Std.JSON.Grammar.__default.NULL)));
      } else if (_source16.is_Bool) {
        bool _444___mcc_h0 = _source16.dtor_b;
        bool _445_b = _444___mcc_h0;
        return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_Bool(Std.JSON.Serializer.__default.Bool(_445_b)));
      } else if (_source16.is_String) {
        Dafny.ISequence<Dafny.Rune> _446___mcc_h1 = _source16.dtor_str;
        Dafny.ISequence<Dafny.Rune> _447_str = _446___mcc_h1;
        Std.Wrappers._IResult<Std.JSON.Grammar._Ijstring, Std.JSON.Errors._ISerializationError> _448_valueOrError0 = Std.JSON.Serializer.__default.String(_447_str);
        if ((_448_valueOrError0).IsFailure()) {
          return (_448_valueOrError0).PropagateFailure<Std.JSON.Grammar._IValue>();
        } else {
          Std.JSON.Grammar._Ijstring _449_s = (_448_valueOrError0).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_String(_449_s));
        }
      } else if (_source16.is_Number) {
        Std.JSON.Values._IDecimal _450___mcc_h2 = _source16.dtor_num;
        Std.JSON.Values._IDecimal _451_dec = _450___mcc_h2;
        Std.Wrappers._IResult<Std.JSON.Grammar._Ijnumber, Std.JSON.Errors._ISerializationError> _452_valueOrError1 = Std.JSON.Serializer.__default.Number(_451_dec);
        if ((_452_valueOrError1).IsFailure()) {
          return (_452_valueOrError1).PropagateFailure<Std.JSON.Grammar._IValue>();
        } else {
          Std.JSON.Grammar._Ijnumber _453_n = (_452_valueOrError1).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_Number(_453_n));
        }
      } else if (_source16.is_Object) {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _454___mcc_h3 = _source16.dtor_obj;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _455_obj = _454___mcc_h3;
        Std.Wrappers._IResult<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError> _456_valueOrError2 = Std.JSON.Serializer.__default.Object(_455_obj);
        if ((_456_valueOrError2).IsFailure()) {
          return (_456_valueOrError2).PropagateFailure<Std.JSON.Grammar._IValue>();
        } else {
          Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _457_o = (_456_valueOrError2).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_Object(_457_o));
        }
      } else {
        Dafny.ISequence<Std.JSON.Values._IJSON> _458___mcc_h4 = _source16.dtor_arr;
        Dafny.ISequence<Std.JSON.Values._IJSON> _459_arr = _458___mcc_h4;
        Std.Wrappers._IResult<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Errors._ISerializationError> _460_valueOrError3 = Std.JSON.Serializer.__default.Array(_459_arr);
        if ((_460_valueOrError3).IsFailure()) {
          return (_460_valueOrError3).PropagateFailure<Std.JSON.Grammar._IValue>();
        } else {
          Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _461_a = (_460_valueOrError3).Extract();
          return Std.Wrappers.Result<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Grammar.Value.create_Array(_461_a));
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError> JSON(Std.JSON.Values._IJSON js) {
      Std.Wrappers._IResult<Std.JSON.Grammar._IValue, Std.JSON.Errors._ISerializationError> _462_valueOrError0 = Std.JSON.Serializer.__default.Value(js);
      if ((_462_valueOrError0).IsFailure()) {
        return (_462_valueOrError0).PropagateFailure<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>();
      } else {
        Std.JSON.Grammar._IValue _463_val = (_462_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError>.create_Success(Std.JSON.Serializer.__default.MkStructural<Std.JSON.Grammar._IValue>(_463_val));
      }
    }
    public static Dafny.ISequence<byte> DIGITS { get {
      return Std.JSON.ByteStrConversion.__default.chars;
    } }
    public static byte MINUS { get {
      return (byte)((new Dafny.Rune('-')).Value);
    } }
    public static Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> COLON { get {
      return Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.COLON);
    } }
    public static Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> COMMA { get {
      return Std.JSON.Serializer.__default.MkStructural<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.Grammar.__default.COMMA);
    } }
  }

  public partial class bytes32 {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class string32 {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.Serializer
namespace Std.JSON.Deserializer.Uint16StrConversion {

  public partial class __default {
    public static BigInteger BASE() {
      return Std.JSON.Deserializer.Uint16StrConversion.__default.@base;
    }
    public static Dafny.ISequence<ushort> OfDigits(Dafny.ISequence<BigInteger> digits) {
      Dafny.ISequence<ushort> _464___accumulator = Dafny.Sequence<ushort>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<ushort>.Concat(Dafny.Sequence<ushort>.FromElements(), _464___accumulator);
      } else {
        _464___accumulator = Dafny.Sequence<ushort>.Concat(Dafny.Sequence<ushort>.FromElements((Std.JSON.Deserializer.Uint16StrConversion.__default.chars).Select((digits).Select(BigInteger.Zero))), _464___accumulator);
        Dafny.ISequence<BigInteger> _in80 = (digits).Drop(BigInteger.One);
        digits = _in80;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ushort> OfNat(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<ushort>.FromElements((Std.JSON.Deserializer.Uint16StrConversion.__default.chars).Select(BigInteger.Zero));
      } else {
        return Std.JSON.Deserializer.Uint16StrConversion.__default.OfDigits(Std.JSON.Deserializer.Uint16StrConversion.__default.FromNat(n));
      }
    }
    public static bool OfNumberStr(Dafny.ISequence<ushort> str, ushort minus)
    {
      return !(!(str).Equals(Dafny.Sequence<ushort>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.JSON.Deserializer.Uint16StrConversion.__default.chars).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<ushort>, bool>>((_465_str) => Dafny.Helpers.Quantifier<ushort>(((_465_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_7) => {
        ushort _466_c = (ushort)_forall_var_7;
        return !(((_465_str).Drop(BigInteger.One)).Contains(_466_c)) || ((Std.JSON.Deserializer.Uint16StrConversion.__default.chars).Contains(_466_c));
      }))))(str)));
    }
    public static bool ToNumberStr(Dafny.ISequence<ushort> str, ushort minus)
    {
      return !(!(str).Equals(Dafny.Sequence<ushort>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || ((Std.JSON.Deserializer.Uint16StrConversion.__default.charToDigit).Contains((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<ushort>, bool>>((_467_str) => Dafny.Helpers.Quantifier<ushort>(((_467_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_8) => {
        ushort _468_c = (ushort)_forall_var_8;
        return !(((_467_str).Drop(BigInteger.One)).Contains(_468_c)) || ((Std.JSON.Deserializer.Uint16StrConversion.__default.charToDigit).Contains(_468_c));
      }))))(str)));
    }
    public static Dafny.ISequence<ushort> OfInt(BigInteger n, ushort minus)
    {
      if ((n).Sign != -1) {
        return Std.JSON.Deserializer.Uint16StrConversion.__default.OfNat(n);
      } else {
        return Dafny.Sequence<ushort>.Concat(Dafny.Sequence<ushort>.FromElements(minus), Std.JSON.Deserializer.Uint16StrConversion.__default.OfNat((BigInteger.Zero) - (n)));
      }
    }
    public static BigInteger ToNat(Dafny.ISequence<ushort> str) {
      if ((str).Equals(Dafny.Sequence<ushort>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat((str).Take((new BigInteger((str).Count)) - (BigInteger.One)))) * (Std.JSON.Deserializer.Uint16StrConversion.__default.@base)) + (Dafny.Map<ushort, BigInteger>.Select(Std.JSON.Deserializer.Uint16StrConversion.__default.charToDigit,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt(Dafny.ISequence<ushort> str, ushort minus)
    {
      if (Dafny.Sequence<ushort>.IsPrefixOf(Dafny.Sequence<ushort>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat((str).Drop(BigInteger.One)));
      } else {
        return Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat(str);
      }
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Std.JSON.Deserializer.Uint16StrConversion.__default.ToNatRight(Std.Collections.Seq.__default.DropFirst<BigInteger>(xs))) * (Std.JSON.Deserializer.Uint16StrConversion.__default.BASE())) + (Std.Collections.Seq.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _469___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_469___accumulator);
      } else {
        _469___accumulator = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) * (Std.Arithmetic.Power.__default.Pow(Std.JSON.Deserializer.Uint16StrConversion.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_469___accumulator);
        Dafny.ISequence<BigInteger> _in81 = Std.Collections.Seq.__default.DropLast<BigInteger>(xs);
        xs = _in81;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _470___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_470___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _470___accumulator = Dafny.Sequence<BigInteger>.Concat(_470___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Std.JSON.Deserializer.Uint16StrConversion.__default.BASE())));
        BigInteger _in82 = Dafny.Helpers.EuclideanDivision(n, Std.JSON.Deserializer.Uint16StrConversion.__default.BASE());
        n = _in82;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in83 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in84 = n;
        xs = _in83;
        n = _in84;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _471_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Std.JSON.Deserializer.Uint16StrConversion.__default.SeqExtend(xs, _471_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Std.JSON.Deserializer.Uint16StrConversion.__default.SeqExtend(Std.JSON.Deserializer.Uint16StrConversion.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _472_xs = Std.JSON.Deserializer.Uint16StrConversion.__default.FromNatWithLen(BigInteger.Zero, len);
      return _472_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs13 = Std.JSON.Deserializer.Uint16StrConversion.__default.SeqAdd(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _473_zs_k = _let_tmp_rhs13.dtor__0;
        BigInteger _474_cin = _let_tmp_rhs13.dtor__1;
        BigInteger _475_sum = ((Std.Collections.Seq.__default.Last<BigInteger>(xs)) + (Std.Collections.Seq.__default.Last<BigInteger>(ys))) + (_474_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs14 = (((_475_sum) < (Std.JSON.Deserializer.Uint16StrConversion.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_475_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_475_sum) - (Std.JSON.Deserializer.Uint16StrConversion.__default.BASE()), BigInteger.One)));
        BigInteger _476_sum__out = _let_tmp_rhs14.dtor__0;
        BigInteger _477_cout = _let_tmp_rhs14.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_473_zs_k, Dafny.Sequence<BigInteger>.FromElements(_476_sum__out)), _477_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs15 = Std.JSON.Deserializer.Uint16StrConversion.__default.SeqSub(Std.Collections.Seq.__default.DropLast<BigInteger>(xs), Std.Collections.Seq.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _478_zs = _let_tmp_rhs15.dtor__0;
        BigInteger _479_cin = _let_tmp_rhs15.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs16 = (((Std.Collections.Seq.__default.Last<BigInteger>(xs)) >= ((Std.Collections.Seq.__default.Last<BigInteger>(ys)) + (_479_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Std.Collections.Seq.__default.Last<BigInteger>(xs)) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_479_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Std.JSON.Deserializer.Uint16StrConversion.__default.BASE()) + (Std.Collections.Seq.__default.Last<BigInteger>(xs))) - (Std.Collections.Seq.__default.Last<BigInteger>(ys))) - (_479_cin), BigInteger.One)));
        BigInteger _480_diff__out = _let_tmp_rhs16.dtor__0;
        BigInteger _481_cout = _let_tmp_rhs16.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_478_zs, Dafny.Sequence<BigInteger>.FromElements(_480_diff__out)), _481_cout);
      }
    }
    public static Dafny.ISequence<ushort> chars { get {
      return Dafny.Sequence<ushort>.FromElements((ushort)((new Dafny.Rune('0')).Value), (ushort)((new Dafny.Rune('1')).Value), (ushort)((new Dafny.Rune('2')).Value), (ushort)((new Dafny.Rune('3')).Value), (ushort)((new Dafny.Rune('4')).Value), (ushort)((new Dafny.Rune('5')).Value), (ushort)((new Dafny.Rune('6')).Value), (ushort)((new Dafny.Rune('7')).Value), (ushort)((new Dafny.Rune('8')).Value), (ushort)((new Dafny.Rune('9')).Value), (ushort)((new Dafny.Rune('a')).Value), (ushort)((new Dafny.Rune('b')).Value), (ushort)((new Dafny.Rune('c')).Value), (ushort)((new Dafny.Rune('d')).Value), (ushort)((new Dafny.Rune('e')).Value), (ushort)((new Dafny.Rune('f')).Value), (ushort)((new Dafny.Rune('A')).Value), (ushort)((new Dafny.Rune('B')).Value), (ushort)((new Dafny.Rune('C')).Value), (ushort)((new Dafny.Rune('D')).Value), (ushort)((new Dafny.Rune('E')).Value), (ushort)((new Dafny.Rune('F')).Value));
    } }
    public static BigInteger @base { get {
      return new BigInteger((Std.JSON.Deserializer.Uint16StrConversion.__default.chars).Count);
    } }
    public static Dafny.IMap<ushort,BigInteger> charToDigit { get {
      return Dafny.Map<ushort, BigInteger>.FromElements(new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('0')).Value), BigInteger.Zero), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('1')).Value), BigInteger.One), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('2')).Value), new BigInteger(2)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('3')).Value), new BigInteger(3)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('4')).Value), new BigInteger(4)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('5')).Value), new BigInteger(5)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('6')).Value), new BigInteger(6)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('7')).Value), new BigInteger(7)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('8')).Value), new BigInteger(8)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('9')).Value), new BigInteger(9)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('a')).Value), new BigInteger(10)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('b')).Value), new BigInteger(11)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('c')).Value), new BigInteger(12)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('d')).Value), new BigInteger(13)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('e')).Value), new BigInteger(14)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('f')).Value), new BigInteger(15)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('A')).Value), new BigInteger(10)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('B')).Value), new BigInteger(11)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('C')).Value), new BigInteger(12)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('D')).Value), new BigInteger(13)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('E')).Value), new BigInteger(14)), new Dafny.Pair<ushort, BigInteger>((ushort)((new Dafny.Rune('F')).Value), new BigInteger(15)));
    } }
  }

  public partial class CharSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<ushort>>(Dafny.Sequence<ushort>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class digit {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.Deserializer.Uint16StrConversion
namespace Std.JSON.Deserializer {

  public partial class __default {
    public static bool Bool(Std.JSON.Utils.Views.Core._IView__ js) {
      return ((js).At(0U)) == ((byte)((new Dafny.Rune('t')).Value));
    }
    public static Std.JSON.Errors._IDeserializationError UnsupportedEscape16(Dafny.ISequence<ushort> code) {
      return Std.JSON.Errors.DeserializationError.create_UnsupportedEscape(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr(Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(code), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Couldn't decode UTF-16")));
    }
    public static ushort ToNat16(Dafny.ISequence<ushort> str) {
      BigInteger _482_hd = Std.JSON.Deserializer.Uint16StrConversion.__default.ToNat(str);
      return (ushort)(_482_hd);
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError> Unescape(Dafny.ISequence<ushort> str, BigInteger start, Dafny.ISequence<ushort> prefix)
    {
    TAIL_CALL_START: ;
      if ((start) >= (new BigInteger((str).Count))) {
        return Std.Wrappers.Result<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError>.create_Success(prefix);
      } else if (((str).Select(start)) == ((ushort)((new Dafny.Rune('\\')).Value))) {
        if ((new BigInteger((str).Count)) == ((start) + (BigInteger.One))) {
          return Std.Wrappers.Result<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError>.create_Failure(Std.JSON.Errors.DeserializationError.create_EscapeAtEOS());
        } else {
          ushort _483_c = (str).Select((start) + (BigInteger.One));
          if ((_483_c) == ((ushort)((new Dafny.Rune('u')).Value))) {
            if ((new BigInteger((str).Count)) <= ((start) + (new BigInteger(6)))) {
              return Std.Wrappers.Result<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError>.create_Failure(Std.JSON.Errors.DeserializationError.create_EscapeAtEOS());
            } else {
              Dafny.ISequence<ushort> _484_code = (str).Subsequence((start) + (new BigInteger(2)), (start) + (new BigInteger(6)));
              if (Dafny.Helpers.Id<Func<Dafny.ISequence<ushort>, bool>>((_485_code) => Dafny.Helpers.Quantifier<ushort>((_485_code).UniqueElements, false, (((_exists_var_0) => {
                ushort _486_c = (ushort)_exists_var_0;
                return ((_485_code).Contains(_486_c)) && (!(Std.JSON.Deserializer.__default.HEX__TABLE__16).Contains(_486_c));
              }))))(_484_code)) {
                return Std.Wrappers.Result<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError>.create_Failure(Std.JSON.Deserializer.__default.UnsupportedEscape16(_484_code));
              } else {
                ushort _487_hd = Std.JSON.Deserializer.__default.ToNat16(_484_code);
                Dafny.ISequence<ushort> _in85 = str;
                BigInteger _in86 = (start) + (new BigInteger(6));
                Dafny.ISequence<ushort> _in87 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements(_487_hd));
                str = _in85;
                start = _in86;
                prefix = _in87;
                goto TAIL_CALL_START;
              }
            }
          } else {
            ushort _488_unescaped = (((_483_c) == ((ushort)(34))) ? ((ushort)(34)) : ((((_483_c) == ((ushort)(92))) ? ((ushort)(92)) : ((((_483_c) == ((ushort)(98))) ? ((ushort)(8)) : ((((_483_c) == ((ushort)(102))) ? ((ushort)(12)) : ((((_483_c) == ((ushort)(110))) ? ((ushort)(10)) : ((((_483_c) == ((ushort)(114))) ? ((ushort)(13)) : ((((_483_c) == ((ushort)(116))) ? ((ushort)(9)) : ((ushort)(0)))))))))))))));
            if ((new BigInteger(_488_unescaped)).Sign == 0) {
              return Std.Wrappers.Result<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError>.create_Failure(Std.JSON.Deserializer.__default.UnsupportedEscape16((str).Subsequence(start, (start) + (new BigInteger(2)))));
            } else {
              Dafny.ISequence<ushort> _in88 = str;
              BigInteger _in89 = (start) + (new BigInteger(2));
              Dafny.ISequence<ushort> _in90 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements(_488_unescaped));
              str = _in88;
              start = _in89;
              prefix = _in90;
              goto TAIL_CALL_START;
            }
          }
        }
      } else {
        Dafny.ISequence<ushort> _in91 = str;
        BigInteger _in92 = (start) + (BigInteger.One);
        Dafny.ISequence<ushort> _in93 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements((str).Select(start)));
        str = _in91;
        start = _in92;
        prefix = _in93;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Std.JSON.Errors._IDeserializationError> String(Std.JSON.Grammar._Ijstring js) {
      Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Std.JSON.Errors._IDeserializationError> _489_valueOrError0 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF8Checked(((js).dtor_contents).Bytes())).ToResult<Std.JSON.Errors._IDeserializationError>(Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
      if ((_489_valueOrError0).IsFailure()) {
        return (_489_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
      } else {
        Dafny.ISequence<Dafny.Rune> _490_asUtf32 = (_489_valueOrError0).Extract();
        Std.Wrappers._IResult<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError> _491_valueOrError1 = (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(_490_asUtf32)).ToResult<Std.JSON.Errors._IDeserializationError>(Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
        if ((_491_valueOrError1).IsFailure()) {
          return (_491_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
        } else {
          Dafny.ISequence<ushort> _492_asUint16 = (_491_valueOrError1).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<ushort>, Std.JSON.Errors._IDeserializationError> _493_valueOrError2 = Std.JSON.Deserializer.__default.Unescape(_492_asUint16, BigInteger.Zero, Dafny.Sequence<ushort>.FromElements());
          if ((_493_valueOrError2).IsFailure()) {
            return (_493_valueOrError2).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
          } else {
            Dafny.ISequence<ushort> _494_unescaped = (_493_valueOrError2).Extract();
            return (Std.Unicode.UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_494_unescaped)).ToResult<Std.JSON.Errors._IDeserializationError>(Std.JSON.Errors.DeserializationError.create_InvalidUnicode());
          }
        }
      }
    }
    public static Std.Wrappers._IResult<BigInteger, Std.JSON.Errors._IDeserializationError> ToInt(Std.JSON.Utils.Views.Core._IView__ sign, Std.JSON.Utils.Views.Core._IView__ n)
    {
      BigInteger _495_n = Std.JSON.ByteStrConversion.__default.ToNat((n).Bytes());
      return Std.Wrappers.Result<BigInteger, Std.JSON.Errors._IDeserializationError>.create_Success((((sign).Char_q(new Dafny.Rune('-'))) ? ((BigInteger.Zero) - (_495_n)) : (_495_n)));
    }
    public static Std.Wrappers._IResult<Std.JSON.Values._IDecimal, Std.JSON.Errors._IDeserializationError> Number(Std.JSON.Grammar._Ijnumber js) {
      Std.JSON.Grammar._Ijnumber _let_tmp_rhs17 = js;
      Std.JSON.Utils.Views.Core._IView__ _496_minus = _let_tmp_rhs17.dtor_minus;
      Std.JSON.Utils.Views.Core._IView__ _497_num = _let_tmp_rhs17.dtor_num;
      Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> _498_frac = _let_tmp_rhs17.dtor_frac;
      Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp> _499_exp = _let_tmp_rhs17.dtor_exp;
      Std.Wrappers._IResult<BigInteger, Std.JSON.Errors._IDeserializationError> _500_valueOrError0 = Std.JSON.Deserializer.__default.ToInt(_496_minus, _497_num);
      if ((_500_valueOrError0).IsFailure()) {
        return (_500_valueOrError0).PropagateFailure<Std.JSON.Values._IDecimal>();
      } else {
        BigInteger _501_n = (_500_valueOrError0).Extract();
        Std.Wrappers._IResult<BigInteger, Std.JSON.Errors._IDeserializationError> _502_valueOrError1 = ((System.Func<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>, Std.Wrappers._IResult<BigInteger, Std.JSON.Errors._IDeserializationError>>)((_source17) => {
          if (_source17.is_Empty) {
            return Std.Wrappers.Result<BigInteger, Std.JSON.Errors._IDeserializationError>.create_Success(BigInteger.Zero);
          } else {
            Std.JSON.Grammar._Ijexp _503___mcc_h0 = _source17.dtor_t;
            Std.JSON.Grammar._Ijexp _source18 = _503___mcc_h0;
            Std.JSON.Utils.Views.Core._IView__ _504___mcc_h1 = _source18.dtor_e;
            Std.JSON.Utils.Views.Core._IView__ _505___mcc_h2 = _source18.dtor_sign;
            Std.JSON.Utils.Views.Core._IView__ _506___mcc_h3 = _source18.dtor_num;
            Std.JSON.Utils.Views.Core._IView__ _507_num = _506___mcc_h3;
            Std.JSON.Utils.Views.Core._IView__ _508_sign = _505___mcc_h2;
            return Std.JSON.Deserializer.__default.ToInt(_508_sign, _507_num);
          }
        }))(_499_exp);
        if ((_502_valueOrError1).IsFailure()) {
          return (_502_valueOrError1).PropagateFailure<Std.JSON.Values._IDecimal>();
        } else {
          BigInteger _509_e10 = (_502_valueOrError1).Extract();
          Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac> _source19 = _498_frac;
          if (_source19.is_Empty) {
            return Std.Wrappers.Result<Std.JSON.Values._IDecimal, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.Decimal.create(_501_n, _509_e10));
          } else {
            Std.JSON.Grammar._Ijfrac _510___mcc_h4 = _source19.dtor_t;
            Std.JSON.Grammar._Ijfrac _source20 = _510___mcc_h4;
            Std.JSON.Utils.Views.Core._IView__ _511___mcc_h5 = _source20.dtor_period;
            Std.JSON.Utils.Views.Core._IView__ _512___mcc_h6 = _source20.dtor_num;
            Std.JSON.Utils.Views.Core._IView__ _513_num = _512___mcc_h6;
            BigInteger _514_pow10 = new BigInteger((_513_num).Length());
            Std.Wrappers._IResult<BigInteger, Std.JSON.Errors._IDeserializationError> _515_valueOrError2 = Std.JSON.Deserializer.__default.ToInt(_496_minus, _513_num);
            if ((_515_valueOrError2).IsFailure()) {
              return (_515_valueOrError2).PropagateFailure<Std.JSON.Values._IDecimal>();
            } else {
              BigInteger _516_frac = (_515_valueOrError2).Extract();
              return Std.Wrappers.Result<Std.JSON.Values._IDecimal, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.Decimal.create(((_501_n) * (Std.Arithmetic.Power.__default.Pow(new BigInteger(10), _514_pow10))) + (_516_frac), (_509_e10) - (_514_pow10)));
            }
          }
        }
      }
    }
    public static Std.Wrappers._IResult<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError> KeyValue(Std.JSON.Grammar._IjKeyValue js) {
      Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Std.JSON.Errors._IDeserializationError> _517_valueOrError0 = Std.JSON.Deserializer.__default.String((js).dtor_k);
      if ((_517_valueOrError0).IsFailure()) {
        return (_517_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>>();
      } else {
        Dafny.ISequence<Dafny.Rune> _518_k = (_517_valueOrError0).Extract();
        Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError> _519_valueOrError1 = Std.JSON.Deserializer.__default.Value((js).dtor_v);
        if ((_519_valueOrError1).IsFailure()) {
          return (_519_valueOrError1).PropagateFailure<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>>();
        } else {
          Std.JSON.Values._IJSON _520_v = (_519_valueOrError1).Extract();
          return Std.Wrappers.Result<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError>.create_Success(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>.create(_518_k, _520_v));
        }
      }
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>>, Std.JSON.Errors._IDeserializationError> Object(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> js) {
      return Std.Collections.Seq.__default.MapWithResult<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>, _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError>(Dafny.Helpers.Id<Func<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>, Std.Wrappers._IResult<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError>>>>((_521_js) => ((System.Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>, Std.Wrappers._IResult<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError>>)((_522_d) => {
        return Std.JSON.Deserializer.__default.KeyValue((_522_d).dtor_t);
      })))(js), (js).dtor_data);
    }
    public static Std.Wrappers._IResult<Dafny.ISequence<Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError> Array(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> js) {
      return Std.Collections.Seq.__default.MapWithResult<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>(Dafny.Helpers.Id<Func<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>, Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>>>>((_523_js) => ((System.Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>, Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>>)((_524_d) => {
        return Std.JSON.Deserializer.__default.Value((_524_d).dtor_t);
      })))(js), (js).dtor_data);
    }
    public static Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError> Value(Std.JSON.Grammar._IValue js) {
      Std.JSON.Grammar._IValue _source21 = js;
      if (_source21.is_Null) {
        Std.JSON.Utils.Views.Core._IView__ _525___mcc_h0 = _source21.dtor_n;
        return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_Null());
      } else if (_source21.is_Bool) {
        Std.JSON.Utils.Views.Core._IView__ _526___mcc_h1 = _source21.dtor_b;
        Std.JSON.Utils.Views.Core._IView__ _527_b = _526___mcc_h1;
        return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_Bool(Std.JSON.Deserializer.__default.Bool(_527_b)));
      } else if (_source21.is_String) {
        Std.JSON.Grammar._Ijstring _528___mcc_h2 = _source21.dtor_str;
        Std.JSON.Grammar._Ijstring _529_str = _528___mcc_h2;
        Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Std.JSON.Errors._IDeserializationError> _530_valueOrError0 = Std.JSON.Deserializer.__default.String(_529_str);
        if ((_530_valueOrError0).IsFailure()) {
          return (_530_valueOrError0).PropagateFailure<Std.JSON.Values._IJSON>();
        } else {
          Dafny.ISequence<Dafny.Rune> _531_s = (_530_valueOrError0).Extract();
          return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_String(_531_s));
        }
      } else if (_source21.is_Number) {
        Std.JSON.Grammar._Ijnumber _532___mcc_h3 = _source21.dtor_num;
        Std.JSON.Grammar._Ijnumber _533_dec = _532___mcc_h3;
        Std.Wrappers._IResult<Std.JSON.Values._IDecimal, Std.JSON.Errors._IDeserializationError> _534_valueOrError1 = Std.JSON.Deserializer.__default.Number(_533_dec);
        if ((_534_valueOrError1).IsFailure()) {
          return (_534_valueOrError1).PropagateFailure<Std.JSON.Values._IJSON>();
        } else {
          Std.JSON.Values._IDecimal _535_n = (_534_valueOrError1).Extract();
          return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_Number(_535_n));
        }
      } else if (_source21.is_Object) {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _536___mcc_h4 = _source21.dtor_obj;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _537_obj = _536___mcc_h4;
        Std.Wrappers._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>>, Std.JSON.Errors._IDeserializationError> _538_valueOrError2 = Std.JSON.Deserializer.__default.Object(_537_obj);
        if ((_538_valueOrError2).IsFailure()) {
          return (_538_valueOrError2).PropagateFailure<Std.JSON.Values._IJSON>();
        } else {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Std.JSON.Values._IJSON>> _539_o = (_538_valueOrError2).Extract();
          return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_Object(_539_o));
        }
      } else {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _540___mcc_h5 = _source21.dtor_arr;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _541_arr = _540___mcc_h5;
        Std.Wrappers._IResult<Dafny.ISequence<Std.JSON.Values._IJSON>, Std.JSON.Errors._IDeserializationError> _542_valueOrError3 = Std.JSON.Deserializer.__default.Array(_541_arr);
        if ((_542_valueOrError3).IsFailure()) {
          return (_542_valueOrError3).PropagateFailure<Std.JSON.Values._IJSON>();
        } else {
          Dafny.ISequence<Std.JSON.Values._IJSON> _543_a = (_542_valueOrError3).Extract();
          return Std.Wrappers.Result<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError>.create_Success(Std.JSON.Values.JSON.create_Array(_543_a));
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError> JSON(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js) {
      return Std.JSON.Deserializer.__default.Value((js).dtor_t);
    }
    public static Dafny.IMap<ushort,BigInteger> HEX__TABLE__16 { get {
      return Std.JSON.Deserializer.Uint16StrConversion.__default.charToDigit;
    } }
    public static Dafny.IMap<byte,BigInteger> DIGITS { get {
      return Std.JSON.ByteStrConversion.__default.charToDigit;
    } }
    public static byte MINUS { get {
      return (byte)((new Dafny.Rune('-')).Value);
    } }
  }
} // end of namespace Std.JSON.Deserializer
namespace Std.JSON.ConcreteSyntax.Spec {

  public partial class __default {
    public static Dafny.ISequence<byte> View(Std.JSON.Utils.Views.Core._IView__ v) {
      return (v).Bytes();
    }
    public static Dafny.ISequence<byte> Structural<__T>(Std.JSON.Grammar._IStructural<__T> self, Func<__T, Dafny.ISequence<byte>> fT)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_before), Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((self).dtor_t)), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_after));
    }
    public static Dafny.ISequence<byte> StructuralView(Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> self) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Structural<Std.JSON.Utils.Views.Core._IView__>(self, Std.JSON.ConcreteSyntax.Spec.__default.View);
    }
    public static Dafny.ISequence<byte> Maybe<__T>(Std.JSON.Grammar._IMaybe<__T> self, Func<__T, Dafny.ISequence<byte>> fT)
    {
      if ((self).is_Empty) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        return Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((self).dtor_t);
      }
    }
    public static Dafny.ISequence<byte> ConcatBytes<__T>(Dafny.ISequence<__T> ts, Func<__T, Dafny.ISequence<byte>> fT)
    {
      Dafny.ISequence<byte> _544___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ts).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_544___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _544___accumulator = Dafny.Sequence<byte>.Concat(_544___accumulator, Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((ts).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in94 = (ts).Drop(BigInteger.One);
        Func<__T, Dafny.ISequence<byte>> _in95 = fT;
        ts = _in94;
        fT = _in95;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> Bracketed<__D, __S>(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, __D, __S, Std.JSON.Utils.Views.Core._IView__> self, Func<Std.JSON.Grammar._ISuffixed<__D, __S>, Dafny.ISequence<byte>> fDatum)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.StructuralView((self).dtor_l), Std.JSON.ConcreteSyntax.Spec.__default.ConcatBytes<Std.JSON.Grammar._ISuffixed<__D, __S>>((self).dtor_data, fDatum)), Std.JSON.ConcreteSyntax.Spec.__default.StructuralView((self).dtor_r));
    }
    public static Dafny.ISequence<byte> KeyValue(Std.JSON.Grammar._IjKeyValue self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.String((self).dtor_k), Std.JSON.ConcreteSyntax.Spec.__default.StructuralView((self).dtor_colon)), Std.JSON.ConcreteSyntax.Spec.__default.Value((self).dtor_v));
    }
    public static Dafny.ISequence<byte> Frac(Std.JSON.Grammar._Ijfrac self) {
      return Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_period), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Exp(Std.JSON.Grammar._Ijexp self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_e), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_sign)), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Number(Std.JSON.Grammar._Ijnumber self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_minus), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_num)), Std.JSON.ConcreteSyntax.Spec.__default.Maybe<Std.JSON.Grammar._Ijfrac>((self).dtor_frac, Std.JSON.ConcreteSyntax.Spec.__default.Frac)), Std.JSON.ConcreteSyntax.Spec.__default.Maybe<Std.JSON.Grammar._Ijexp>((self).dtor_exp, Std.JSON.ConcreteSyntax.Spec.__default.Exp));
    }
    public static Dafny.ISequence<byte> String(Std.JSON.Grammar._Ijstring self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_lq), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_contents)), Std.JSON.ConcreteSyntax.Spec.__default.View((self).dtor_rq));
    }
    public static Dafny.ISequence<byte> CommaSuffix(Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> c) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Maybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>(c, Std.JSON.ConcreteSyntax.Spec.__default.StructuralView);
    }
    public static Dafny.ISequence<byte> Member(Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__> self) {
      return Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.KeyValue((self).dtor_t), Std.JSON.ConcreteSyntax.Spec.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Item(Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__> self) {
      return Dafny.Sequence<byte>.Concat(Std.JSON.ConcreteSyntax.Spec.__default.Value((self).dtor_t), Std.JSON.ConcreteSyntax.Spec.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Object(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Bracketed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>(obj, Dafny.Helpers.Id<Func<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>, Dafny.ISequence<byte>>>>((_545_obj) => ((System.Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>, Dafny.ISequence<byte>>)((_546_d) => {
        return Std.JSON.ConcreteSyntax.Spec.__default.Member(_546_d);
      })))(obj));
    }
    public static Dafny.ISequence<byte> Array(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Bracketed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>(arr, Dafny.Helpers.Id<Func<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>, Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>, Dafny.ISequence<byte>>>>((_547_arr) => ((System.Func<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>, Dafny.ISequence<byte>>)((_548_d) => {
        return Std.JSON.ConcreteSyntax.Spec.__default.Item(_548_d);
      })))(arr));
    }
    public static Dafny.ISequence<byte> Value(Std.JSON.Grammar._IValue self) {
      Std.JSON.Grammar._IValue _source22 = self;
      if (_source22.is_Null) {
        Std.JSON.Utils.Views.Core._IView__ _549___mcc_h0 = _source22.dtor_n;
        Std.JSON.Utils.Views.Core._IView__ _550_n = _549___mcc_h0;
        return Std.JSON.ConcreteSyntax.Spec.__default.View(_550_n);
      } else if (_source22.is_Bool) {
        Std.JSON.Utils.Views.Core._IView__ _551___mcc_h1 = _source22.dtor_b;
        Std.JSON.Utils.Views.Core._IView__ _552_b = _551___mcc_h1;
        return Std.JSON.ConcreteSyntax.Spec.__default.View(_552_b);
      } else if (_source22.is_String) {
        Std.JSON.Grammar._Ijstring _553___mcc_h2 = _source22.dtor_str;
        Std.JSON.Grammar._Ijstring _554_str = _553___mcc_h2;
        return Std.JSON.ConcreteSyntax.Spec.__default.String(_554_str);
      } else if (_source22.is_Number) {
        Std.JSON.Grammar._Ijnumber _555___mcc_h3 = _source22.dtor_num;
        Std.JSON.Grammar._Ijnumber _556_num = _555___mcc_h3;
        return Std.JSON.ConcreteSyntax.Spec.__default.Number(_556_num);
      } else if (_source22.is_Object) {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _557___mcc_h4 = _source22.dtor_obj;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _558_obj = _557___mcc_h4;
        return Std.JSON.ConcreteSyntax.Spec.__default.Object(_558_obj);
      } else {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _559___mcc_h5 = _source22.dtor_arr;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _560_arr = _559___mcc_h5;
        return Std.JSON.ConcreteSyntax.Spec.__default.Array(_560_arr);
      }
    }
    public static Dafny.ISequence<byte> JSON(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Structural<Std.JSON.Grammar._IValue>(js, Std.JSON.ConcreteSyntax.Spec.__default.Value);
    }
  }
} // end of namespace Std.JSON.ConcreteSyntax.Spec
namespace Std.JSON.ConcreteSyntax.SpecProperties {

} // end of namespace Std.JSON.ConcreteSyntax.SpecProperties
namespace Std.JSON.ConcreteSyntax {

} // end of namespace Std.JSON.ConcreteSyntax
namespace Std.JSON.ZeroCopy.Serializer {

  public partial class __default {
    public static Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> Serialize(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js)
    {
      Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> rbs = Std.Wrappers.Result<byte[], Std.JSON.Errors._ISerializationError>.Default(new byte[0]);
      Std.JSON.Utils.Views.Writers._IWriter__ _561_writer;
      _561_writer = Std.JSON.ZeroCopy.Serializer.__default.Text(js);
      Std.Wrappers._IOutcomeResult<Std.JSON.Errors._ISerializationError> _562_valueOrError0 = Std.Wrappers.OutcomeResult<Std.JSON.Errors._ISerializationError>.Default();
      _562_valueOrError0 = Std.Wrappers.__default.Need<Std.JSON.Errors._ISerializationError>((_561_writer).Unsaturated_q, Std.JSON.Errors.SerializationError.create_OutOfMemory());
      if ((_562_valueOrError0).IsFailure()) {
        rbs = (_562_valueOrError0).PropagateFailure<byte[]>();
        return rbs;
      }
      byte[] _563_bs;
      byte[] _out6;
      _out6 = (_561_writer).ToArray();
      _563_bs = _out6;
      rbs = Std.Wrappers.Result<byte[], Std.JSON.Errors._ISerializationError>.create_Success(_563_bs);
      return rbs;
      return rbs;
    }
    public static Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> SerializeTo(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js, byte[] dest)
    {
      Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> len = Std.Wrappers.Result<uint, Std.JSON.Errors._ISerializationError>.Default(0);
      Std.JSON.Utils.Views.Writers._IWriter__ _564_writer;
      _564_writer = Std.JSON.ZeroCopy.Serializer.__default.Text(js);
      Std.Wrappers._IOutcomeResult<Std.JSON.Errors._ISerializationError> _565_valueOrError0 = Std.Wrappers.OutcomeResult<Std.JSON.Errors._ISerializationError>.Default();
      _565_valueOrError0 = Std.Wrappers.__default.Need<Std.JSON.Errors._ISerializationError>((_564_writer).Unsaturated_q, Std.JSON.Errors.SerializationError.create_OutOfMemory());
      if ((_565_valueOrError0).IsFailure()) {
        len = (_565_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      Std.Wrappers._IOutcomeResult<Std.JSON.Errors._ISerializationError> _566_valueOrError1 = Std.Wrappers.OutcomeResult<Std.JSON.Errors._ISerializationError>.Default();
      _566_valueOrError1 = Std.Wrappers.__default.Need<Std.JSON.Errors._ISerializationError>((new BigInteger((_564_writer).dtor_length)) <= (new BigInteger((dest).Length)), Std.JSON.Errors.SerializationError.create_OutOfMemory());
      if ((_566_valueOrError1).IsFailure()) {
        len = (_566_valueOrError1).PropagateFailure<uint>();
        return len;
      }
      (_564_writer).CopyTo(dest);
      len = Std.Wrappers.Result<uint, Std.JSON.Errors._ISerializationError>.create_Success((_564_writer).dtor_length);
      return len;
      return len;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Text(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js) {
      return Std.JSON.ZeroCopy.Serializer.__default.JSON(js, Std.JSON.Utils.Views.Writers.Writer__.Empty);
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ JSON(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      return (((writer).Append((js).dtor_before)).Then(Dafny.Helpers.Id<Func<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Func<Std.JSON.Utils.Views.Writers._IWriter__, Std.JSON.Utils.Views.Writers._IWriter__>>>((_567_js) => ((System.Func<Std.JSON.Utils.Views.Writers._IWriter__, Std.JSON.Utils.Views.Writers._IWriter__>)((_568_wr) => {
        return Std.JSON.ZeroCopy.Serializer.__default.Value((_567_js).dtor_t, _568_wr);
      })))(js))).Append((js).dtor_after);
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Value(Std.JSON.Grammar._IValue v, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Grammar._IValue _source23 = v;
      if (_source23.is_Null) {
        Std.JSON.Utils.Views.Core._IView__ _569___mcc_h0 = _source23.dtor_n;
        Std.JSON.Utils.Views.Core._IView__ _570_n = _569___mcc_h0;
        Std.JSON.Utils.Views.Writers._IWriter__ _571_wr = (writer).Append(_570_n);
        return _571_wr;
      } else if (_source23.is_Bool) {
        Std.JSON.Utils.Views.Core._IView__ _572___mcc_h1 = _source23.dtor_b;
        Std.JSON.Utils.Views.Core._IView__ _573_b = _572___mcc_h1;
        Std.JSON.Utils.Views.Writers._IWriter__ _574_wr = (writer).Append(_573_b);
        return _574_wr;
      } else if (_source23.is_String) {
        Std.JSON.Grammar._Ijstring _575___mcc_h2 = _source23.dtor_str;
        Std.JSON.Grammar._Ijstring _576_str = _575___mcc_h2;
        Std.JSON.Utils.Views.Writers._IWriter__ _577_wr = Std.JSON.ZeroCopy.Serializer.__default.String(_576_str, writer);
        return _577_wr;
      } else if (_source23.is_Number) {
        Std.JSON.Grammar._Ijnumber _578___mcc_h3 = _source23.dtor_num;
        Std.JSON.Grammar._Ijnumber _579_num = _578___mcc_h3;
        Std.JSON.Utils.Views.Writers._IWriter__ _580_wr = Std.JSON.ZeroCopy.Serializer.__default.Number(_579_num, writer);
        return _580_wr;
      } else if (_source23.is_Object) {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _581___mcc_h4 = _source23.dtor_obj;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _582_obj = _581___mcc_h4;
        Std.JSON.Utils.Views.Writers._IWriter__ _583_wr = Std.JSON.ZeroCopy.Serializer.__default.Object(_582_obj, writer);
        return _583_wr;
      } else {
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _584___mcc_h5 = _source23.dtor_arr;
        Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _585_arr = _584___mcc_h5;
        Std.JSON.Utils.Views.Writers._IWriter__ _586_wr = Std.JSON.ZeroCopy.Serializer.__default.Array(_585_arr, writer);
        return _586_wr;
      }
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ String(Std.JSON.Grammar._Ijstring str, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      return (((writer).Append((str).dtor_lq)).Append((str).dtor_contents)).Append((str).dtor_rq);
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Number(Std.JSON.Grammar._Ijnumber num, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ _587_wr1 = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      Std.JSON.Utils.Views.Writers._IWriter__ _588_wr2 = ((((num).dtor_frac).is_NonEmpty) ? (((_587_wr1).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_587_wr1));
      Std.JSON.Utils.Views.Writers._IWriter__ _589_wr3 = ((((num).dtor_exp).is_NonEmpty) ? ((((_588_wr2).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_588_wr2));
      Std.JSON.Utils.Views.Writers._IWriter__ _590_wr = _589_wr3;
      return _590_wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ StructuralView(Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__> st, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Object(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ _591_wr = Std.JSON.ZeroCopy.Serializer.__default.StructuralView((obj).dtor_l, writer);
      Std.JSON.Utils.Views.Writers._IWriter__ _592_wr = Std.JSON.ZeroCopy.Serializer.__default.Members(obj, _591_wr);
      Std.JSON.Utils.Views.Writers._IWriter__ _593_wr = Std.JSON.ZeroCopy.Serializer.__default.StructuralView((obj).dtor_r, _592_wr);
      return _593_wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Array(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ _594_wr = Std.JSON.ZeroCopy.Serializer.__default.StructuralView((arr).dtor_l, writer);
      Std.JSON.Utils.Views.Writers._IWriter__ _595_wr = Std.JSON.ZeroCopy.Serializer.__default.Items(arr, _594_wr);
      Std.JSON.Utils.Views.Writers._IWriter__ _596_wr = Std.JSON.ZeroCopy.Serializer.__default.StructuralView((arr).dtor_r, _595_wr);
      return _596_wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Members(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ wr = Std.JSON.Utils.Views.Writers.Writer.Default();
      Std.JSON.Utils.Views.Writers._IWriter__ _out7;
      _out7 = Std.JSON.ZeroCopy.Serializer.__default.MembersImpl(obj, writer);
      wr = _out7;
      return wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Items(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ wr = Std.JSON.Utils.Views.Writers.Writer.Default();
      Std.JSON.Utils.Views.Writers._IWriter__ _out8;
      _out8 = Std.JSON.ZeroCopy.Serializer.__default.ItemsImpl(arr, writer);
      wr = _out8;
      return wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ MembersImpl(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> obj, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ wr = Std.JSON.Utils.Views.Writers.Writer.Default();
      wr = writer;
      Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>> _597_members;
      _597_members = (obj).dtor_data;
      BigInteger _hi1 = new BigInteger((_597_members).Count);
      for (BigInteger _598_i = BigInteger.Zero; _598_i < _hi1; _598_i++) {
        wr = Std.JSON.ZeroCopy.Serializer.__default.Member((_597_members).Select(_598_i), wr);
      }
      return wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ ItemsImpl(Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> arr, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ wr = Std.JSON.Utils.Views.Writers.Writer.Default();
      wr = writer;
      Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>> _599_items;
      _599_items = (arr).dtor_data;
      BigInteger _hi2 = new BigInteger((_599_items).Count);
      for (BigInteger _600_i = BigInteger.Zero; _600_i < _hi2; _600_i++) {
        wr = Std.JSON.ZeroCopy.Serializer.__default.Item((_599_items).Select(_600_i), wr);
      }
      return wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Member(Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__> m, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ _601_wr = Std.JSON.ZeroCopy.Serializer.__default.String(((m).dtor_t).dtor_k, writer);
      Std.JSON.Utils.Views.Writers._IWriter__ _602_wr = Std.JSON.ZeroCopy.Serializer.__default.StructuralView(((m).dtor_t).dtor_colon, _601_wr);
      Std.JSON.Utils.Views.Writers._IWriter__ _603_wr = Std.JSON.ZeroCopy.Serializer.__default.Value(((m).dtor_t).dtor_v, _602_wr);
      Std.JSON.Utils.Views.Writers._IWriter__ _604_wr = ((((m).dtor_suffix).is_Empty) ? (_603_wr) : (Std.JSON.ZeroCopy.Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _603_wr)));
      return _604_wr;
    }
    public static Std.JSON.Utils.Views.Writers._IWriter__ Item(Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__> m, Std.JSON.Utils.Views.Writers._IWriter__ writer)
    {
      Std.JSON.Utils.Views.Writers._IWriter__ _605_wr = Std.JSON.ZeroCopy.Serializer.__default.Value((m).dtor_t, writer);
      Std.JSON.Utils.Views.Writers._IWriter__ _606_wr = ((((m).dtor_suffix).is_Empty) ? (_605_wr) : (Std.JSON.ZeroCopy.Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _605_wr)));
      return _606_wr;
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Serializer
namespace Std.JSON.ZeroCopy.Deserializer.Core {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Get(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Errors._IDeserializationError err)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _607_valueOrError0 = (cs).Get<Std.JSON.Errors._IDeserializationError>(err);
      if ((_607_valueOrError0).IsFailure()) {
        return (_607_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _608_cs = (_607_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_608_cs).Split());
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> WS(Std.JSON.Utils.Cursors._ICursor__ cs)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core._IView__>.Default(Std.JSON.Grammar.jblanks.Default());
      uint _609_point_k;
      _609_point_k = (cs).dtor_point;
      uint _610_end;
      _610_end = (cs).dtor_end;
      while (((_609_point_k) < (_610_end)) && (Std.JSON.Grammar.__default.Blank_q(((cs).dtor_s).Select(_609_point_k)))) {
        _609_point_k = (_609_point_k) + (1U);
      }
      sp = (Std.JSON.Utils.Cursors.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _609_point_k, (cs).dtor_end)).Split();
      return sp;
      return sp;
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<__T>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Structural<__T>(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._IParser__<__T, Std.JSON.Errors._IDeserializationError> parser)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs18 = Std.JSON.ZeroCopy.Deserializer.Core.__default.WS(cs);
      Std.JSON.Utils.Views.Core._IView__ _611_before = _let_tmp_rhs18.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _612_cs = _let_tmp_rhs18.dtor_cs;
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _613_valueOrError0 = Dafny.Helpers.Id<Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<__T>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>>>((parser).dtor_fn)(_612_cs);
      if ((_613_valueOrError0).IsFailure()) {
        return (_613_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<__T>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<__T> _let_tmp_rhs19 = (_613_valueOrError0).Extract();
        __T _614_val = _let_tmp_rhs19.dtor_t;
        Std.JSON.Utils.Cursors._ICursor__ _615_cs = _let_tmp_rhs19.dtor_cs;
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs20 = Std.JSON.ZeroCopy.Deserializer.Core.__default.WS(_615_cs);
        Std.JSON.Utils.Views.Core._IView__ _616_after = _let_tmp_rhs20.dtor_t;
        Std.JSON.Utils.Cursors._ICursor__ _617_cs = _let_tmp_rhs20.dtor_cs;
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<__T>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IStructural<__T>>.create(Std.JSON.Grammar.Structural<__T>.create(_611_before, _614_val, _616_after), _617_cs));
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> TryStructural(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs21 = Std.JSON.ZeroCopy.Deserializer.Core.__default.WS(cs);
      Std.JSON.Utils.Views.Core._IView__ _618_before = _let_tmp_rhs21.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _619_cs = _let_tmp_rhs21.dtor_cs;
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs22 = ((_619_cs).SkipByte()).Split();
      Std.JSON.Utils.Views.Core._IView__ _620_val = _let_tmp_rhs22.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _621_cs = _let_tmp_rhs22.dtor_cs;
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs23 = Std.JSON.ZeroCopy.Deserializer.Core.__default.WS(_621_cs);
      Std.JSON.Utils.Views.Core._IView__ _622_after = _let_tmp_rhs23.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _623_cs = _let_tmp_rhs23.dtor_cs;
      return Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>.create(Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core._IView__>.create(_618_before, _620_val, _622_after), _623_cs);
    }
    public static Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>> SpecView { get {
      return ((System.Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>>)((_624_v) => {
        return Std.JSON.ConcreteSyntax.Spec.__default.View(_624_v);
      }));
    } }
  }

  public partial class jopt {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.ZeroCopy.Deserializer.Core.jopt.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ValueParser {
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>>(Std.JSON.Utils.Parsers.SubParser<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Core
namespace Std.JSON.ZeroCopy.Deserializer.Strings {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> StringBody(Std.JSON.Utils.Cursors._ICursor__ cs)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.Default(Std.JSON.Utils.Cursors.Cursor.Default());
      bool _625_escaped;
      _625_escaped = false;
      uint _hi3 = (cs).dtor_end;
      for (uint _626_point_k = (cs).dtor_point; _626_point_k < _hi3; _626_point_k++) {
        byte _627_byte;
        _627_byte = ((cs).dtor_s).Select(_626_point_k);
        if (((_627_byte) == ((byte)((new Dafny.Rune('\"')).Value))) && (!(_625_escaped))) {
          pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _626_point_k, (cs).dtor_end));
          return pr;
        } else if ((_627_byte) == ((byte)((new Dafny.Rune('\\')).Value))) {
          _625_escaped = !(_625_escaped);
        } else {
          _625_escaped = false;
        }
      }
      pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_EOF());
      return pr;
      return pr;
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Quote(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _628_valueOrError0 = (cs).AssertChar<Std.JSON.Errors._IDeserializationError>(new Dafny.Rune('\"'));
      if ((_628_valueOrError0).IsFailure()) {
        return (_628_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _629_cs = (_628_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_629_cs).Split());
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> String(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _630_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.Quote(cs);
      if ((_630_valueOrError0).IsFailure()) {
        return (_630_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs24 = (_630_valueOrError0).Extract();
        Std.JSON.Utils.Views.Core._IView__ _631_lq = _let_tmp_rhs24.dtor_t;
        Std.JSON.Utils.Cursors._ICursor__ _632_cs = _let_tmp_rhs24.dtor_cs;
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _633_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.StringBody(_632_cs);
        if ((_633_valueOrError1).IsFailure()) {
          return (_633_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>>();
        } else {
          Std.JSON.Utils.Cursors._ICursor__ _634_contents = (_633_valueOrError1).Extract();
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs25 = (_634_contents).Split();
          Std.JSON.Utils.Views.Core._IView__ _635_contents = _let_tmp_rhs25.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _636_cs = _let_tmp_rhs25.dtor_cs;
          Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _637_valueOrError2 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.Quote(_636_cs);
          if ((_637_valueOrError2).IsFailure()) {
            return (_637_valueOrError2).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>>();
          } else {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs26 = (_637_valueOrError2).Extract();
            Std.JSON.Utils.Views.Core._IView__ _638_rq = _let_tmp_rhs26.dtor_t;
            Std.JSON.Utils.Cursors._ICursor__ _639_cs = _let_tmp_rhs26.dtor_cs;
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._Ijstring>.create(Std.JSON.Grammar.jstring.create(_631_lq, _635_contents, _638_rq), _639_cs));
          }
        }
      }
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Strings
namespace Std.JSON.ZeroCopy.Deserializer.Numbers {

  public partial class __default {
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> Digits(Std.JSON.Utils.Cursors._ICursor__ cs) {
      return ((cs).SkipWhile(Std.JSON.Grammar.__default.Digit_q)).Split();
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> NonEmptyDigits(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _640_sp = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.Digits(cs);
      if (((_640_sp).dtor_t).Empty_q) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_OtherError(Std.JSON.Errors.DeserializationError.create_EmptyNumber()));
      } else {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_640_sp);
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> NonZeroInt(Std.JSON.Utils.Cursors._ICursor__ cs) {
      return Std.JSON.ZeroCopy.Deserializer.Numbers.__default.NonEmptyDigits(cs);
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> OptionalMinus(Std.JSON.Utils.Cursors._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_641_c) => {
        return (_641_c) == ((byte)((new Dafny.Rune('-')).Value));
      })))).Split();
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> OptionalSign(Std.JSON.Utils.Cursors._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_642_c) => {
        return ((_642_c) == ((byte)((new Dafny.Rune('-')).Value))) || ((_642_c) == ((byte)((new Dafny.Rune('+')).Value)));
      })))).Split();
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> TrimmedInt(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _643_sp = ((cs).SkipIf(((System.Func<byte, bool>)((_644_c) => {
        return (_644_c) == ((byte)((new Dafny.Rune('0')).Value));
      })))).Split();
      if (((_643_sp).dtor_t).Empty_q) {
        return Std.JSON.ZeroCopy.Deserializer.Numbers.__default.NonZeroInt((_643_sp).dtor_cs);
      } else {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_643_sp);
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Exp(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs27 = ((cs).SkipIf(((System.Func<byte, bool>)((_645_c) => {
        return ((_645_c) == ((byte)((new Dafny.Rune('e')).Value))) || ((_645_c) == ((byte)((new Dafny.Rune('E')).Value)));
      })))).Split();
      Std.JSON.Utils.Views.Core._IView__ _646_e = _let_tmp_rhs27.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _647_cs = _let_tmp_rhs27.dtor_cs;
      if ((_646_e).Empty_q) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>.create(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijexp>.create_Empty(), _647_cs));
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs28 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.OptionalSign(_647_cs);
        Std.JSON.Utils.Views.Core._IView__ _648_sign = _let_tmp_rhs28.dtor_t;
        Std.JSON.Utils.Cursors._ICursor__ _649_cs = _let_tmp_rhs28.dtor_cs;
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _650_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.NonEmptyDigits(_649_cs);
        if ((_650_valueOrError0).IsFailure()) {
          return (_650_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs29 = (_650_valueOrError0).Extract();
          Std.JSON.Utils.Views.Core._IView__ _651_num = _let_tmp_rhs29.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _652_cs = _let_tmp_rhs29.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>.create(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijexp>.create_NonEmpty(Std.JSON.Grammar.jexp.create(_646_e, _648_sign, _651_num)), _652_cs));
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Frac(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs30 = ((cs).SkipIf(((System.Func<byte, bool>)((_653_c) => {
        return (_653_c) == ((byte)((new Dafny.Rune('.')).Value));
      })))).Split();
      Std.JSON.Utils.Views.Core._IView__ _654_period = _let_tmp_rhs30.dtor_t;
      Std.JSON.Utils.Cursors._ICursor__ _655_cs = _let_tmp_rhs30.dtor_cs;
      if ((_654_period).Empty_q) {
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>.create(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijfrac>.create_Empty(), _655_cs));
      } else {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _656_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.NonEmptyDigits(_655_cs);
        if ((_656_valueOrError0).IsFailure()) {
          return (_656_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs31 = (_656_valueOrError0).Extract();
          Std.JSON.Utils.Views.Core._IView__ _657_num = _let_tmp_rhs31.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _658_cs = _let_tmp_rhs31.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>.create(Std.JSON.Grammar.Maybe<Std.JSON.Grammar._Ijfrac>.create_NonEmpty(Std.JSON.Grammar.jfrac.create(_654_period, _657_num)), _658_cs));
        }
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber> NumberFromParts(Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> minus, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> num, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>> frac, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>> exp)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber> _659_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._Ijnumber>.create(Std.JSON.Grammar.jnumber.create((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _659_sp;
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Number(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _660_minus = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.OptionalMinus(cs);
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _661_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.TrimmedInt((_660_minus).dtor_cs);
      if ((_661_valueOrError0).IsFailure()) {
        return (_661_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _662_num = (_661_valueOrError0).Extract();
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _663_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.Frac((_662_num).dtor_cs);
        if ((_663_valueOrError1).IsFailure()) {
          return (_663_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijfrac>> _664_frac = (_663_valueOrError1).Extract();
          Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _665_valueOrError2 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.Exp((_664_frac).dtor_cs);
          if ((_665_valueOrError2).IsFailure()) {
            return (_665_valueOrError2).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>>();
          } else {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IMaybe<Std.JSON.Grammar._Ijexp>> _666_exp = (_665_valueOrError2).Extract();
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.ZeroCopy.Deserializer.Numbers.__default.NumberFromParts(_660_minus, _662_num, _664_frac, _666_exp));
          }
        }
      }
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Numbers
namespace Std.JSON.ZeroCopy.Deserializer.ObjectParams {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Colon(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _667_valueOrError0 = (cs).AssertChar<Std.JSON.Errors._IDeserializationError>(new Dafny.Rune(':'));
      if ((_667_valueOrError0).IsFailure()) {
        return (_667_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _668_cs = (_667_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_668_cs).Split());
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> KeyValueFromParts(Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring> k, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> colon, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> v)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> _669_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IjKeyValue>.create(Std.JSON.Grammar.jKeyValue.create((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _669_sp;
    }
    public static Dafny.ISequence<byte> ElementSpec(Std.JSON.Grammar._IjKeyValue t) {
      return Std.JSON.ConcreteSyntax.Spec.__default.KeyValue(t);
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Element(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _670_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.String(cs);
      if ((_670_valueOrError0).IsFailure()) {
        return (_670_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring> _671_k = (_670_valueOrError0).Extract();
        Std.JSON.Utils.Parsers._IParser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError> _672_p = Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.Colon);
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _673_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Utils.Views.Core._IView__>((_671_k).dtor_cs, _672_p);
        if ((_673_valueOrError1).IsFailure()) {
          return (_673_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _674_colon = (_673_valueOrError1).Extract();
          Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _675_valueOrError2 = Dafny.Helpers.Id<Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>>>((json).dtor_fn)((_674_colon).dtor_cs);
          if ((_675_valueOrError2).IsFailure()) {
            return (_675_valueOrError2).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>>();
          } else {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> _676_v = (_675_valueOrError2).Extract();
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> _677_kv = Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.KeyValueFromParts(_671_k, _674_colon, _676_v);
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_677_kv);
          }
        }
      }
    }
    public static byte OPEN { get {
      return (byte)((new Dafny.Rune('{')).Value);
    } }
    public static byte CLOSE { get {
      return (byte)((new Dafny.Rune('}')).Value);
    } }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.ObjectParams
namespace Std.JSON.ZeroCopy.Deserializer.Objects {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Object(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _678_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Objects.__default.Bracketed(cs, json);
      if ((_678_valueOrError0).IsFailure()) {
        return (_678_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _679_sp = (_678_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_679_sp);
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Open(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _680_valueOrError0 = (cs).AssertByte<Std.JSON.Errors._IDeserializationError>(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.OPEN);
      if ((_680_valueOrError0).IsFailure()) {
        return (_680_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _681_cs = (_680_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_681_cs).Split());
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Close(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _682_valueOrError0 = (cs).AssertByte<Std.JSON.Errors._IDeserializationError>(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE);
      if ((_682_valueOrError0).IsFailure()) {
        return (_682_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _683_cs = (_682_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_683_cs).Split());
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> BracketedFromParts(Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> open, Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> close)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _684_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>.create(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _684_sp;
    }
    public static Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> AppendWithSuffix(Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> elem, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> sep)
    {
      Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__> _685_suffixed = Std.JSON.Grammar.Suffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>.create((elem).dtor_t, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>.create_NonEmpty((sep).dtor_t));
      Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _686_elems_k = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(_685_suffixed)), (sep).dtor_cs);
      return _686_elems_k;
    }
    public static Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> AppendLast(Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> elem, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> sep)
    {
      Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__> _687_suffixed = Std.JSON.Grammar.Suffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>.create((elem).dtor_t, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>.create_Empty());
      Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _688_elems_k = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(_687_suffixed)), (elem).dtor_cs);
      return _688_elems_k;
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Elements(Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> open, Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _689_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.Element((elems).dtor_cs, json);
      if ((_689_valueOrError0).IsFailure()) {
        return (_689_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IjKeyValue> _690_elem = (_689_valueOrError0).Extract();
        if (((_690_elem).dtor_cs).EOF_q) {
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_EOF());
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _691_sep = Std.JSON.ZeroCopy.Deserializer.Core.__default.TryStructural((_690_elem).dtor_cs);
          short _692_s0 = (((_691_sep).dtor_t).dtor_t).Peek();
          if (((_692_s0) == ((short)(Std.JSON.ZeroCopy.Deserializer.Objects.__default.SEPARATOR))) && (((((_691_sep).dtor_t).dtor_t).Length()) == (1U))) {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _693_sep = _691_sep;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _694_elems = Std.JSON.ZeroCopy.Deserializer.Objects.__default.AppendWithSuffix(elems, _690_elem, _693_sep);
            Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> _in96 = json;
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _in97 = open;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _in98 = _694_elems;
            json = _in96;
            open = _in97;
            elems = _in98;
            goto TAIL_CALL_START;
          } else if (((_692_s0) == ((short)(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE))) && (((((_691_sep).dtor_t).dtor_t).Length()) == (1U))) {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _695_sep = _691_sep;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _696_elems_k = Std.JSON.ZeroCopy.Deserializer.Objects.__default.AppendLast(elems, _690_elem, _695_sep);
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _697_bracketed = Std.JSON.ZeroCopy.Deserializer.Objects.__default.BracketedFromParts(open, _696_elems_k, _695_sep);
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_697_bracketed);
          } else {
            byte _698_separator = Std.JSON.ZeroCopy.Deserializer.Objects.__default.SEPARATOR;
            Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _699_pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE, _698_separator), _692_s0));
            return _699_pr;
          }
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Bracketed(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _700_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Utils.Views.Core._IView__>(cs, Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.Objects.__default.Open));
      if ((_700_valueOrError0).IsFailure()) {
        return (_700_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _701_open = (_700_valueOrError0).Extract();
        Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>> _702_elems = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(), (_701_open).dtor_cs);
        if ((((_701_open).dtor_cs).Peek()) == ((short)(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE))) {
          Std.JSON.Utils.Parsers._IParser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError> _703_p = Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.Objects.__default.Close);
          Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _704_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Utils.Views.Core._IView__>((_701_open).dtor_cs, _703_p);
          if ((_704_valueOrError1).IsFailure()) {
            return (_704_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
          } else {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _705_close = (_704_valueOrError1).Extract();
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.ZeroCopy.Deserializer.Objects.__default.BracketedFromParts(_701_open, _702_elems, _705_close));
          }
        } else {
          return Std.JSON.ZeroCopy.Deserializer.Objects.__default.Elements(json, _701_open, _702_elems);
        }
      }
    }
    public static Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>> SpecViewOpen { get {
      return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView;
    } }
    public static Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>> SpecViewClose { get {
      return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView;
    } }
    public static byte SEPARATOR { get {
      return (byte)((new Dafny.Rune(',')).Value);
    } }
  }

  public partial class jopen {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.OPEN));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.ZeroCopy.Deserializer.Objects.jopen.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ObjectParams.__default.CLOSE));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.ZeroCopy.Deserializer.Objects.jclose.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Objects
namespace Std.JSON.ZeroCopy.Deserializer.ArrayParams {

  public partial class __default {
    public static Dafny.ISequence<byte> ElementSpec(Std.JSON.Grammar._IValue t) {
      return Std.JSON.ConcreteSyntax.Spec.__default.Value(t);
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Element(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      return Dafny.Helpers.Id<Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>>>((json).dtor_fn)(cs);
    }
    public static byte OPEN { get {
      return (byte)((new Dafny.Rune('[')).Value);
    } }
    public static byte CLOSE { get {
      return (byte)((new Dafny.Rune(']')).Value);
    } }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.ArrayParams
namespace Std.JSON.ZeroCopy.Deserializer.Arrays {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Array(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _706_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Bracketed(cs, json);
      if ((_706_valueOrError0).IsFailure()) {
        return (_706_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _707_sp = (_706_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_707_sp);
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Open(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _708_valueOrError0 = (cs).AssertByte<Std.JSON.Errors._IDeserializationError>(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.OPEN);
      if ((_708_valueOrError0).IsFailure()) {
        return (_708_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _709_cs = (_708_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_709_cs).Split());
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Close(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _710_valueOrError0 = (cs).AssertByte<Std.JSON.Errors._IDeserializationError>(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE);
      if ((_710_valueOrError0).IsFailure()) {
        return (_710_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _711_cs = (_710_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_711_cs).Split());
      }
    }
    public static Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> BracketedFromParts(Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> open, Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> close)
    {
      Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _712_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>.create(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _712_sp;
    }
    public static Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> AppendWithSuffix(Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> elem, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> sep)
    {
      Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__> _713_suffixed = Std.JSON.Grammar.Suffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>.create((elem).dtor_t, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>.create_NonEmpty((sep).dtor_t));
      Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _714_elems_k = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(_713_suffixed)), (sep).dtor_cs);
      return _714_elems_k;
    }
    public static Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> AppendLast(Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> elems, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> elem, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> sep)
    {
      Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__> _715_suffixed = Std.JSON.Grammar.Suffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>.create((elem).dtor_t, Std.JSON.Grammar.Maybe<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>.create_Empty());
      Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _716_elems_k = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(_715_suffixed)), (elem).dtor_cs);
      return _716_elems_k;
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Elements(Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json, Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> open, Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _717_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.Element((elems).dtor_cs, json);
      if ((_717_valueOrError0).IsFailure()) {
        return (_717_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> _718_elem = (_717_valueOrError0).Extract();
        if (((_718_elem).dtor_cs).EOF_q) {
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_EOF());
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _719_sep = Std.JSON.ZeroCopy.Deserializer.Core.__default.TryStructural((_718_elem).dtor_cs);
          short _720_s0 = (((_719_sep).dtor_t).dtor_t).Peek();
          if (((_720_s0) == ((short)(Std.JSON.ZeroCopy.Deserializer.Arrays.__default.SEPARATOR))) && (((((_719_sep).dtor_t).dtor_t).Length()) == (1U))) {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _721_sep = _719_sep;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _722_elems = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.AppendWithSuffix(elems, _718_elem, _721_sep);
            Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> _in99 = json;
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _in100 = open;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _in101 = _722_elems;
            json = _in99;
            open = _in100;
            elems = _in101;
            goto TAIL_CALL_START;
          } else if (((_720_s0) == ((short)(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE))) && (((((_719_sep).dtor_t).dtor_t).Length()) == (1U))) {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _723_sep = _719_sep;
            Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _724_elems_k = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.AppendLast(elems, _718_elem, _723_sep);
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _725_bracketed = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.BracketedFromParts(open, _724_elems_k, _723_sep);
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_725_bracketed);
          } else {
            byte _726_separator = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.SEPARATOR;
            Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _727_pr = Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Failure(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors._IDeserializationError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE, _726_separator), _720_s0));
            return _727_pr;
          }
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Bracketed(Std.JSON.Utils.Cursors._ICursor__ cs, Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> json)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _728_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Utils.Views.Core._IView__>(cs, Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Open));
      if ((_728_valueOrError0).IsFailure()) {
        return (_728_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _729_open = (_728_valueOrError0).Extract();
        Std.JSON.Utils.Cursors._ISplit<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>> _730_elems = Std.JSON.Utils.Cursors.Split<Dafny.ISequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>>.create(Dafny.Sequence<Std.JSON.Grammar._ISuffixed<Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__>>.FromElements(), (_729_open).dtor_cs);
        if ((((_729_open).dtor_cs).Peek()) == ((short)(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE))) {
          Std.JSON.Utils.Parsers._IParser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError> _731_p = Std.JSON.Utils.Parsers.Parser__<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Close);
          Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _732_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Utils.Views.Core._IView__>((_729_open).dtor_cs, _731_p);
          if ((_732_valueOrError1).IsFailure()) {
            return (_732_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>>();
          } else {
            Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Utils.Views.Core._IView__>> _733_close = (_732_valueOrError1).Extract();
            return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.ZeroCopy.Deserializer.Arrays.__default.BracketedFromParts(_729_open, _730_elems, _733_close));
          }
        } else {
          return Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Elements(json, _729_open, _730_elems);
        }
      }
    }
    public static Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>> SpecViewOpen { get {
      return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView;
    } }
    public static Func<Std.JSON.Utils.Views.Core._IView__, Dafny.ISequence<byte>> SpecViewClose { get {
      return Std.JSON.ZeroCopy.Deserializer.Core.__default.SpecView;
    } }
    public static byte SEPARATOR { get {
      return (byte)((new Dafny.Rune(',')).Value);
    } }
  }

  public partial class jopen {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.OPEN));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.ZeroCopy.Deserializer.Arrays.jopen.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Std.JSON.Utils.Views.Core._IView__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(Dafny.Sequence<byte>.FromElements(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE));
    public static Std.JSON.Utils.Views.Core._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TYPE = new Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__>(Std.JSON.ZeroCopy.Deserializer.Arrays.jclose.Default());
    public static Dafny.TypeDescriptor<Std.JSON.Utils.Views.Core._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Arrays
namespace Std.JSON.ZeroCopy.Deserializer.Constants {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Constant(Std.JSON.Utils.Cursors._ICursor__ cs, Dafny.ISequence<byte> expected)
    {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ICursor__, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _734_valueOrError0 = (cs).AssertBytes<Std.JSON.Errors._IDeserializationError>(expected, 0U);
      if ((_734_valueOrError0).IsFailure()) {
        return (_734_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>>();
      } else {
        Std.JSON.Utils.Cursors._ICursor__ _735_cs = (_734_valueOrError0).Extract();
        return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success((_735_cs).Split());
      }
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Constants
namespace Std.JSON.ZeroCopy.Deserializer.Values {

  public partial class __default {
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> Value(Std.JSON.Utils.Cursors._ICursor__ cs) {
      short _736_c = (cs).Peek();
      if ((_736_c) == ((short)((new Dafny.Rune('{')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _737_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.Objects.__default.Object(cs, Std.JSON.ZeroCopy.Deserializer.Values.__default.ValueParser(cs));
        if ((_737_valueOrError0).IsFailure()) {
          return (_737_valueOrError0).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _let_tmp_rhs32 = (_737_valueOrError0).Extract();
          Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IjKeyValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _738_obj = _let_tmp_rhs32.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _739_cs_k = _let_tmp_rhs32.dtor_cs;
          Std.JSON.Grammar._IValue _740_v = Std.JSON.Grammar.Value.create_Object(_738_obj);
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> _741_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(_740_v, _739_cs_k);
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_741_sp);
        }
      } else if ((_736_c) == ((short)((new Dafny.Rune('[')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _742_valueOrError1 = Std.JSON.ZeroCopy.Deserializer.Arrays.__default.Array(cs, Std.JSON.ZeroCopy.Deserializer.Values.__default.ValueParser(cs));
        if ((_742_valueOrError1).IsFailure()) {
          return (_742_valueOrError1).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__>> _let_tmp_rhs33 = (_742_valueOrError1).Extract();
          Std.JSON.Grammar._IBracketed<Std.JSON.Utils.Views.Core._IView__, Std.JSON.Grammar._IValue, Std.JSON.Utils.Views.Core._IView__, Std.JSON.Utils.Views.Core._IView__> _743_arr = _let_tmp_rhs33.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _744_cs_k = _let_tmp_rhs33.dtor_cs;
          Std.JSON.Grammar._IValue _745_v = Std.JSON.Grammar.Value.create_Array(_743_arr);
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> _746_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(_745_v, _744_cs_k);
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_746_sp);
        }
      } else if ((_736_c) == ((short)((new Dafny.Rune('\"')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _747_valueOrError2 = Std.JSON.ZeroCopy.Deserializer.Strings.__default.String(cs);
        if ((_747_valueOrError2).IsFailure()) {
          return (_747_valueOrError2).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijstring> _let_tmp_rhs34 = (_747_valueOrError2).Extract();
          Std.JSON.Grammar._Ijstring _748_str = _let_tmp_rhs34.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _749_cs_k = _let_tmp_rhs34.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(Std.JSON.Grammar.Value.create_String(_748_str), _749_cs_k));
        }
      } else if ((_736_c) == ((short)((new Dafny.Rune('t')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _750_valueOrError3 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.TRUE);
        if ((_750_valueOrError3).IsFailure()) {
          return (_750_valueOrError3).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs35 = (_750_valueOrError3).Extract();
          Std.JSON.Utils.Views.Core._IView__ _751_cst = _let_tmp_rhs35.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _752_cs_k = _let_tmp_rhs35.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(Std.JSON.Grammar.Value.create_Bool(_751_cst), _752_cs_k));
        }
      } else if ((_736_c) == ((short)((new Dafny.Rune('f')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _753_valueOrError4 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.FALSE);
        if ((_753_valueOrError4).IsFailure()) {
          return (_753_valueOrError4).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs36 = (_753_valueOrError4).Extract();
          Std.JSON.Utils.Views.Core._IView__ _754_cst = _let_tmp_rhs36.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _755_cs_k = _let_tmp_rhs36.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(Std.JSON.Grammar.Value.create_Bool(_754_cst), _755_cs_k));
        }
      } else if ((_736_c) == ((short)((new Dafny.Rune('n')).Value))) {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _756_valueOrError5 = Std.JSON.ZeroCopy.Deserializer.Constants.__default.Constant(cs, Std.JSON.Grammar.__default.NULL);
        if ((_756_valueOrError5).IsFailure()) {
          return (_756_valueOrError5).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Utils.Views.Core._IView__> _let_tmp_rhs37 = (_756_valueOrError5).Extract();
          Std.JSON.Utils.Views.Core._IView__ _757_cst = _let_tmp_rhs37.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _758_cs_k = _let_tmp_rhs37.dtor_cs;
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(Std.JSON.Grammar.Value.create_Null(_757_cst), _758_cs_k));
        }
      } else {
        Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>> _759_valueOrError6 = Std.JSON.ZeroCopy.Deserializer.Numbers.__default.Number(cs);
        if ((_759_valueOrError6).IsFailure()) {
          return (_759_valueOrError6).PropagateFailure<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>>();
        } else {
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._Ijnumber> _let_tmp_rhs38 = (_759_valueOrError6).Extract();
          Std.JSON.Grammar._Ijnumber _760_num = _let_tmp_rhs38.dtor_t;
          Std.JSON.Utils.Cursors._ICursor__ _761_cs_k = _let_tmp_rhs38.dtor_cs;
          Std.JSON.Grammar._IValue _762_v = Std.JSON.Grammar.Value.create_Number(_760_num);
          Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue> _763_sp = Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar._IValue>.create(_762_v, _761_cs_k);
          return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.create_Success(_763_sp);
        }
      }
    }
    public static Std.JSON.Utils.Parsers._ISubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError> ValueParser(Std.JSON.Utils.Cursors._ICursor__ cs) {
      Func<Std.JSON.Utils.Cursors._ICursor__, bool> _764_pre = Dafny.Helpers.Id<Func<Std.JSON.Utils.Cursors._ICursor__, Func<Std.JSON.Utils.Cursors._ICursor__, bool>>>((_765_cs) => ((System.Func<Std.JSON.Utils.Cursors._ICursor__, bool>)((_766_ps_k) => {
        return ((_766_ps_k).Length()) < ((_765_cs).Length());
      })))(cs);
      Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>> _767_fn = Dafny.Helpers.Id<Func<Func<Std.JSON.Utils.Cursors._ICursor__, bool>, Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>>>>((_768_pre) => ((System.Func<Std.JSON.Utils.Cursors._ICursor__, Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IValue>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>>)((_769_ps_k) => {
        return Std.JSON.ZeroCopy.Deserializer.Values.__default.Value(_769_ps_k);
      })))(_764_pre);
      return Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>.create(_767_fn);
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.Values
namespace Std.JSON.ZeroCopy.Deserializer.API {

  public partial class __default {
    public static Std.JSON.Errors._IDeserializationError LiftCursorError(Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError> err) {
      Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError> _source24 = err;
      if (_source24.is_EOF) {
        return Std.JSON.Errors.DeserializationError.create_ReachedEOF();
      } else if (_source24.is_ExpectingByte) {
        byte _770___mcc_h0 = _source24.dtor_expected;
        short _771___mcc_h1 = _source24.dtor_b;
        short _772_b = _771___mcc_h1;
        byte _773_expected = _770___mcc_h0;
        return Std.JSON.Errors.DeserializationError.create_ExpectingByte(_773_expected, _772_b);
      } else if (_source24.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _774___mcc_h2 = _source24.dtor_expected__sq;
        short _775___mcc_h3 = _source24.dtor_b;
        short _776_b = _775___mcc_h3;
        Dafny.ISequence<byte> _777_expected__sq = _774___mcc_h2;
        return Std.JSON.Errors.DeserializationError.create_ExpectingAnyByte(_777_expected__sq, _776_b);
      } else {
        Std.JSON.Errors._IDeserializationError _778___mcc_h4 = _source24.dtor_err;
        Std.JSON.Errors._IDeserializationError _779_err = _778___mcc_h4;
        return _779_err;
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>, Std.JSON.Errors._IDeserializationError> JSON(Std.JSON.Utils.Cursors._ICursor__ cs) {
      return Std.Wrappers.Result<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>, Std.JSON.Utils.Cursors._ICursorError<Std.JSON.Errors._IDeserializationError>>.MapFailure<Std.JSON.Errors._IDeserializationError>(Std.JSON.ZeroCopy.Deserializer.Core.__default.Structural<Std.JSON.Grammar._IValue>(cs, Std.JSON.Utils.Parsers.Parser__<Std.JSON.Grammar._IValue, Std.JSON.Errors._IDeserializationError>.create(Std.JSON.ZeroCopy.Deserializer.Values.__default.Value)), Std.JSON.ZeroCopy.Deserializer.API.__default.LiftCursorError);
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._IDeserializationError> Text(Std.JSON.Utils.Views.Core._IView__ v) {
      Std.Wrappers._IResult<Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>, Std.JSON.Errors._IDeserializationError> _780_valueOrError0 = Std.JSON.ZeroCopy.Deserializer.API.__default.JSON(Std.JSON.Utils.Cursors.Cursor__.OfView(v));
      if ((_780_valueOrError0).IsFailure()) {
        return (_780_valueOrError0).PropagateFailure<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>();
      } else {
        Std.JSON.Utils.Cursors._ISplit<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>> _let_tmp_rhs39 = (_780_valueOrError0).Extract();
        Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> _781_text = _let_tmp_rhs39.dtor_t;
        Std.JSON.Utils.Cursors._ICursor__ _782_cs = _let_tmp_rhs39.dtor_cs;
        Std.Wrappers._IOutcomeResult<Std.JSON.Errors._IDeserializationError> _783_valueOrError1 = Std.Wrappers.__default.Need<Std.JSON.Errors._IDeserializationError>((_782_cs).EOF_q, Std.JSON.Errors.DeserializationError.create_ExpectingEOF());
        if ((_783_valueOrError1).IsFailure()) {
          return (_783_valueOrError1).PropagateFailure<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>();
        } else {
          return Std.Wrappers.Result<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._IDeserializationError>.create_Success(_781_text);
        }
      }
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._IDeserializationError> OfBytes(Dafny.ISequence<byte> bs) {
      Std.Wrappers._IOutcomeResult<Std.JSON.Errors._IDeserializationError> _784_valueOrError0 = Std.Wrappers.__default.Need<Std.JSON.Errors._IDeserializationError>((new BigInteger((bs).Count)) < (Std.BoundedInts.__default.TWO__TO__THE__32), Std.JSON.Errors.DeserializationError.create_IntOverflow());
      if ((_784_valueOrError0).IsFailure()) {
        return (_784_valueOrError0).PropagateFailure<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>>();
      } else {
        return Std.JSON.ZeroCopy.Deserializer.API.__default.Text(Std.JSON.Utils.Views.Core.View__.OfBytes(bs));
      }
    }
  }
} // end of namespace Std.JSON.ZeroCopy.Deserializer.API
namespace Std.JSON.ZeroCopy.Deserializer {

} // end of namespace Std.JSON.ZeroCopy.Deserializer
namespace Std.JSON.ZeroCopy.API {

  public partial class __default {
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Serialize(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js) {
      return Std.Wrappers.Result<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError>.create_Success((Std.JSON.ZeroCopy.Serializer.__default.Text(js)).Bytes());
    }
    public static Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> SerializeAlloc(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js)
    {
      Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> bs = Std.Wrappers.Result<byte[], Std.JSON.Errors._ISerializationError>.Default(new byte[0]);
      Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> _out9;
      _out9 = Std.JSON.ZeroCopy.Serializer.__default.Serialize(js);
      bs = _out9;
      return bs;
    }
    public static Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> SerializeInto(Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> js, byte[] bs)
    {
      Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> len = Std.Wrappers.Result<uint, Std.JSON.Errors._ISerializationError>.Default(0);
      Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> _out10;
      _out10 = Std.JSON.ZeroCopy.Serializer.__default.SerializeTo(js, bs);
      len = _out10;
      return len;
    }
    public static Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._IDeserializationError> Deserialize(Dafny.ISequence<byte> bs) {
      return Std.JSON.ZeroCopy.Deserializer.API.__default.OfBytes(bs);
    }
  }
} // end of namespace Std.JSON.ZeroCopy.API
namespace Std.JSON.ZeroCopy {

} // end of namespace Std.JSON.ZeroCopy
namespace Std.JSON.API {

  public partial class __default {
    public static Std.Wrappers._IResult<Dafny.ISequence<byte>, Std.JSON.Errors._ISerializationError> Serialize(Std.JSON.Values._IJSON js) {
      Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError> _785_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
      if ((_785_valueOrError0).IsFailure()) {
        return (_785_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> _786_js = (_785_valueOrError0).Extract();
        return Std.JSON.ZeroCopy.API.__default.Serialize(_786_js);
      }
    }
    public static Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> SerializeAlloc(Std.JSON.Values._IJSON js)
    {
      Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> bs = Std.Wrappers.Result<byte[], Std.JSON.Errors._ISerializationError>.Default(new byte[0]);
      Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> _787_js;
      Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError> _788_valueOrError0 = Std.Wrappers.Result<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError>.Default(Std.JSON.Grammar.Structural<Std.JSON.Grammar._IValue>.Default(Std.JSON.Grammar.Value.Default()));
      _788_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
      if ((_788_valueOrError0).IsFailure()) {
        bs = (_788_valueOrError0).PropagateFailure<byte[]>();
        return bs;
      }
      _787_js = (_788_valueOrError0).Extract();
      Std.Wrappers._IResult<byte[], Std.JSON.Errors._ISerializationError> _out11;
      _out11 = Std.JSON.ZeroCopy.API.__default.SerializeAlloc(_787_js);
      bs = _out11;
      return bs;
    }
    public static Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> SerializeInto(Std.JSON.Values._IJSON js, byte[] bs)
    {
      Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> len = Std.Wrappers.Result<uint, Std.JSON.Errors._ISerializationError>.Default(0);
      Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> _789_js;
      Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError> _790_valueOrError0 = Std.Wrappers.Result<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._ISerializationError>.Default(Std.JSON.Grammar.Structural<Std.JSON.Grammar._IValue>.Default(Std.JSON.Grammar.Value.Default()));
      _790_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
      if ((_790_valueOrError0).IsFailure()) {
        len = (_790_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      _789_js = (_790_valueOrError0).Extract();
      Std.Wrappers._IResult<uint, Std.JSON.Errors._ISerializationError> _out12;
      _out12 = Std.JSON.ZeroCopy.API.__default.SerializeInto(_789_js, bs);
      len = _out12;
      return len;
    }
    public static Std.Wrappers._IResult<Std.JSON.Values._IJSON, Std.JSON.Errors._IDeserializationError> Deserialize(Dafny.ISequence<byte> bs) {
      Std.Wrappers._IResult<Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue>, Std.JSON.Errors._IDeserializationError> _791_valueOrError0 = Std.JSON.ZeroCopy.API.__default.Deserialize(bs);
      if ((_791_valueOrError0).IsFailure()) {
        return (_791_valueOrError0).PropagateFailure<Std.JSON.Values._IJSON>();
      } else {
        Std.JSON.Grammar._IStructural<Std.JSON.Grammar._IValue> _792_js = (_791_valueOrError0).Extract();
        return Std.JSON.Deserializer.__default.JSON(_792_js);
      }
    }
  }
} // end of namespace Std.JSON.API
namespace Std.JSON {

} // end of namespace Std.JSON
namespace Std {

} // end of namespace Std
