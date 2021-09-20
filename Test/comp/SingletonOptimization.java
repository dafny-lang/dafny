package Library;

import dafny.*;
import java.math.*;

public class SingletonOptimization {
    // static method SingletonTuple(a: (ghost MyInt, MyInt)) returns (b: (MyInt, ghost MyInt, ghost MyInt))
    public static int SingletonTuple(int a) {
        return a;
    }
}
