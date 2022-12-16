package Library;

import dafny.*;
import java.math.*;

public class SingletonOptimization {
    // static method SingletonTuple(a: (ghost MyInt, MyInt)) returns (b: (MyInt, ghost MyInt, ghost MyInt))
    public static int SingletonTuple(int a) {
        return a + 1;
    }
    // static method NoWrapper(a: InvisibleWrapper) returns (b: InvisibleWrapper)
    public static int NoWrapper(int a) {
        return a + 1;
    }
    // static method GhostWrapper(a: Ghost<MyInt>) returns (b: Ghost<MyInt>)
    public static int GhostWrapper(int a) {
        return a + 1;
    }
}
