---
title: "Duplicate name of import: ..."
---

This error results from importing two modules with the same name. For example
```dafny
import A.Util
import B.util
```
In this case, the default name given to the two imports is the same: `Util`.
To give them different names, use the longer form of the import statement
```dafny
import A.Util
import BU = B.Util;
```
Now a name `N` from `A.Util` can  be referred to as `Util.N` and
a name `N` from `B.Util` can be referred to as `BU.N`.
