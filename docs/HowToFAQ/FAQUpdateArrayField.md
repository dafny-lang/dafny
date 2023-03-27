---
title: How do I tell Dafny that a class field may be updated?
---

## Question

I get a "call might violate context's modifies clause" in the following context.
I have a field in a class that is is an array whose elements are being modified by a call, but the field does not exist when the enclosing method
is called. So how do I tell Dafny that it can be modified?

Here is an example situation:
```dafny
class WrapArray {
  var intarray: array<int>; 
  constructor (i:int) 
    requires i > 0
  {
    this.intarray := new int[i];
  }
  method init(i: int)
    modifies intarray
  {
    var index: int := 0;
    while (index < intarray.Length){
      intarray[index] := i;
      index := index+1;
    }
  }
}

method Main()
{
  var sh:= new WrapArray(5);
  sh.init(4);
}
```

## Answer

When dafny is asked to verify this, it complains about the call `sh.init` that it modifies objects that
Main does not allow. Indeed `sh.init` does modify the elements of `sh.intarray` and says so in its `modifies` clause,
but that array does not even exist, nor is `sh` in scope, in the pre-state of `Main`. 
So where should it be indicated that `sh.intarray` may be modified?

The key is in the fact that neither `sh` nor `sh.intarray` is allocated in `Main`'s pre-state. `Main` should be allowed 
to modify objects that are allocated after the pre-state. Indeed `Main` knows that `sh` is newly allocated, so its fields
may be changed. That is, we are allowed to assign to `sh.intarray`. But here we want to change the state of `sh.intarray`,
not `sh`. The array is newly allocated, but `Main` does not know this.
After all, it is possible that the constructor initialized `sh.intarray` with some existing array and changing that array's elements
would change the state of some other object. We need to tell `Main` that the constructor of `WrapArray` allocates a new 
array of ints. The syntax to do that is to add a postcondition to the constructor that says `fresh(intarray)`.

Writing the constructor like this

```dafny
  constructor (i:int)
    requires i>0
    ensures fresh(intarray)
  {
      this.intarray := new int[i];
  }
  
```

solves the problem.
