---
title: How do I make a singleton instance of a class for repeated later use?
---

## Question

How do I make a singleton instance of a class for repeated later use?
In general, one might need to allocate an object, do some initialization,
but then treat it as const from then on.

## Answer

In the following code, the constructor `C()` in `FooUtil` initializes a const value with a 
value of the type `Blah`. Note that the constructor has two phases. In the first, `foo` is assigned a value.
Once assigned, `foo` cannot be assinged again. However, after `new;`, the `foo.update` can be called to 
finish the initialization of `foo`.
```dafny
module M {
    class Blah {
        var x: nat;
        constructor C() {
            x := 0;
        }
        method update() 
            modifies this
        {
            x := 1;
        }

    }
    class FooUtil {
        const foo: Blah;
        constructor C() {
            foo := new Blah.C();
            new;
            foo.update();
        }
    }
}
```

Even in this case, although `foo` is `const`, the fields of `foo` can still be modified, unless the fields of `Blah` are themselves declared `const`.
