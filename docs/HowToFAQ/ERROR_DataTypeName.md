---
title: "Error: name of datatype (String) is used as a function?"
---

How do I fix this error message: "name of datatype (String) is used as a function"?

```dafny
module MString {
  export provides String
  datatype String = String(s: string)
}
module MX {
  import opened MString
  const S := String("asd")
}
```

The names visible in module `MX` are the datatype `String` but not its constructor, since 
the dataype is only imported as `provides`.
Consequently, the only option for the name `String` in module `MX` is that datatype, 
which then causes the error message.

The fix to this is to declare the export as `export reveals String`.
If `String` is meant to be opaque (only provided) then you cannot construct elements of it; 
if it is meant to be transparent, then you must reveal it.
