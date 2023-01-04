---
title: Can classes appear in specs?
---

## Question

Can classes appear in specs?

## Answer

Class types can be argument types for a method or function and the corresponding formal parameter can then be mentioned in specs.
Within the specs, you can call functions (ghost or not) of those classes.

However, there are some limitations:
- Primarily, the `new` operator may not be used in a specification, so new class objects cannot be allocated in the spec
- Note also that class objects are on the heap; as heap objects they will need to be mentioned in reads clauses.
