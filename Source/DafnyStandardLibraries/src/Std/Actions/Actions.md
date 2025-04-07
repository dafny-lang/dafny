# The `Actions` module

This module defines a hierarchy of action types.

## GenericAction<I, O>

A trait to express any imperative action in Dafny.
This is essentially a reflective interface for a method,
with all possible specifications attached.
It can also be thought of as the logical last step
in the progression of arrow types,
from the total, heap-independent `->`,
to the partial but still heap-independent `-->`,
to the heap-reading `~>`.
A generic action is thus like a function that can also modify the heap.

(The behavior of a generic action may also be non-deterministic,
but this case seems less useful in practice,
so the definition of a MostlyGenericAction
that may only modify the heap deterministically
is left as an invitation to the sufficiently motivated Dafny contributor!)

The more specific `Action` trait can be much more pleasant to use
when composing non-interferring actions together,
such as working with enumerators or streams,
as they make simplifying assumptions that are true for many reusable actions.
However, this more general action may be more flexible
when accepting any kind of callback in a higher-order method.

## Action<I, O>

A composable imperative action.
  
Specializes `GenericAction` to assume its behavior can be specified
independently from most other actions,
and therefore fits into the `Valid()`/`Repr` idiom
(and hence extends the `Validatable` trait).
Its specified behavior is allowed to depend on only
what inputs it consumed and outputs it produced in the past.

A key design point for making this possible in Dafny:
the `ValidInput` and `ValidHistory` predicates,
which the action's specification of behavior are drawn from,
specifically avoid reading the current state of the action.
That is so extrinsic properties of an action do NOT depend on their current state.
This is key to ensure that you can prove properties of a given action that
will continue to hold as the Dafny heap changes.
This approach works because Dafny understands that for a given object,
the implementation of these predicates cannot change over time.

The downside is that these are then forced to use quantifiers
to talk about all possible states of an action.
The solution is the trait proof pattern,
where a trait is passed around with an abstract lemma
that can be invoked on the otherwise quantified state as needed.
See [`TotalActionProof`](Actions.dfy) as an example for details.

This trait is intended to be applicable for any imperative action
regardless of how many input or output values it consumes and produces,
despite only defining two type parameters.
Implementors should feel free to use the `()` unit type or tuple types
for `I` and `O`, under the assumption that
future Dafny backends will be able to easily optimize
away the overhead of passing around a pointless `()` value
or wrapping up multiple values into a tuple.

## Errors

Because the Action trait is so general,
there are many error producing and handling patterns that
can be expressed, even within the same type signature:

1. An `Action<I, Option<O>>` can produce None to indicate there is no value,
    but the action could still be called again. Similarly a `Result<O, E>`
    output could indicate a failure that is only related to that invocation.
2. An `Action<I, Option<O>>` could also produce None to indicate the action
    is "exhausted" and cannot produce any more values.
    This is the basis for the `Producer<T>` specialization.
    Similarly a `Result<O, E>` could indicate the action is broken
    for abnormal reasons and can't be called again.
3. An `Action<I, Option<Result<O, E>>` can indicate both cases independently:
    a `Some(Success(O))` provides another value, 
    a `None` indicate no more values,
    and a `Some(Failure(E))` indicates an error.
    The error could be fatal or recoverable depending on the protocol.
4. For even better readability, it is often better to declare a more specialized datatype,
    such as
    
    <!-- %no-check -->
    ```dafny
    datatype DataStreamEvent = 
      | NoData 
      | Done 
      | Data(values: bytes)
      | BadData(error: string)
      | FatalError(error: string)
    ```

    along with rules for what sequences of these values are valid
    (e.g. once `Done` appears no other constructors can appear,
    and perhaps if you get a `FatalError` the `ValidInput` constraints
    don't even let you invoke the action again)

The key point in distinguishing these semantics 
is how `ValidInput`, `ValidOutput`, and `ValidHistory` are constrained, 
defining the protocol for using the action across time,
depending on what inputs and outputs occur.
All of the above cases are useful for precisely modeling behavior over time,
and so this library provides explicit specializations for some common patterns
but allows for basically any well-founded approach.

## Specializations

In practice, many actions fit into a more specific version of this concept.
See the other sibling files for some useful specializations:

| Type           | Supertype               | Behavior                                                        |
| -------------- | ----------------------- | --------------------------------------------------------------- |
| `IProducer<T>` | `Action<(), T>`         | consumes nothing, may produce an infinite number of values      |
| `Producer<T>`  | `Action<(), Option<T>>` | consumes nothing, must produce a finite number of values        |
| `IConsumer<T>` | `Action<T, ()>`         | produces nothing, may consume an infinite number of values      |
| `Consumer<T>`  | `Action<T, boolean>`    | produces nothing, must consume a finite number of values        |

These concepts are roughly duals to each other (`IProducer`/`IConsumer`, and `Producer`/`Consumer`).
The generic signatures of `Producer` and `Consumer` are not exact mirror-images
because in both cases they must produce an additional piece of boolean information
about whether they are "exhausted".

In practice, the most common traits will usually be `Producer` and `IConsumer`. 
That is, most data sources in real programs tend to produce finite elements,
and it's usually impractical and/or unnecessary to specify how many statically,
but most data sinks tend to have no constraints.
  