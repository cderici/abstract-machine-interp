This is a theoretical model implemented in [PLT Redex](https://docs.racket-lang.org/redex/index.html?q=redex) to investigate the relationship between the stack and the heap when an abstract machine and an interpreter work together.

It includes models for a CEK machine and a stackful (regular recursive) interpreter, both implementing a subset of the [Fully Expanded Racket Programs](https://docs.racket-lang.org/reference/syntax-model.html?q=fully%20expanded#%28part._fully-expanded%29).

The main focus is the memory usage. As the expressions go deeper and deeper, the CEK builds up continuations on the heap (which creates a GC pressure in the real world scenario, e.g., [Pycket](https://github.com/pycket/pycket)), while the stackful adds stack frames (in this case to the underlying Redex stack through the recursive meta-function calls).

To share the load between the heap and the stack, we switch back and forth between the two interpreters. While the switch from the CEK to stackful depends on the heap use preference, there are cases where it is mandatory for the stackful to switch to the CEK, such as overflow and continuation capture (because there is no continuation in the stackful).

The investigation is about the trade-offs between these two, and tries to answer questions such as

 * To what extent we can share the load? Can we measure and quantify it?
 * How big is the switch overhead? Can it be bound?
 * What if we had an infinite stack space and only switch because of the continuation captures?

For a related study, see `Hieb, Dybvig, Bruggeman, "Representing Control in the Presence of First-Class Continuations"` ([pdf](https://cs.indiana.edu/~dyb/pubs/stack.pdf))