# uls

Roc with [unspecialized lambda set variables](https://www.notion.so/rwx/Non-linear-monomorphization-0b26991a028949a285ca77a8ffcff3c5#1930c4eadf08465f9c7b96469f11f664).

Has:

- closures
- prototypes (to represent abilities)
- variables
- isomorphic types (i.e. `Ack` is a value has the unique type `Ack`)
    - `()` is syntax sugar for `Unit`.
- types: functions, lambda sets, ints

that should be enough to emulate how unspecialized lambda sets, and their
specialization, would work in Roc.

[See the tests](./test/) for examples.

Target phases: `parse`, `solve`, `mono`
Target emit: `print`, `elab`

## Idea

TODO: enumerate the algorithm
