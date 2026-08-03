# Terminal alternating-label boundary

`FiniteMixedSideTerminalAlternatingLabelData` replaces the arithmetic inputs
`targetIndex_even` and `pathCard_odd` by the literal alternating colouring of
the terminal path.

For each target, the data records the colour side containing the obstruction
target and terminal endpoints, together with the equivalence between membership
in that side and even path index. The Lean development derives:

- evenness of the canonical nearest-target index; and
- odd cardinality of the terminal path from the last endpoint index.

The next constructor task is to obtain this labelled terminal path directly
from the component path selected by the Definition 19 stopping history. The
remaining independent obligations are the positive final-hole degree-three
statement, the one-sided clone-to-flank adjacency, and the unequal-centre
bounded propagation trace.
