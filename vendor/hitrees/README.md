# HITrees core

`src/HITrees/Basic.lean` and `LICENSE` are unmodified copies from
<https://git.ista.ac.at/plv/hitrees>, commit
`3ddf725488a8b2e83af391a1c6ad77796c904865`.

This is the core datatype and monad from *HITrees: Higher-Order Interaction
Trees*, <https://arxiv.org/abs/2510.14558>. Only this dependency-free module is
vendored. The upstream development targets Lean 4.22.0-rc2; this module is checked
with this repository's pinned Lean toolchain. Its BSD-3-Clause notice is retained
in `LICENSE` and applies to this directory.

The DOOM effects, tail-call transition semantics, and replay proofs live in
`Doom/Interaction.lean`; they are project-specific, not the upstream RecE/Exec
library or a port of the original ITree `eutt` theory.
