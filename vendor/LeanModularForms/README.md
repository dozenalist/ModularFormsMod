# LeanModularForms module compatibility snapshot

The 28 upstream Lean files are the transitive `LeanModularForms` imports needed by
`ModularFormsMod.ModularFormOver.Hecke`. They come from
[`dozenalist/LeanModularForms` at `f737ca88e0887ecbaad3510b30e37042c243fd17`](https://github.com/dozenalist/LeanModularForms/tree/f737ca88e0887ecbaad3510b30e37042c243fd17),
a fork of [Chris Birkbeck's LeanModularForms](https://github.com/CBirkbeck/LeanModularForms).
The original copyright headers and Apache-2.0 licence are retained.
A minimal `LeanModularForms.lean` entry point exports the two required modules.

The upstream snapshot does not use Lean's module system. Lean rejects imports
of those files from a module, and Palomar requires every submitted Lean source
to be a module. This contained Lake package therefore adds `module`, changes
imports to `public import`, and uses `@[expose] public section` to preserve the
existing public declarations and definition bodies. Its declarative Lakefile
uses the same Mathlib commit as the parent project. Any further compatibility
changes are recorded in this directory's Git history.
Its build directory is inside the parent project's `.lake/build` directory so
that both Comparator and Palomar can rebuild it with the source checkout mounted
read-only. Palomar grants writes only to each package's `.lake/build` and
`.lake/config` directories; other locations directly under `.lake` are read-only.

The helpers `HeckeRing.mul_mem_delta`, `diamondOpCuspAux`, and
`natDiagDetNeZero` are made public because exposed definitions or public
statements refer to them. Their mathematical types and bodies are unchanged.
The three proofs `heckeT_p_slash_invariant`, `heckeT_p_holomorphic`, and
`heckeT_p_bdd_at_cusps` are also public so they can supply fields of the exposed
`heckeT_p` definition.
The proof of `HeckeRing.smulOrbit_card` uses an explicit unfolding and `exact`
in place of a `convert` step that fails after the module migration.

This is proof infrastructure only. `Challenge.lean` imports Mathlib directly
and does not import this package or any other project source.
