# The Lean proof of «The Coloured Sand Theorem»

This folder holds the Lean 4 proof (with Mathlib) of every theorem of «The Coloured Sand Theorem»: Theorems A–J, for every prime. The proof uses no `sorry`, no `native_decide` and no axiom beyond Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`). Nothing is cited from outside Lean and Mathlib.

## What is proved

The object is the sandpile group `K(H(d, q))` of the Hamming graph `H(d, q)`, defined in `RequestProject/Splitting/Basic.lean` and `RequestProject/TheoremB/Basic.lean`. The two headline statements are:

- **Every odd prime `p` dividing `q`, every `d`:** `ColouredSand.OddTwist.oddTotal_S2` (`RequestProject/OddTotal/Sylow.lean`). The `p`-primary part of `K(H(d, q))` is an explicit direct sum of cyclic groups (Theorem J of the paper).
- **The prime 2, every even `q`, every `d`:** `ColouredSand.ThmH.T4` (`RequestProject/ThmH/TheoremH.lean`), Theorem H of the paper.

Theorems A–G and I, Lemmas 2–5, 7 and 8, Corollaries 1 and 6 and Example 9 are proved too, each for every prime. The cases `p = 2` of Theorems F, G and I and the case `p ∤ q` of Theorem E were added last, in the folders `ThmGTwo`, `TwoTheoremI` and `StringsAll`.

## How it was checked

The proof was built in 36 pieces. Each piece was written by Aristotle (Harmonic) from a statement taken from the paper, compiled on the author's machine and audited: the auditor restated every result by hand in a check file and printed its axioms.

- `checks/pieces/`: the 36 check files, one per piece.
- `checks/final/`: the final check. It is six files (`CheckColouredSandFinal2A1` to `A5` and `CheckColouredSandFinal2B`); each one imports all 36 pieces, so the whole proof is checked in one environment. Each piece's check file goes inside its own namespace unchanged. Together they print 451 `#print axioms` answers, all within the three standard axioms.
- `checks/final/DepsColouredSand2.lean`: the dependency cone of the headline theorems. Their union uses 9 833 declarations of this project, in 335 modules.

Size (the 36 pieces): 254 files, 46 787 lines, 2 370 `theorem`/`lemma` lines, 0 `sorry`. `RequestProject/` holds the 438 modules imported by the final check, among them modules of the Dancing Sand proof that the Coloured Sand uses.

## Rebuild it yourself

GitHub's machines rebuild everything from these files with the workflow `.github/workflows/lean-build.yml` («Lean build» in the Actions tab). On your own machine, with [elan](https://github.com/leanprover/elan) installed:

```
cd lean/project
lake exe cache get
lake build
lake env lean checks/final/CheckColouredSandFinal2A1.lean
```

and the same for `A2`–`A5`, `B` and `DepsColouredSand2.lean`. Toolchain: `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` (pinned in `lake-manifest.json`).
