# The Lean proof of «The Coloured Sand Theorem»

This folder holds the Lean 4 proof (with Mathlib) of every theorem of «The Coloured Sand Theorem», version 6: Theorems A–J, for every prime. The proof uses no `sorry`, no `native_decide` and no axiom beyond Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`). Nothing is cited from outside Lean and Mathlib.

**Certificate:** [`LEAN_CERTIFICATE_COLOURED_SAND_v2.pdf`](LEAN_CERTIFICATE_COLOURED_SAND_v2.pdf) ([Markdown](LEAN_CERTIFICATE_COLOURED_SAND_v2.md)): the full statements, the definitions they use, what is not certified, the dependency cone and the data of every piece. It is also in the paper's Zenodo record, [doi:10.5281/zenodo.23327608](https://doi.org/10.5281/zenodo.23327608) (all versions).

## What is proved

The object is the sandpile group `K(H(d, q))` of the Hamming graph `H(d, q)`, defined in `project/RequestProject/Splitting/Basic.lean` and `project/RequestProject/TheoremB/Basic.lean`. The two headline statements are:

- **Every odd prime `p` dividing `q`, every `d`:** `ColouredSand.OddTwist.oddTotal_S2` (`project/RequestProject/OddTotal/Sylow.lean`). The `p`-primary part of `K(H(d, q))` is an explicit direct sum of cyclic groups (Theorem J of the paper).
- **The prime 2, every even `q`, every `d`:** `ColouredSand.ThmH.T4` (`project/RequestProject/ThmH/TheoremH.lean`), Theorem H of the paper.

Theorems A–G and I, Lemmas 2–5, 7 and 8, Corollaries 1 and 6 and Example 9 are proved too, each for every prime. The cases `p = 2` of Theorems F, G and I and the case `p ∤ q` of Theorem E were added last, in the folders `ThmGTwo`, `TwoTheoremI` and `StringsAll`.

## What is not formalized

These points are stated in §2 of the certificate; none of them is needed for the statements on `K(H(d, q))`.

- **The lattices.** Theorem I and the block formulas of Theorem J are proved for explicit dance lattices: `L(λ)` for odd `p`, and the dance lattices of the Dancing Sand Theorem for `p = 2` (on which `FamilyGroup.X` is defined). Their identification with the tilting lattices `T_{ℤ_p}(λ)` of the paper, and of the multiplicities of the recursions with those of `T(λ)` in `V^{⊗m}`, is proved in the paper and not in Lean.
- **Theorem E.** The pieces state it for the `ℤ_p`-module `coker(q(c+H)+U)` on `B_m(ℤ_p)`, free summand included. Its form in the paper, for `Syl_p X_q(m,c)`, is checked by the separate file `project/checks/CheckTheoremEPaperForm.lean` (written by a cold reader; standard axioms only), which is not one of the 36 pieces.
- **Example 10** of the paper (the block `λ = 12`, `p = 3`) has no Lean statement; the numerical verification record of the paper is evidence, not part of the proof.

## How it was checked

The proof was built in 36 pieces. Each piece was written by Aristotle (Harmonic) from a statement taken from the paper, compiled on the author's machine and audited: the auditor restated every result by hand in a check file and printed its axioms.

- `project/checks/pieces/`: the 36 check files, one per piece.
- `project/checks/final/`: the final check. It is six files (`CheckColouredSandFinal2A1` to `A5` and `CheckColouredSandFinal2B`); each one imports all 36 pieces, so the whole proof is checked in one environment, and together they repeat every piece's hand restatements. Together they print 451 `#print axioms` answers, all within the three standard axioms.
- `project/checks/final/DepsColouredSand2.lean`: the dependency cone of the headline theorems. Their union uses 9 833 declarations of this project, in 335 modules.
- [`final/`](final/): how the final check was assembled — `assemble_final_v2_partsA.py` and `assemble_final_v2_halves.py`, the md5 of the 36 check files (`MANIFEST_checks_md5_v2.txt`), the table of every piece (`per_piece.tsv`: piece, folder, files, lines, `theorem`/`lemma` lines, check-file statements) and the import closure of the final check (`closure.py`, `closure_modules.txt`). The scripts keep the paths of the author's machine.
- [`actions/`](actions/): the logs of GitHub Actions run [38724562833](https://github.com/tretoef-estrella/coloured-sand-theorem/actions/runs/38724562833) (15 October 2026, commit `51c25f0`, green): the artifact `Final_check_actions_logs.zip` (md5 `f301083f2c3770791fd24ad2db515fba`, SHA-256 `b15a709827b7f7f72372f649fde82cd75f5c5300b65bd97c68cfc0a6c20ffb72`), its eight logs unpacked in `actions/logs/`, and the steps of the job with their times. Their axiom lines are identical, line for line, to those of the runs on the author's machine.

Size (the 36 pieces): 254 files, 46 787 lines, 2 370 `theorem`/`lemma` lines, 0 `sorry`. `project/RequestProject/` holds the 438 modules imported by the final check, among them modules of the Dancing Sand proof that the Coloured Sand uses.

## Rebuild it yourself

GitHub's machines rebuild everything from these files with the workflow [`.github/workflows/lean-build.yml`](../.github/workflows/lean-build.yml) («Lean build» in the Actions tab). The workflow downloads Mathlib's published compiled files (`lake exe cache get`) and builds this project from its sources. On your own machine, with [elan](https://github.com/leanprover/elan) installed:

```
cd lean/project
lake exe cache get
lake build
lake env lean checks/final/CheckColouredSandFinal2A1.lean
```

and the same for `A2`–`A5`, `B`, `DepsColouredSand2.lean` and `checks/CheckTheoremEPaperForm.lean`. Toolchain: `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` (pinned in `lake-manifest.json`).
