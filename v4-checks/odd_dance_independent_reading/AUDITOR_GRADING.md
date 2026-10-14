# Grading of the cold reader «Grepy el Jurado» (COLOURED_SAND_2) — the odd dance
Grepy Sand, Tue Oct 13 2026, 23:05–23:15 CEST (times from `date`).

**Under grading:** `JURADO_1/REPORT_COLOURED_SAND_2.md` (md5 `707930f1ea19af0266ba7ce8870099ab`, 481 lines), copied with its whole `checks/` folder from `~/Desktop/LECTORES_EN_FRIO/COLOURED_SAND_2/` (manifest `JURADO_1/MANIFEST_md5.txt`, 499 files). Its full proof of the odd-p floor: `JURADO_1/checks/THEOREM_F_ODD_P.md` (md5 `9ef0c04203217e82571ddc796576ca8a`). It reads the Bailarín report `REPORT.md` (md5 `d9c2f1ab…`).

## Verdict of the reader
**HOLDS WITH CORRECTIONS.** No error, no gap, no counterexample. The corrections are of presentation, citation and priority.

## Grade: HIGH MARK
- **Every row is a derivation, not a stamp.** I read R1–R11 and the whole of `THEOREM_F_ODD_P.md`. R2 writes out the `[E,F]` cases of `Φ_p` and gives the closed `E^{(r)}`. R3 does all ten index ranges of `Ψ_r`, the two `F`-identities of `ι` and the Casimir/Lucas argument. R6 checks every pivot, sign and shape of the moves. R8 re-derives the windows, the deficit law and the cost form. R9 writes the odd-p floor (Theorem F_p) as a full eight-step induction and then checks the Bailarín's list of changes item by item.
- **The riskiest step is now a proof.** The Bailarín's Theorem 4.4 was only a list of changes to [DST] §7. The reader expanded it into a full proof. Every listed change is right, including the claim that the DIG windows fall into cases 3(b) and 3(d). It found one missing fact, (O1): the o-order of `o_D = Σ d_t p^t` is the binary order of the digit sets. (O1) is true and is now stated with its one-line proof.
- **Own engines with live controls:**
  - K1: 569 lattices; the closed `E^{(r)}` on 273 812 pairs.
  - K2: 62 identifications `L(λ)⊗𝔽_p ≅ T(λ)` without Donkin.
  - **K3: 31 of 31 sealed direct Smith forms beyond the published range, 0 disagreements.**
  - K4: about 34 000 cells.
  - K5: 12 whole Hamming groups up to `d = 60`, against Kirchhoff and the 𝔽_p-rank.
  - K6: 47 310 houses.
- **Literature (JOB 3):** a wide sweep. The engines reached are listed, and so are the ones it could not reach (Semantic Scholar, BASE, OATD, and Google Scholar not directly). Nothing is CONTRADICTED. Two priority facts must be stated:
  - **d = 2 of Theorem TOTAL is Ducey–Gerhard–Watson 2016** (already known from the Tamiz).
  - **The existence of the ℤ_p tilting lattices and the lifting of the decompositions are classical** (Andersen 1997 §1.2; Jantzen E.19–E.22). New: the explicit lattices, the odd moves, Theorem D_p, Theorem I, the cost form, Theorem F_p, Theorem TOTAL for `d ≥ 3`.
- **Honest about itself.** Slips it disclosed:
  - one `rm` of an empty file it had just made;
  - four guessed time stamps, corrected from `date`;
  - six short runs started before their estimate, one of them outside the watchdog;
  - six watchdog kills, never used as results.

  Not done: it did not re-prove [DST] (`p = 2`).
- Two slips keep it below HIGHEST: the `rm` and the run outside the watchdog. They break the rules but touch no result.

## My own checks (re-runs of its scripts, my copy, my watchdog)
In `JURADO_1/rerun_auditor/`:
- `k1.py 3 60`: identical to its smoke log; 0 s, 7 MB.
- `k5.py 13`: 12 Hamming groups AGREE, control fires, identical to its `k5.log`; 8 s, 136 MB.
- `k6.py 3:1 3:2 3:3`: 1 638 houses, no failure, all four window types present, identical counts; 1 s, 15 MB.

Independent of it: my own gate of the closed formulas of `Φ_p` for piece CSI1 (`../lean/chk/chkCSI1.py`, 15 676 checks, 0 failures). It uses its form of `E^{(r)}`, in my implementation.

## What this changes in the registers
- **Theorem I (Conjecture I of v3, every prime) and Theorem TOTAL (`Syl_p K(H(d,q))` for every `p | q`, every `d`): PROVED by pencil, two readers (constructor + external cold reader), NOT in Lean.**
  - For `p = 2` they rest on [DST], same author, in Lean, not re-read here.
  - They cite Donkin's tensor product theorem and the Krull–Schmidt classification of tilting modules. K2 identifies 62 cases without Donkin; Lean stage 4 must avoid the citation.
- **For v4** (Rafa's order: one Lean certificate first, then v4):
  - write Theorem F_p in full with (O1);
  - write the closed `E^{(r)}`;
  - name Weyl's theorem in Lemma 1.0;
  - cite precisely: STWZ Prop. 3.4(a); Andersen 1997 Remark 1.1(ii), §1.2; Jantzen E.6, E.19–E.22;
  - credit Ducey–Gerhard–Watson for `d = 2`;
  - say the existence of ℤ_p tilting lattices is classical;
  - lower the grade of claim #15 as written at the time.
- **Side note, not for this project:** D. Betzer, Zenodo 10.5281/zenodo.22065778 (23 Aug 2026), claims GMMY Conj. 4.14 for the hypercube. That is relevant to the cube paper's priority list ([DST] §1.8) and belongs to the cube's auditor.

## Next
Lean stage 4, piece CSI1 (the odd twist `Φ_p`, `lean/CSI1_the_odd_twist.md`), sent to Aristotle on Rafa's order of 13 Oct 23:05.
