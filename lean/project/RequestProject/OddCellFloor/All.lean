module

public import RequestProject.OddCellFloor.Basic
public import RequestProject.OddCellFloor.Integrality
public import RequestProject.OddCellFloor.Floor

/-!
# `CSI17_integrality_and_cell_floor_at_p.md` — integrality (Lemma 7.9_p) and the floor of every
cell (Theorem 7.10_p, house form)

Index of the formalization (namespace `ColouredSand.OddTwist`), the base-`p` analogue of C9
(`RequestProject/CellFloor/`).

## Reused, not redefined
C1 (`AntitonicFit.fit`, `ifit`, `toR`, `IsCut`, `IsStrictCut`, Lemma 7.2), C2
(`SmithBounds.NonIncrOn`, `tailSum`, `IsRMatching`, `theorem_U`), C7 (`TheoremF.dancer`,
Lemma 0), C9 (`CellFloor.IsCellArrow`, `CellFloor.IsSharpArrow` — both depend only on `I` —,
`CellFloor.ifit_eq_of_fit_eq_int`, `CellFloor.fit_one`, `CellFloor.dancer_inj`,
`CellFloor.nonIncrOn_cast_real`), CSI15 (`JHP`, `cHatHP`, `typP`, `thetaP`, `typP_OR_iff_digit`)
and CSI16 (`xHseqP`, `JHseqP`, `yhatP`, `cHatSeqP`, `IsPotentialP`, `JHseqP_mono`, `oddF_J0`,
`oddF_W3`, `oddF_F1_Cut`, `oddF_theorem_F`).

## Encodings (details in `Basic.lean`)
* prime `p` with `[Fact p.Prime]`; house `(I, k, ℓ, e, dg)` unbundled, conditions as hypotheses
  `hI`, `hℓ : ℓ < p ^ k`, `hd`, `he : 1 ≤ e`; `N = 2 ^ #I`; sequences are `ℕ → ℤ` read on `[0, N)`.
* penalties `Pr Pc : ℕ` with no relation assumed; `oddCellClock` (clocks `z`), `oddCellCost`
  (costs), `oddCellPenal V … P = V − P·J_H` (`v`, `w` of Part B); `oddCellXSharp` (`x^♯`),
  `oddCellYhatSharp` (`ŷ^♯`), `oddCellCostSharp` (`cost^♯`).
* `ℓ = p^k − 1` is `hℓ' : ℓ = p ^ k - 1`, `I ≠ ∅` is `hne : I.Nonempty`.

## Where each statement is
* *Part A* (`Integrality.lean`), **Lemma 7.9_p**: (I1) `oddCell_lemma_7_9_I1`; (I2)
  `oddCell_lemma_7_9_I2`; (I3) `oddCell_lemma_7_9_I3` (types all OR / `θ_t = 1`,
  `J_H(q) = [q ≠ 0]`, strict cut at `1`, the restricted real and integer fits, integrality).
* *Part B* (`Floor.lean`): (U1) `oddCell_B_U1`, (U2) `oddCell_B_U2`, (U3) `oddCell_B_U3`,
  together `oddCell_theorem_B`; the consequence via `SmithBounds.theorem_U` is
  `oddCell_theorem_B_floor`.
* *Part C* (`Floor.lean`): (U1)–(U3) `oddCell_theorem_C`; the consequence is
  `oddCell_theorem_C_floor`.

## More general than the file
* Everything holds for every prime `p`, including `p = 2`.
* `oddCell_B_U3` needs no house condition; `oddCell_B_U1` only the digit condition.
* The consequences `oddCell_theorem_B_floor`, `oddCell_theorem_C_floor` assume no potential: one
  is supplied by Theorem F_p (`oddF_theorem_F`).
-/
