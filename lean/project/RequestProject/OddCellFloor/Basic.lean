module

public import RequestProject.OddPotential.All
public import RequestProject.CellFloor.All
public import RequestProject.SmithBounds.All

/-!
# `CSI17_integrality_and_cell_floor_at_p.md` — *Setting*: penalty cells of a base-`p` house

Namespace `ColouredSand.OddTwist`.  This is the base-`p` analogue of
`RequestProject/CellFloor/Basic.lean` (C9), built from the base-`p` sequences of CSI16
(`RequestProject/OddPotential/`).  Every new name carries the prefix `oddCell` (or `oddCell_`).

## Encoding

* The prime is `p : ℕ` with `[Fact p.Prime]` (the file's `p` odd is never used: everything also
  holds for `p = 2`).
* A **house** `H = (I, k, ℓ, e, d)` is unbundled, as in CSI15–CSI16: `I : Finset ℕ`, `k ℓ : ℕ`,
  `e : ℤ`, digits `dg : ℕ → ℕ` (`d_t = dg t`); the house conditions are hypotheses
  `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < p ^ k`, `hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1`, `he : 1 ≤ e`
  (each theorem carries only those its proof uses; this is said in its docstring).
* `N = 2^{|I|}` is `2 ^ #I`; positions are natural numbers `q < N`, the dancer at `q` is
  `TheoremF.dancer I q`.  Sequences of length `N` are functions `ℕ → ℤ` (or `ℕ → ℝ`) of which only
  the positions `< N` matter (as in C1, C7, C9, CSI16).
* `x_H = xHseqP p k I dg ℓ e`, `J_H = JHseqP p k I dg ℓ` (in `ℕ`, cast to `ℤ`),
  `ŷ_H = yhatP p k I dg ℓ e = AntitonicFit.ifit N x_H`, `ĉ_H(q, q') = cHatSeqP p k I dg ℓ e q q'`;
  the real fit of an integer sequence `x` is `AntitonicFit.fit N (AntitonicFit.toR x)`; potentials
  are `IsPotentialP p k I dg ℓ e V` (CSI16).
* Penalties `Pr Pc : ℕ`; **no relation between them is assumed**.
  - `oddCellClock p k I dg ℓ e Pr Pc q = x_H(q) − P_r J_H(q) + P_c J_H(N − 1 − q)` (clocks `z`);
  - `oddCellCost p k I dg ℓ e Pr Pc q q' = ĉ_H(q, q') − P_r J_H(q) + P_c J_H(q')` (costs);
  - the cell arrows are C9's `CellFloor.IsCellArrow I q q'`
    (`q < N ∧ q' < N ∧ dancer_I(q') ⊆ dancer_I(q)`, loops included), which depends only on `I`
    and is reused as it is.
* `oddCellPenal V p k I dg ℓ P q = V(q) − P J_H(q)`, so that `v = oddCellPenal V … Pr` and
  `w = oddCellPenal V … Pc` in Part B.
* Part A (I3) and Part C: `oddCellXSharp p k I dg ℓ e j = x_H(j + 1)` is `x^♯` (used with length
  `N − 1`), `oddCellYhatSharp … = ifit_{N−1}(x^♯)` is `ŷ^♯`,
  `oddCellCostSharp … a b = ĉ_H(a + 1, b)` is `cost^♯`, and the arrows are C9's
  `CellFloor.IsSharpArrow I a b` (`a < N − 1 ∧ b < N − 1 ∧ dancer_I(b) ⊆ dancer_I(a + 1)`), which
  depends only on `I`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF

/-- *Setting* of `CSI17_integrality_and_cell_floor_at_p.md`: the **cell clocks** of
`Cell(H; P_r, P_c)`, `z(q) := x_H(q) − P_r J_H(q) + P_c J_H(N − 1 − q)`. -/
def oddCellClock (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (Pr Pc : ℕ) : ℕ → ℤ :=
  fun q => xHseqP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
    (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)

/-- *Setting* of `CSI17_integrality_and_cell_floor_at_p.md`: the **cell costs**
`cost(q, q') := ĉ_H(q, q') − P_r J_H(q) + P_c J_H(q')`. -/
def oddCellCost (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (Pr Pc : ℕ) (q q' : ℕ) :
    ℤ :=
  cHatSeqP p k I dg ℓ e q q' - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
    (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ)

/-- *Part B* of `CSI17_integrality_and_cell_floor_at_p.md`: `q ↦ V(q) − P J_H(q)`; with
`P = P_r` this is `v`, with `P = P_c` it is `w`. -/
def oddCellPenal (V : ℕ → ℤ) (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (P : ℕ) : ℕ → ℤ :=
  fun q => V q - (P : ℤ) * (JHseqP p k I dg ℓ q : ℤ)

/-- *Part A* (I3) of `CSI17_integrality_and_cell_floor_at_p.md`: `x^♯(j) := x_H(j + 1)` (a
sequence of length `N − 1`). -/
def oddCellXSharp (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : ℕ → ℤ :=
  fun j => xHseqP p k I dg ℓ e (j + 1)

/-- *Part C* of `CSI17_integrality_and_cell_floor_at_p.md`: `ŷ^♯ := ifit_{N−1}(x^♯)`. -/
noncomputable def oddCellYhatSharp (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) :
    ℕ → ℤ :=
  ifit (2 ^ #I - 1) (oddCellXSharp p k I dg ℓ e)

/-- *Part C* of `CSI17_integrality_and_cell_floor_at_p.md`: `cost^♯(a, b) := ĉ_H(a + 1, b)`. -/
def oddCellCostSharp (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (a b : ℕ) : ℤ :=
  cHatSeqP p k I dg ℓ e (a + 1) b

/-- `ĉ_H(q, q) = 0`: `R_H(a) − R_H(a) + γ(∅)` and `γ(∅) = 0`.  (Proof of Part B (U3) and Part C of
`CSI17_integrality_and_cell_floor_at_p.md`.) -/
theorem oddCell_cHat_self (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (q : ℕ) :
    cHatSeqP p k I dg ℓ e q q = 0 := by
  simp [cHatSeqP, cHatHP, Rulers.gamma]

end ColouredSand.OddTwist
