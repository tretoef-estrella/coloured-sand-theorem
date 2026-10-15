module

public import RequestProject.Potential.All
public import RequestProject.SmithBounds.All

/-!
# The *Setting* of `C9_integrality_and_cell_floor.md`

## Encoding

* A **house** `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`, `α : ℤ`,
  with the house conditions as hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`, `hα : 1 ≤ α`
  (each theorem carries only the ones its proof uses; this is said in its docstring).
  `N = 2^{|I|}` is `2 ^ #I`.  Positions are natural numbers; sequences of length `N` are functions
  `ℕ → ℤ` (or `ℕ → ℝ`) of which only the positions `< N` matter (as in pieces C1, C7, C8).
* `x_H` is `TheoremF.xHseq I k ℓ α`, `J_H` is `TheoremF.JHseq I k ℓ` (natural-number valued,
  cast to `ℤ` where needed), `ŷ_H` is `Potential.yhat I k ℓ α = AntitonicFit.ifit N x_H`, the
  real fit of an integer sequence `x` is `AntitonicFit.fit N (AntitonicFit.toR x)`, and
  `ĉ_H(p, q)` is `Potential.cHat I k ℓ α p q`.
* The penalties `P_r, P_c` are natural numbers `Pr Pc : ℕ`.
* `cellClock I k ℓ α Pr Pc p = x_H(p) − P_r J_H(p) + P_c J_H(N − 1 − p)` (the cell clocks `z`);
  `cellCost I k ℓ α Pr Pc p q = ĉ_H(p, q) − P_r J_H(p) + P_c J_H(q)` (the cell costs);
  `IsCellArrow I p q` is `p < N ∧ q < N ∧ dancer_I(q) ⊆ dancer_I(p)` (loops included).
* `penal V I k ℓ P p = V(p) − P J_H(p)`, so that `v = penal V I k ℓ Pr` and
  `w = penal V I k ℓ Pc` in Theorem B.
* For Lemma 7.9 (I3) and Theorem C: `xSharp I k ℓ α j = x_H(j + 1)` is `x^♯` (used with length
  `N − 1`), `yhatSharp I k ℓ α = ifit_{N−1}(x^♯)` is `ŷ^♯`, `costSharp I k ℓ α a b = ĉ_H(a + 1, b)`
  is `cost^♯`, and `IsSharpArrow I a b` is `a < N − 1 ∧ b < N − 1 ∧ dancer_I(b) ⊆ dancer_I(a + 1)`.
-/

@[expose] public section

namespace CellFloor

open Finset AntitonicFit TheoremF Potential

/-- *Setting* of `C9_integrality_and_cell_floor.md`: the **cell clocks**
`z(p) := x_H(p) − P_r J_H(p) + P_c J_H(N − 1 − p)`. -/
def cellClock (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (Pr Pc : ℕ) : ℕ → ℤ := fun p =>
  xHseq I k ℓ α p - (Pr : ℤ) * (JHseq I k ℓ p : ℤ) + (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - p) : ℤ)

/-- *Setting* of `C9_integrality_and_cell_floor.md`: the **cell costs**
`cost(p, q) := ĉ_H(p, q) − P_r J_H(p) + P_c J_H(q)`. -/
def cellCost (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (Pr Pc : ℕ) (p q : ℕ) : ℤ :=
  cHat I k ℓ α p q - (Pr : ℤ) * (JHseq I k ℓ p : ℤ) + (Pc : ℤ) * (JHseq I k ℓ q : ℤ)

/-- *Setting* of `C9_integrality_and_cell_floor.md`: the **cell arrows** are the pairs
`p, q < N` with `dancer_I(q) ⊆ dancer_I(p)` (loops `q = p` included). -/
def IsCellArrow (I : Finset ℕ) (p q : ℕ) : Prop :=
  p < 2 ^ #I ∧ q < 2 ^ #I ∧ dancer I q ⊆ dancer I p

/-- *Part B* (Theorem B) of `C9_integrality_and_cell_floor.md`: `p ↦ V(p) − P J_H(p)`; with
`P = P_r` this is `v`, with `P = P_c` it is `w`. -/
def penal (V : ℕ → ℤ) (I : Finset ℕ) (k ℓ : ℕ) (P : ℕ) : ℕ → ℤ := fun p =>
  V p - (P : ℤ) * (JHseq I k ℓ p : ℤ)

/-- *Part A* (Lemma 7.9 (I3)) of `C9_integrality_and_cell_floor.md`: `x^♯(j) := x_H(j + 1)`
(a sequence of length `N − 1`). -/
def xSharp (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : ℕ → ℤ := fun j => xHseq I k ℓ α (j + 1)

/-- *Part C* (Theorem C) of `C9_integrality_and_cell_floor.md`: `ŷ^♯ := ifit_{N−1}(x^♯)`. -/
noncomputable def yhatSharp (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : ℕ → ℤ :=
  ifit (2 ^ #I - 1) (xSharp I k ℓ α)

/-- *Part C* (Theorem C) of `C9_integrality_and_cell_floor.md`: `cost^♯(a, b) := ĉ_H(a + 1, b)`. -/
def costSharp (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (a b : ℕ) : ℤ := cHat I k ℓ α (a + 1) b

/-- *Part C* (Theorem C) of `C9_integrality_and_cell_floor.md`: the arrows of the shifted problem,
`a, b < N − 1` with `dancer_I(b) ⊆ dancer_I(a + 1)` (rows `D ≠ ∅`, columns `D ≠ I`). -/
def IsSharpArrow (I : Finset ℕ) (a b : ℕ) : Prop :=
  a < 2 ^ #I - 1 ∧ b < 2 ^ #I - 1 ∧ dancer I b ⊆ dancer I (a + 1)

/-! ### General facts used in the proofs -/

/-- If the real fit of an integer sequence takes integer values `y`, then the integer fit equals
`y` (on a level set of integral value `v` with `P` positions and sum `S`, `S = P v` by (L), so
`S mod P = 0`).  (Proof step of Lemma 7.9 in `C9_integrality_and_cell_floor.md`.) -/
theorem ifit_eq_of_fit_eq_int {N : ℕ} {x y : ℕ → ℤ} (h : ∀ j < N, fit N (toR x) j = (y j : ℝ)) :
    ∀ j < N, ifit N x j = y j := by
  intro j hj
  rw [ifit_of_lt hj]
  have hS := sum_levelSet_fit_int (x := x) hj
  rw [h j hj] at hS
  have hP : 0 < (levelSet N (fit N (toR x)) j).card := card_pos.2 ⟨j, by simp [levelSet, hj]⟩
  have hS' : ∑ i ∈ levelSet N (fit N (toR x)) j, x i =
      0 + ((levelSet N (fit N (toR x)) j).card : ℤ) * y j := by
    rw [zero_add]; exact_mod_cast hS
  rw [hS', blockF_add_mul _ _ hP, blockF_zero, zero_add]

/-- The fit of a sequence of length `1` is the sequence itself.  (Base case of the induction in
the proof of Lemma 7.9 (I1), `C9_integrality_and_cell_floor.md`.) -/
theorem fit_one (x : ℕ → ℝ) : fit 1 x 0 = x 0 := by
  have hfit : IsFit 1 x x := ⟨fun i hi => by omega, fun y _ => by
    simp only [sqDist, sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
    exact sum_nonneg fun j _ => sq_nonneg _⟩
  exact fit_unique hfit 0 (by omega)

/-- Two positions `< N` with the same dancer are equal (Lemma 0c of C7).  (Used in Theorems B
and C of `C9_integrality_and_cell_floor.md`.) -/
theorem dancer_inj {I : Finset ℕ} {p q : ℕ} (hp : p < 2 ^ #I) (hq : q < 2 ^ #I)
    (h : dancer I p = dancer I q) : p = q := by
  rw [← lemma_0c_rank hp, ← lemma_0c_rank hq, h]

/-- `ĉ_H(p, p) = 0`: `R_H(a) − R_H(a) + γ(∅)` and `γ(∅) = 0`.  (Proof of Theorem B (U3),
`C9_integrality_and_cell_floor.md`.) -/
theorem cHat_self (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (p : ℕ) : cHat I k ℓ α p p = 0 := by
  simp [cHat, Houses.cHatH, Rulers.gamma]

end CellFloor
