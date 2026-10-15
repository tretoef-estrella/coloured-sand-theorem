module

public import RequestProject.OddCellFloor.Integrality

/-!
# Parts B and C of `CSI17_integrality_and_cell_floor_at_p.md`: the floor of every cell

Namespace `ColouredSand.OddTwist`; encodings as in `RequestProject/OddCellFloor/Basic.lean`.
The proofs are those of C9 (`RequestProject/CellFloor/Floor.lean`) with the base-`p` potential
of CSI16 (`IsPotentialP`, Theorem F_p `oddF_theorem_F`).  The `r`-matchings and `tailSum` are those
of C2 (`SmithBounds.IsRMatching`, `SmithBounds.tailSum`); for the consequences everything is cast
to `ℝ`, as `SmithBounds.theorem_U` is stated over `ℝ`.  The arrows are C9's
`CellFloor.IsCellArrow I` and `CellFloor.IsSharpArrow I` (they depend only on `I`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF SmithBounds CellFloor

variable {p : ℕ} [hp : Fact p.Prime] {dg : ℕ → ℕ}

/-- `V(q) − P J_H(q)` is non-increasing when `V` is (`J_H` is non-decreasing, CSI16); proof of
Part B (U1) of `CSI17_integrality_and_cell_floor_at_p.md`. -/
lemma oddCellPenal_nonIncr {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ}
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V)
    (P : ℕ) : NonIncrOn (2 ^ #I) (oddCellPenal V p k I dg ℓ P) := by
  intro j hj
  simp only [oddCellPenal]
  have h1 : (JHseqP p k I dg ℓ j : ℤ) ≤ JHseqP p k I dg ℓ (j + 1) := by
    exact_mod_cast JHseqP_mono oddHou_two_le_p hd (by omega) hj
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ P by positivity)
  have h3 := hV.M j (j + 1) (by omega) hj
  linarith

/-- **Part B (U1)** of `CSI17_integrality_and_cell_floor_at_p.md`: `v = V − P_r J_H` and
`w = V − P_c J_H` are non-increasing on `[0, N)`.  (Only (M) of the potential and the digit
condition are used.) -/
theorem oddCell_B_U1 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (Pr Pc : ℕ) {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    NonIncrOn (2 ^ #I) (oddCellPenal V p k I dg ℓ Pr) ∧
      NonIncrOn (2 ^ #I) (oddCellPenal V p k I dg ℓ Pc) :=
  ⟨oddCellPenal_nonIncr hd hV Pr, oddCellPenal_nonIncr hd hV Pc⟩

/-- **Part B (U2)** of `CSI17_integrality_and_cell_floor_at_p.md`: for every `q < N`,
`v(q) − w(N − 1 − q) = ifit_N(z)(q)`, the integer fit of the cell clocks. -/
theorem oddCell_B_U2 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ)
    {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    ∀ q < 2 ^ #I, oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc (2 ^ #I - 1 - q) =
      ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q := by
  intro q hq
  rw [(oddCell_lemma_7_9_I2 hI hd hℓ he Pr Pc).1 q hq, ← hV.E q hq]
  simp only [oddCellPenal]
  ring

omit hp in
/-- **Part B (U3)** of `CSI17_integrality_and_cell_floor_at_p.md`: for every cell arrow
`q, q' < N`, `dancer_I(q') ⊆ dancer_I(q)`: `v(q) − w(q') ≤ cost(q, q')`, with equality on loops
`q' = q`.  (Only (G) of the potential is used; no house condition, and no primality, is needed.) -/
theorem oddCell_B_U3 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (Pr Pc : ℕ) {V : ℕ → ℤ}
    (hV : IsPotentialP p k I dg ℓ e V) :
    (∀ q q', IsCellArrow I q q' →
      oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc q' ≤
        oddCellCost p k I dg ℓ e Pr Pc q q') ∧
    (∀ q < 2 ^ #I, oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc q =
      oddCellCost p k I dg ℓ e Pr Pc q q) := by
  have hloop : ∀ q, oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc q =
      oddCellCost p k I dg ℓ e Pr Pc q q := by
    intro q
    simp only [oddCellPenal, oddCellCost, oddCell_cHat_self]
    ring
  refine ⟨fun q q' ⟨hq, hq', hsub⟩ => ?_, fun q _ => hloop q⟩
  by_cases heq : dancer I q' = dancer I q
  · obtain rfl := dancer_inj hq' hq heq
    exact (hloop q').le
  · have hG := hV.G q q' ⟨hq, hq', ssubset_of_subset_of_ne hsub heq⟩
    simp only [oddCellPenal, oddCellCost]
    linarith

/-- **Part B** of `CSI17_integrality_and_cell_floor_at_p.md` ((U1), (U2), (U3) together): for a
base-`p` house `H`, `P_r, P_c ∈ ℕ` (no relation assumed) and a potential `V` for `H` (CSI16), with
`v = V − P_r J_H`, `w = V − P_c J_H`. -/
theorem oddCell_theorem_B {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ)
    {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (NonIncrOn (2 ^ #I) (oddCellPenal V p k I dg ℓ Pr) ∧
      NonIncrOn (2 ^ #I) (oddCellPenal V p k I dg ℓ Pc)) ∧
    (∀ q < 2 ^ #I, oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc (2 ^ #I - 1 - q) =
      ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q) ∧
    ((∀ q q', IsCellArrow I q q' →
      oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc q' ≤
        oddCellCost p k I dg ℓ e Pr Pc q q') ∧
    (∀ q < 2 ^ #I, oddCellPenal V p k I dg ℓ Pr q - oddCellPenal V p k I dg ℓ Pc q =
      oddCellCost p k I dg ℓ e Pr Pc q q)) :=
  ⟨oddCell_B_U1 hd Pr Pc hV, oddCell_B_U2 hI hd hℓ he Pr Pc hV, oddCell_B_U3 Pr Pc hV⟩

/-- **Part B, consequence** of `CSI17_integrality_and_cell_floor_at_p.md` (by
`SmithBounds.theorem_U`, everything cast to `ℝ`): for a base-`p` house `H`, `P_r, P_c ∈ ℕ`, every
`r` and every `r`-matching `(Rows, β)` of the cell arrows on `[0, N)`,
`tailSum N r (ifit_N(z)) ≤ Σ_{a ∈ Rows} cost(a, β(a))`.  The potential is supplied by Theorem F_p
(`oddF_theorem_F`), so none is assumed (more general than the file's wording). -/
theorem oddCell_theorem_B_floor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) {r : ℕ}
    {Rows : Finset ℕ} {β : ℕ → ℕ} (hm : IsRMatching (2 ^ #I) (IsCellArrow I) r Rows β) :
    tailSum (2 ^ #I) r (fun j => (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) j : ℝ)) ≤
      ∑ a ∈ Rows, (oddCellCost p k I dg ℓ e Pr Pc a (β a) : ℝ) := by
  obtain ⟨V, hV⟩ := oddF_theorem_F hI hd hℓ he
  obtain ⟨⟨h1, h2⟩, hU2, hU3, -⟩ := oddCell_theorem_B hI hd hℓ he Pr Pc hV
  exact theorem_U (IsCellArrow I) (fun a b => (oddCellCost p k I dg ℓ e Pr Pc a b : ℝ))
    (fun j => (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) j : ℝ))
    (fun j => (oddCellPenal V p k I dg ℓ Pr j : ℝ)) (fun j => (oddCellPenal V p k I dg ℓ Pc j : ℝ))
    (nonIncrOn_cast_real h1) (nonIncrOn_cast_real h2)
    (fun j hj => by simp only; exact_mod_cast hU2 j hj)
    (fun a _ b _ hab => by simp only; exact_mod_cast hU3 a b hab) hm

/-- **Part C** of `CSI17_integrality_and_cell_floor_at_p.md` (the shift `0`, `i = 0`): for a
base-`p` house `H = (I, k, p^k − 1, e, d)` with `I ≠ ∅` and a potential `V` for `H`, with
`v(j) := V(j + 1)`, `w(j) := V(j)`:
* (U1) `v`, `w` are non-increasing on `[0, N − 1)`;
* (U2) `v(j) − w(N − 2 − j) = ŷ^♯(j)` for `j < N − 1`, where `ŷ^♯ = ifit_{N−1}(x^♯)`;
* (U3) `v(a) − w(b) ≤ cost^♯(a, b) = ĉ_H(a + 1, b)` for every arrow `a, b < N − 1`,
  `dancer_I(b) ⊆ dancer_I(a + 1)` (rows `D ≠ ∅`, columns `D ≠ I`).
(The house condition `ℓ < p^k` follows from `ℓ = p^k − 1`.) -/
theorem oddCell_theorem_C {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (NonIncrOn (2 ^ #I - 1) (fun j => V (j + 1)) ∧ NonIncrOn (2 ^ #I - 1) V) ∧
    (∀ j < 2 ^ #I - 1, V (j + 1) - V (2 ^ #I - 2 - j) = oddCellYhatSharp p k I dg ℓ e j) ∧
    (∀ a b, IsSharpArrow I a b → V (a + 1) - V b ≤ oddCellCostSharp p k I dg ℓ e a b) := by
  refine ⟨⟨fun j hj => hV.M _ _ (by omega) (by omega),
    fun j hj => hV.M _ _ (by omega) (by omega)⟩, fun j hj => ?_, fun a b ⟨ha, hb, hsub⟩ => ?_⟩
  · rw [oddCellYhatSharp, (oddCell_lemma_7_9_I3 hI hd hℓ' he hne).2.2.2.2.1 j hj,
      ← hV.E (j + 1) (by omega), show 2 ^ #I - 1 - (j + 1) = 2 ^ #I - 2 - j by omega]
  · by_cases heq : dancer I b = dancer I (a + 1)
    · obtain rfl := dancer_inj (by omega) (by omega) heq
      simp [oddCellCostSharp, oddCell_cHat_self]
    · exact hV.G (a + 1) b ⟨by omega, by omega, ssubset_of_subset_of_ne hsub heq⟩

/-- **Part C, consequence** of `CSI17_integrality_and_cell_floor_at_p.md` (by
`SmithBounds.theorem_U`, everything cast to `ℝ`): for a base-`p` house `H = (I, k, p^k − 1, e, d)`
with `I ≠ ∅`, every `r`-matching `(Rows, β)` of the arrows `dancer_I(b) ⊆ dancer_I(a + 1)` on
`[0, N − 1)` costs at least `tailSum (N − 1) r ŷ^♯`.  The potential is supplied by Theorem F_p
(`oddF_theorem_F`). -/
theorem oddCell_theorem_C_floor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I - 1) (IsSharpArrow I) r Rows β) :
    tailSum (2 ^ #I - 1) r (fun j => (oddCellYhatSharp p k I dg ℓ e j : ℝ)) ≤
      ∑ a ∈ Rows, (oddCellCostSharp p k I dg ℓ e a (β a) : ℝ) := by
  have hℓ : ℓ < p ^ k := by have : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos; omega
  obtain ⟨V, hV⟩ := oddF_theorem_F hI hd hℓ he
  obtain ⟨⟨h1, h2⟩, hU2, hU3⟩ := oddCell_theorem_C hI hd hℓ' he hne hV
  exact theorem_U (IsSharpArrow I) (fun a b => (oddCellCostSharp p k I dg ℓ e a b : ℝ))
    (fun j => (oddCellYhatSharp p k I dg ℓ e j : ℝ))
    (fun j => (V (j + 1) : ℝ)) (fun j => (V j : ℝ))
    (nonIncrOn_cast_real h1) (nonIncrOn_cast_real h2)
    (fun j hj => by
      simp only
      rw [show 2 ^ #I - 1 - 1 - j = 2 ^ #I - 2 - j by omega]
      exact_mod_cast hU2 j hj)
    (fun a _ b _ hab => by simp only; exact_mod_cast hU3 a b hab) hm

end ColouredSand.OddTwist
