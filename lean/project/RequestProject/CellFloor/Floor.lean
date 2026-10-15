module

public import RequestProject.CellFloor.Integrality

/-!
# Parts B and C of `C9_integrality_and_cell_floor.md`: Theorems B and C (Theorem 7.10, house form)

Encodings as in `RequestProject/CellFloor/Basic.lean`.  The `r`-matchings and `tailSum` are those
of piece C2 (`SmithBounds.IsRMatching`, `SmithBounds.tailSum`); for the consequences everything
is cast to `ℝ`, as `SmithBounds.theorem_U` is stated over `ℝ`.
-/

@[expose] public section

namespace CellFloor

open Finset AntitonicFit TheoremF Potential SmithBounds

/-- `V(p) − P J_H(p)` is non-increasing when `V` is (`J_H` is non-decreasing, C7); proof of
Theorem B (U1), `C9_integrality_and_cell_floor.md`. -/
lemma penal_nonIncr {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {V : ℕ → ℤ} (hV : IsPotential I k ℓ α V)
    (P : ℕ) : NonIncrOn (2 ^ #I) (penal V I k ℓ P) := by
  intro j hj
  simp only [penal]
  have h1 : (JHseq I k ℓ j : ℤ) ≤ JHseq I k ℓ (j + 1) := by exact_mod_cast JHseq_mono (by omega) hj
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ P by positivity)
  have h3 := hV.M j (j + 1) (by omega) hj
  linarith

/-- **Theorem B (U1)** of `C9_integrality_and_cell_floor.md`: `v = V − P_r J_H` and
`w = V − P_c J_H` are non-increasing on `[0, N)`.  (Only (M) of the potential is used; no house
condition is needed.) -/
theorem theorem_B_U1 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (Pr Pc : ℕ) {V : ℕ → ℤ}
    (hV : IsPotential I k ℓ α V) :
    NonIncrOn (2 ^ #I) (penal V I k ℓ Pr) ∧ NonIncrOn (2 ^ #I) (penal V I k ℓ Pc) :=
  ⟨penal_nonIncr hV Pr, penal_nonIncr hV Pc⟩

/-- **Theorem B (U2)** of `C9_integrality_and_cell_floor.md`: for every `p < N`,
`v(p) − w(N − 1 − p) = ifit_N(z)(p)`, the integer fit of the cell clocks. -/
theorem theorem_B_U2 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (Pr Pc : ℕ) {V : ℕ → ℤ} (hV : IsPotential I k ℓ α V) :
    ∀ p < 2 ^ #I, penal V I k ℓ Pr p - penal V I k ℓ Pc (2 ^ #I - 1 - p) =
      ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) p := by
  intro p hp
  rw [(lemma_7_9_I2 hI hℓ hα Pr Pc).1 p hp, ← hV.E p hp]
  simp only [penal]
  ring

/-- **Theorem B (U3)** of `C9_integrality_and_cell_floor.md`: for every cell arrow `p, q < N`,
`dancer_I(q) ⊆ dancer_I(p)`: `v(p) − w(q) ≤ cost(p, q)`, with equality when `q = p`.  (Only (G) of
the potential is used; no house condition is needed.) -/
theorem theorem_B_U3 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (Pr Pc : ℕ) {V : ℕ → ℤ}
    (hV : IsPotential I k ℓ α V) :
    (∀ p q, IsCellArrow I p q →
      penal V I k ℓ Pr p - penal V I k ℓ Pc q ≤ cellCost I k ℓ α Pr Pc p q) ∧
    (∀ p < 2 ^ #I, penal V I k ℓ Pr p - penal V I k ℓ Pc p = cellCost I k ℓ α Pr Pc p p) := by
  have hloop : ∀ p, penal V I k ℓ Pr p - penal V I k ℓ Pc p = cellCost I k ℓ α Pr Pc p p := by
    intro p
    simp only [penal, cellCost, cHat_self]
    ring
  refine ⟨fun p q ⟨hp, hq, hsub⟩ => ?_, fun p _ => hloop p⟩
  by_cases heq : dancer I q = dancer I p
  · obtain rfl := dancer_inj hq hp heq
    exact (hloop q).le
  · have hG := hV.G p q ⟨hp, hq, ssubset_of_subset_of_ne hsub heq⟩
    simp only [penal, cellCost]
    linarith

/-- **Theorem B** of `C9_integrality_and_cell_floor.md` ((U1), (U2), (U3) together): for a house
`H`, `P_r, P_c ∈ ℕ` and a potential `V` for `H`, with `v = V − P_r J_H`, `w = V − P_c J_H`. -/
theorem theorem_B {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (Pr Pc : ℕ) {V : ℕ → ℤ} (hV : IsPotential I k ℓ α V) :
    (NonIncrOn (2 ^ #I) (penal V I k ℓ Pr) ∧ NonIncrOn (2 ^ #I) (penal V I k ℓ Pc)) ∧
    (∀ p < 2 ^ #I, penal V I k ℓ Pr p - penal V I k ℓ Pc (2 ^ #I - 1 - p) =
      ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) p) ∧
    ((∀ p q, IsCellArrow I p q →
      penal V I k ℓ Pr p - penal V I k ℓ Pc q ≤ cellCost I k ℓ α Pr Pc p q) ∧
    (∀ p < 2 ^ #I, penal V I k ℓ Pr p - penal V I k ℓ Pc p = cellCost I k ℓ α Pr Pc p p)) :=
  ⟨theorem_B_U1 Pr Pc hV, theorem_B_U2 hI hℓ hα Pr Pc hV, theorem_B_U3 Pr Pc hV⟩

/-- `NonIncrOn` transfers along the cast `ℤ → ℝ` (used for the consequences of Theorems B and C,
`C9_integrality_and_cell_floor.md`). -/
lemma nonIncrOn_cast_real {N : ℕ} {f : ℕ → ℤ} (h : NonIncrOn N f) :
    NonIncrOn N (fun j => (f j : ℝ)) := fun j hj => by
  simp only; exact_mod_cast h j hj

/-- **Theorem B, consequence** (Theorem 7.4 of C2, `SmithBounds.theorem_U`, with everything cast to
`ℝ`) of `C9_integrality_and_cell_floor.md`: for a house `H`, `P_r, P_c ∈ ℕ`, every `r` and every
`r`-matching `(Rows, β)` of the cell arrows on `[0, N)`,
`tailSum N r (ifit_N(z)) ≤ Σ_{a ∈ Rows} cost(a, β(a))`, i.e. `T(r) ≥ Y(r)`.  The potential is
obtained from `Potential.theorem_F`. -/
theorem theorem_B_floor {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (Pr Pc : ℕ) {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I) (IsCellArrow I) r Rows β) :
    tailSum (2 ^ #I) r (fun j => (ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) j : ℝ)) ≤
      ∑ a ∈ Rows, (cellCost I k ℓ α Pr Pc a (β a) : ℝ) := by
  obtain ⟨V, hV⟩ := theorem_F hI hℓ hα
  obtain ⟨⟨h1, h2⟩, hU2, hU3, -⟩ := theorem_B hI hℓ hα Pr Pc hV
  exact theorem_U (IsCellArrow I) (fun a b => (cellCost I k ℓ α Pr Pc a b : ℝ))
    (fun j => (ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) j : ℝ))
    (fun j => (penal V I k ℓ Pr j : ℝ)) (fun j => (penal V I k ℓ Pc j : ℝ))
    (nonIncrOn_cast_real h1) (nonIncrOn_cast_real h2) (fun j hj => by simp only; exact_mod_cast hU2 j hj)
    (fun a _ b _ hab => by simp only; exact_mod_cast hU3 a b hab) hm

/-- **Theorem C** of `C9_integrality_and_cell_floor.md`: for a house `H = (I, k, 2^k − 1, α)` with
`I ≠ ∅` and a potential `V` for `H`, with `v(j) := V(j + 1)`, `w(j) := V(j)`:
* (U1) `v`, `w` are non-increasing on `[0, N − 1)`;
* (U2) `v(j) − w(N − 2 − j) = ŷ^♯(j)` for `j < N − 1`, where `ŷ^♯ = ifit_{N−1}(x^♯)`;
* (U3) `v(a) − w(b) ≤ cost^♯(a, b) = ĉ_H(a + 1, b)` for every arrow `a, b < N − 1`,
  `dancer_I(b) ⊆ dancer_I(a + 1)`.
(The house condition `ℓ < 2^k` follows from `ℓ = 2^k − 1`.) -/
theorem theorem_C {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ' : ℓ = 2 ^ k - 1)
    (hα : 1 ≤ α) (hne : I.Nonempty) {V : ℕ → ℤ} (hV : IsPotential I k ℓ α V) :
    (NonIncrOn (2 ^ #I - 1) (fun j => V (j + 1)) ∧ NonIncrOn (2 ^ #I - 1) V) ∧
    (∀ j < 2 ^ #I - 1, V (j + 1) - V (2 ^ #I - 2 - j) = yhatSharp I k ℓ α j) ∧
    (∀ a b, IsSharpArrow I a b → V (a + 1) - V b ≤ costSharp I k ℓ α a b) := by
  refine ⟨⟨fun j hj => hV.M _ _ (by omega) (by omega),
    fun j hj => hV.M _ _ (by omega) (by omega)⟩, fun j hj => ?_, fun a b ⟨ha, hb, hsub⟩ => ?_⟩
  · rw [yhatSharp, (lemma_7_9_I3 hI hℓ' hα hne).2.2.2.1 j hj, ← hV.E (j + 1) (by omega),
      show 2 ^ #I - 1 - (j + 1) = 2 ^ #I - 2 - j by omega]
  · by_cases heq : dancer I b = dancer I (a + 1)
    · obtain rfl := dancer_inj (by omega) (by omega) heq
      simp [costSharp, cHat_self]
    · exact hV.G (a + 1) b ⟨by omega, by omega, ssubset_of_subset_of_ne hsub heq⟩

/-- **Theorem C, consequence** (by `SmithBounds.theorem_U`, with everything cast to `ℝ`) of
`C9_integrality_and_cell_floor.md`: for a house `H = (I, k, 2^k − 1, α)` with `I ≠ ∅`, every
`r`-matching `(Rows, β)` of the arrows `dancer_I(b) ⊆ dancer_I(a + 1)` on `[0, N − 1)` costs at
least `tailSum (N − 1) r ŷ^♯`.  The potential is obtained from `Potential.theorem_F`. -/
theorem theorem_C_floor {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ' : ℓ = 2 ^ k - 1) (hα : 1 ≤ α) (hne : I.Nonempty) {r : ℕ} {Rows : Finset ℕ}
    {β : ℕ → ℕ} (hm : IsRMatching (2 ^ #I - 1) (IsSharpArrow I) r Rows β) :
    tailSum (2 ^ #I - 1) r (fun j => (yhatSharp I k ℓ α j : ℝ)) ≤
      ∑ a ∈ Rows, (costSharp I k ℓ α a (β a) : ℝ) := by
  have hℓ : ℓ < 2 ^ k := by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
  obtain ⟨V, hV⟩ := theorem_F hI hℓ hα
  obtain ⟨⟨h1, h2⟩, hU2, hU3⟩ := theorem_C hI hℓ' hα hne hV
  exact theorem_U (IsSharpArrow I) (fun a b => (costSharp I k ℓ α a b : ℝ))
    (fun j => (yhatSharp I k ℓ α j : ℝ))
    (fun j => (V (j + 1) : ℝ)) (fun j => (V j : ℝ))
    (nonIncrOn_cast_real h1) (nonIncrOn_cast_real h2)
    (fun j hj => by
      simp only
      rw [show 2 ^ #I - 1 - 1 - j = 2 ^ #I - 2 - j by omega]
      exact_mod_cast hU2 j hj)
    (fun a _ b _ hab => by simp only; exact_mod_cast hU3 a b hab) hm

end CellFloor
