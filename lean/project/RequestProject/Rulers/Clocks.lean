module

public import RequestProject.Rulers.CostForm

/-!
# The clocks: **Proposition 5.3** and **Proposition 5.4 (c)** of `C3_rulers_gold_clocks.md`

Encodings as in `Basic.lean` and `Family.lean`: the raw clock `u_i(D)` is `clock k I i D`,
`x_D` is `xD k I m D` (with `α = 1`), `x^♯_D` is `xSharp k I D` (with `α = 1`), `K = 2^k` is
written `2 ^ k`, and `m := i − 1` is written `i - 1`.  Both identities are identities in `ℤ`.
-/

@[expose] public section

namespace Rulers

open Finset

variable {k : ℕ} {I : Finset ℕ}

/-- `ξ_D = K + o_E − o_D` (with `E = I ∖ D`), `ξ_D ≥ 1`, and
`φ(ξ_D) + s_2(ξ_D) = ξ_D + k − |D| − G(E) + 1` (Step 1 of the proof of Proposition 5.3). -/
lemma xi_facts (hI : ∀ t ∈ I, t < k) {D : Finset ℕ} (hD : D ⊆ I) :
    (xi k I D : ℤ) = 2 ^ k + oE (I \ D) - oE D ∧ 1 ≤ xi k I D ∧
      phi (xi k I D) + s2 (xi k I D) = (xi k I D : ℤ) + k - D.card - G k I (I \ D) + 1 := by
  obtain ⟨hx, hx1⟩ := lemma_5_0_xi hI hD
  have hs := oE_sdiff hD
  have hs' : ((oE (I \ D) : ℕ) : ℤ) + oE D = oE I := by exact_mod_cast hs
  have hxE : (xi k I D : ℤ) = 2 ^ k + oE (I \ D) - oE D := by rw [hx]; linarith
  refine ⟨hxE, hx1, ?_⟩
  have hcore := s2_core hI hD (xi k I D - 1) (by push_cast [hx1]; linarith)
  have hsucc := s2_succ (xi k I D - 1)
  rw [Nat.sub_add_cancel hx1] at hsucc
  rw [phi]
  linarith

/-- **Proposition 5.3 (the clocks)** of `C3_rulers_gold_clocks.md`: let `α = 1`, `i ≥ 1`,
`m := i − 1`.  For every dancer `D ⊆ I`, `u_i(D) = k + K + κ(m, K) + x_D`. -/
theorem proposition_5_3 (hI : ∀ t ∈ I, t < k) {D : Finset ℕ} (hD : D ⊆ I) (i : ℕ)
    (hi : 1 ≤ i) :
    clock k I i D = k + 2 ^ k + kappa (i - 1) (2 ^ k) + xD k I (i - 1) D := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨hxE, hx1, hphi⟩ := xi_facts hI hD
  simp only [Nat.add_sub_cancel, clock, xD, ruler, sum_h_sub, kappa_oE]
  rw [show m + 1 + oE D - 1 = m + oE D by omega]
  have hsum : m + oE D + xi k I D = m + 2 ^ k + oE (I \ D) := by
    have : ((m + oE D + xi k I D : ℕ) : ℤ) = ((m + 2 ^ k + oE (I \ D) : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this
  rw [kappa, kappa, hsum, s2_two_pow]
  have hGD := G_eq (k := k) (I := I) D
  have hGE := G_eq (k := k) (I := I) (I \ D)
  push_cast
  linarith

/-- **Proposition 5.4 (c)** of `C3_rulers_gold_clocks.md`: for `α = 1` and `∅ ≠ D ⊆ I`,
`u_0(D) = k + K + x^♯_D`. -/
theorem proposition_5_4_c (hI : ∀ t ∈ I, t < k) {D : Finset ℕ} (hDne : D ≠ ∅) (hD : D ⊆ I) :
    clock k I 0 D = k + 2 ^ k + xSharp k I D := by
  have hne : D.Nonempty := nonempty_iff_ne_empty.2 hDne
  obtain ⟨hxE, hx1, hphi⟩ := xi_facts hI hD
  have hE : ∀ t ∈ I \ D, t < k := fun t ht => hI t (mem_sdiff.1 ht).1
  simp only [clock, xSharp, rulerSharp, sum_h_sub, kappa_K_sub_one hE,
    kappa_K_sub_one (fun t ht => hI t (hD ht)), zero_add]
  have hpos : 1 ≤ oE D := by
    obtain ⟨x, hx⟩ := hne
    exact le_trans (Nat.one_le_two_pow) (single_le_sum (f := fun t => 2 ^ t) (by simp) hx)
  have hsum : oE D - 1 + xi k I D = 2 ^ k - 1 + oE (I \ D) := by
    have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have : ((oE D - 1 + xi k I D : ℕ) : ℤ) = ((2 ^ k - 1 + oE (I \ D) : ℕ) : ℤ) := by
      push_cast [hpos, hK]; linarith
    exact_mod_cast this
  rw [kappa, hsum, s2_K_sub_one_add hE]
  have h1 := s2_oE_sub_one hne
  rw [show D.min' hne = minOr k D by rw [minOr, dif_pos hne]] at h1
  have h1' : ((s2 (oE D - 1) : ℕ) : ℤ) + 1 = D.card + minOr k D := by exact_mod_cast h1
  have hGE := G_eq (k := k) (I := I) (I \ D)
  push_cast
  linarith

end Rulers
