module

public import RequestProject.Rulers.Bits

/-!
# The cost form: **Proposition 5.2** and **Proposition 5.4 (a), (b)** of
`C3_rulers_gold_clocks.md`

Encodings as in `Basic.lean` and `Family.lean`: `K = 2^k` is written `2 ^ k`, the shift `i ≥ 1`
and `m := i − 1` are natural numbers (so `m` is written `i - 1`), `α` is an integer, and the sum
`Σ_{d=o_a}^{o_b+K−1}` is the sum over `Finset.Ico (oE a) (oE b + 2 ^ k)`.  Both identities are
identities in `ℤ`.
-/

@[expose] public section

namespace Rulers

open Finset

variable {k : ℕ} {I : Finset ℕ}

/-- `κ(μ, o_E) = s_2(μ) + |E| − s_2(μ + o_E)` (the digits of `o_E` are the elements of `E`). -/
lemma kappa_oE (μ : ℕ) (E : Finset ℕ) :
    kappa μ (oE E) = (s2 μ : ℤ) + E.card - s2 (μ + oE E) := by
  rw [kappa, s2_oE]

/-- **Proposition 5.2 (the cost form)** of `C3_rulers_gold_clocks.md`: let `b ⊆ a ⊆ I`,
`Δ := a ∖ b`, `α ≥ 1`, `i ≥ 1` and `m := i − 1`.  Then
`1 − K + o_Δ + δ(Δ) + Σ_{d=o_a}^{o_b+K−1} (α + v_2(i + d))
  = αK + κ(m, K) + R_m(a) − R_{m+K}(b) + γ(Δ)`.
(The hypothesis `α ≥ 1` of the file is kept, although the identity holds for every integer
`α`.) -/
theorem proposition_5_2 (hI : ∀ t ∈ I, t < k) {a b : Finset ℕ} (hba : b ⊆ a) (ha : a ⊆ I)
    (α : ℤ) (_hα : 1 ≤ α) (i : ℕ) (hi : 1 ≤ i) :
    1 - (2 : ℤ) ^ k + oE (a \ b) + delta k (a \ b) +
        ∑ d ∈ Ico (oE a) (oE b + 2 ^ k), (α + (v2 (i + d) : ℤ)) =
      α * 2 ^ k + kappa (i - 1) (2 ^ k) + ruler k I α (i - 1) a -
        ruler k I α (i - 1 + 2 ^ k) b + gamma k I (a \ b) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hs := oE_sdiff hba
  have hlt := oE_lt (a \ b) k (fun t ht => hI t (ha (mem_sdiff.1 ht).1))
  have hle : oE a ≤ oE b + 2 ^ k := by omega
  have hΔ : a \ b ⊆ I := fun t ht => ha (mem_sdiff.1 ht).1
  have hleg := legendre_sum_shift m (oE a) (oE b + 2 ^ k) hle
  rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, hleg, lemma_5_1_a hI hΔ,
    G_sdiff hba]
  simp only [ruler, sum_h_sub, kappa_oE]
  rw [kappa, s2_two_pow]
  rw [show m + (oE b + 2 ^ k) = m + 2 ^ k + oE b by ring]
  have hGa := G_eq (k := k) (I := I) a
  have hGb := G_eq (k := k) (I := I) b
  have hs' : ((oE (a \ b) : ℕ) : ℤ) + oE b = oE a := by exact_mod_cast hs
  push_cast [hle]
  linarith

/-- **Proposition 5.4 (a)** of `C3_rulers_gold_clocks.md`: for `E ⊆ I`,
`κ(K − 1, o_E) = k − min E` if `E ≠ ∅`, and `0` if `E = ∅`. -/
theorem proposition_5_4_a (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) :
    kappa (2 ^ k - 1) (oE E) =
      if h : E = ∅ then 0 else (k : ℤ) - E.min' (nonempty_iff_ne_empty.2 h) := by
  rw [kappa_K_sub_one (fun t ht => hI t (hE ht))]
  split_ifs with h
  · subst h; simp [minOr_empty]
  · rw [minOr, dif_pos (nonempty_iff_ne_empty.2 h)]

/-- **Proposition 5.4 (b)** of `C3_rulers_gold_clocks.md`: for `∅ ≠ D ⊆ I`, `b ⊆ D`,
`Δ := D ∖ b` and `α ≥ 1`:
`1 − K + o_Δ + δ(Δ) + Σ_{d=o_D}^{o_b+K−1} (α + v_2(d)) = αK + R^♯(D) − R^♯(b) + γ(Δ)`.
(The hypothesis `α ≥ 1` of the file is kept, although the identity holds for every integer
`α`.) -/
theorem proposition_5_4_b (hI : ∀ t ∈ I, t < k) {D b : Finset ℕ} (hDne : D ≠ ∅) (hD : D ⊆ I)
    (hbD : b ⊆ D) (α : ℤ) (_hα : 1 ≤ α) :
    1 - (2 : ℤ) ^ k + oE (D \ b) + delta k (D \ b) +
        ∑ d ∈ Ico (oE D) (oE b + 2 ^ k), (α + (v2 d : ℤ)) =
      α * 2 ^ k + rulerSharp k I α D - rulerSharp k I α b + gamma k I (D \ b) := by
  have hne : D.Nonempty := nonempty_iff_ne_empty.2 hDne
  have hs := oE_sdiff hbD
  have hlt := oE_lt (D \ b) k (fun t ht => hI t (hD (mem_sdiff.1 ht).1))
  have hle : oE D ≤ oE b + 2 ^ k := by omega
  have hpos : 1 ≤ oE D := by
    obtain ⟨x, hx⟩ := hne
    exact le_trans (Nat.one_le_two_pow) (single_le_sum (f := fun t => 2 ^ t) (by simp) hx)
  have hΔ : D \ b ⊆ I := fun t ht => hD (mem_sdiff.1 ht).1
  have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hleg := legendre_sum (oE D) (oE b + 2 ^ k) hpos hle
  rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, hleg, lemma_5_1_a hI hΔ,
    G_sdiff hbD, show oE b + 2 ^ k - 1 = 2 ^ k - 1 + oE b by omega,
    s2_K_sub_one_add (fun t ht => hI t (hD (hbD ht)))]
  simp only [rulerSharp, sum_h_sub, kappa_K_sub_one (fun t ht => hI t (hD ht)),
    kappa_K_sub_one (fun t ht => hI t (hD (hbD ht)))]
  have h1 := s2_oE_sub_one hne
  rw [show D.min' hne = minOr k D by rw [minOr, dif_pos hne]] at h1
  have h1' : ((s2 (oE D - 1) : ℕ) : ℤ) + 1 = D.card + minOr k D := by exact_mod_cast h1
  have hGa := G_eq (k := k) (I := I) D
  have hGb := G_eq (k := k) (I := I) b
  have hs' : ((oE (D \ b) : ℕ) : ℤ) + oE b = oE D := by exact_mod_cast hs
  push_cast [hle]
  linarith

end Rulers
