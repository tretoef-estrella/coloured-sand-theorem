module

public import RequestProject.Glue.Lattice
public import RequestProject.Glue.Binomial

/-!
# The action of `E t`, `F t` on the glued vectors (CSG2, §2, proofs of (G1) and (G3))

The vector identities of §2 (with `λ = μ + 2r`):
* `E_stilde`: `E t (s̃ x j) = C(μ−j+t, t) • s̃ x (j−t) + (x β_E(j,t)) • ℓ_{j+r−t}`
  (the first term only when `t ≤ j`);
* `F_stilde`: `F t (s̃ x j) = C(j+t, t) • s̃ x (j+t) + (x β_F(j,t)) • ℓ_{j+r+t}`;
* `P_stilde`: `P w (s̃ x j) = s̃ x j` if `μ − 2j = w`, else `0`.
-/

@[expose] public section

namespace ColouredSand.Glue

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

theorem E_stilde (r : ℕ) (hLM : L = M + 2 * r) (x : ℚ_[p]) (t j : ℕ) (hj : j ≤ M) :
    Eop p L M t (stilde p L M r x j) =
      (if t ≤ j then ((M - j + t).choose t : ℚ_[p]) • stilde p L M r x (j - t) else 0) +
        (x * (betaE L M r j t : ℚ_[p])) • ell p L M (j + r - t) := by
  ext (i' | j')
  · rw [Eop_inl, cL_stilde, Pi.add_apply, Pi.smul_apply, ell_inl, smul_eq_mul]
    unfold betaE
    have hi := Nat.le_of_lt_succ i'.2
    by_cases h1 : t ≤ j + r
    · by_cases h2 : (i' : ℕ) = j + r - t
      · rw [if_pos ⟨hj, by omega, by omega⟩, if_pos h2, if_pos h1,
          show L - ((i' : ℕ) + t) + t = L - (j + r - t) by omega]
        by_cases h3 : t ≤ j
        · rw [if_pos h3, if_pos h3, Pi.smul_apply, stilde_inl, if_pos ⟨by omega, by omega⟩,
            smul_eq_mul, show j - t + r = j + r - t by omega]
          push_cast; ring
        · rw [if_neg h3, if_neg h3, Pi.zero_apply]; push_cast; ring
      · rw [if_neg (by omega), if_neg h2]
        split_ifs with h3
        · rw [Pi.smul_apply, stilde_inl, if_neg (by omega)]; simp
        · simp
    · rw [if_neg (by omega), if_neg h1, if_neg (by omega)]
      split_ifs <;> first | (exfalso; omega) | simp
  · rw [Eop_inr, cR_stilde, Pi.add_apply, Pi.smul_apply, ell_inr, smul_eq_mul, mul_zero, add_zero]
    have hj' := Nat.le_of_lt_succ j'.2
    by_cases h3 : t ≤ j
    · rw [if_pos h3, Pi.smul_apply, stilde_inr, smul_eq_mul]
      by_cases h4 : (j' : ℕ) = j - t
      · rw [if_pos ⟨by omega, by omega⟩, if_pos h4, show M - ((j' : ℕ) + t) + t = M - j + t by omega]
      · rw [if_neg (by omega), if_neg h4]; simp
    · rw [if_neg h3, if_neg (by omega)]; simp

theorem F_stilde (r : ℕ) (hLM : L = M + 2 * r) (x : ℚ_[p]) (t j : ℕ) (hj : j ≤ M) :
    Fop p L M t (stilde p L M r x j) =
      ((j + t).choose t : ℚ_[p]) • stilde p L M r x (j + t) +
        (x * (betaF L M r j t : ℚ_[p])) • ell p L M (j + r + t) := by
  ext (i' | j')
  · rw [Fop_inl, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ell_inl,
      stilde_inl]
    unfold betaF
    have hi := Nat.le_of_lt_succ i'.2
    by_cases h2 : (i' : ℕ) = j + r + t
    · rw [if_pos (show t ≤ (i' : ℕ) by omega), cL_stilde,
        if_pos (show j ≤ M ∧ (i' : ℕ) - t = j + r ∧ (i' : ℕ) - t ≤ L from
          ⟨hj, by omega, by omega⟩), if_pos h2, if_pos (show j + r + t ≤ L by omega), h2]
      by_cases h3 : j + t ≤ M
      · rw [if_pos (show j + t ≤ M ∧ j + r + t = j + t + r from ⟨h3, by ring⟩), if_pos h3]
        push_cast; ring
      · rw [if_neg (by omega), if_neg h3]; push_cast; ring
    · rw [if_neg h2, if_neg (show ¬(j + t ≤ M ∧ (i' : ℕ) = j + t + r) by omega)]
      by_cases ht : t ≤ (i' : ℕ)
      · have hc : cL (stilde p L M r x j) ((i' : ℕ) - t) = 0 := by
          rw [cL_stilde, if_neg (by omega)]
        rw [if_pos ht, hc]; simp
      · rw [if_neg ht]; simp
  · rw [Fop_inr, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ell_inr, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero, stilde_inr]
    have hj' := Nat.le_of_lt_succ j'.2
    by_cases h4 : (j' : ℕ) = j + t
    · rw [if_pos (show t ≤ (j' : ℕ) by omega), cR_stilde, if_pos ⟨by omega, by omega⟩, if_pos h4, h4]
    · rw [if_neg h4]
      by_cases ht : t ≤ (j' : ℕ)
      · have hc : cR (stilde p L M r x j) ((j' : ℕ) - t) = 0 := by
          rw [cR_stilde, if_neg (by omega)]
        rw [if_pos ht, hc]; simp
      · rw [if_neg ht]; simp

theorem P_stilde (r : ℕ) (hLM : L = M + 2 * r) (x : ℚ_[p]) (w : ℤ) (j : ℕ) :
    Pop p L M w (stilde p L M r x j) =
      if (M : ℤ) - 2 * j = w then stilde p L M r x j else 0 := by
  ext (i' | j')
  · rw [Pop_apply, stilde_inl]
    simp only [wt]
    by_cases h : j ≤ M ∧ (i' : ℕ) = j + r
    · rw [if_pos h]
      have : (L : ℤ) - 2 * ((i' : ℕ) : ℤ) = M - 2 * j := by rw [h.2, hLM]; push_cast; ring
      simp only [this]
      split_ifs <;> simp [stilde_inl, h]
    · rw [if_neg h]; split_ifs <;> simp [stilde_inl, h]
  · rw [Pop_apply, stilde_inr]
    simp only [wt]
    by_cases h : (j' : ℕ) = j
    · rw [if_pos h]; simp only [h]; split_ifs <;> simp [stilde_inr, h]
    · rw [if_neg h]; split_ifs <;> simp [stilde_inr, h]

end ColouredSand.Glue
