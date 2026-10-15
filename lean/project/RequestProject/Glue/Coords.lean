module

public import RequestProject.Glue.Defs

/-!
# Coordinates of the operators of §0 (CSG2, §0 "Setting")

Coordinate formulas for `F t`, `E t`, `P w`, `Hq` and for the vectors `ℓ_i`, `s_j`, `s̃ x j`
of `RequestProject/Glue/Defs.lean`, and the action of `F t`, `E t`, `P w` on the basis exactly as
written in §0 of `CSG2_lemma_7_the_glue.md` (`F_ell`, `F_ess`, `E_ell`, `E_ess`, `P_ell`, `P_ess`):
this is the check that the matrices `Fmat`, `Emat`, `Pmat` encode the definitions of §0.

`cL v n` (resp. `cR v n`) is the coordinate of `v` at `inl n` (resp. `inr n`), and `0` when `n`
is out of range.
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

/-- The `ℓ_n`-coordinate of `v` (`0` if `n > λ`). -/
noncomputable def cL (v : V p L M) (n : ℕ) : ℚ_[p] :=
  if h : n ≤ L then v (.inl ⟨n, Nat.lt_succ_of_le h⟩) else 0

/-- The `s_n`-coordinate of `v` (`0` if `n > μ`). -/
noncomputable def cR (v : V p L M) (n : ℕ) : ℚ_[p] :=
  if h : n ≤ M then v (.inr ⟨n, Nat.lt_succ_of_le h⟩) else 0

lemma cL_fin (v : V p L M) (i : Fin (L + 1)) : cL v i = v (.inl i) := by
  simp [cL, Nat.le_of_lt_succ i.2]

lemma cR_fin (v : V p L M) (j : Fin (M + 1)) : cR v j = v (.inr j) := by
  simp [cR, Nat.le_of_lt_succ j.2]

variable (p L M) in
lemma Fop_inl (t : ℕ) (v : V p L M) (i' : Fin (L + 1)) :
    Fop p L M t v (.inl i') =
      if t ≤ (i' : ℕ) then (((i' : ℕ).choose t : ℕ) : ℚ_[p]) * cL v (i' - t) else 0 := by
  simp only [Fop, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fmat,
    Matrix.of_apply]
  simp only [zero_mul, Finset.sum_const_zero, add_zero, ite_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i' - t, by omega⟩]
    · simp [cL, show (i' : ℕ) - t ≤ L by omega, show (i' : ℕ) - t + t = i' by omega]
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; simp; omega
    · simp
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; omega

variable (p L M) in
lemma Fop_inr (t : ℕ) (v : V p L M) (j' : Fin (M + 1)) :
    Fop p L M t v (.inr j') =
      if t ≤ (j' : ℕ) then (((j' : ℕ).choose t : ℕ) : ℚ_[p]) * cR v (j' - t) else 0 := by
  simp only [Fop, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fmat,
    Matrix.of_apply]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, ite_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j' - t, by omega⟩]
    · simp [cR, show (j' : ℕ) - t ≤ M by omega, show (j' : ℕ) - t + t = j' by omega]
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; simp; omega
    · simp
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; omega

variable (p L M) in
lemma Eop_inl (t : ℕ) (v : V p L M) (i' : Fin (L + 1)) :
    Eop p L M t v (.inl i') =
      (((L - ((i' : ℕ) + t) + t).choose t : ℕ) : ℚ_[p]) * cL v (i' + t) := by
  simp only [Eop, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Emat,
    Matrix.of_apply]
  simp only [zero_mul, Finset.sum_const_zero, add_zero, ite_mul]
  by_cases h : (i' : ℕ) + t ≤ L
  · rw [Finset.sum_eq_single ⟨i' + t, by omega⟩]
    · simp [cL, h]
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; simp; omega
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [cL, h]
    · intro b _; rw [if_neg]; omega

variable (p L M) in
lemma Eop_inr (t : ℕ) (v : V p L M) (j' : Fin (M + 1)) :
    Eop p L M t v (.inr j') =
      (((M - ((j' : ℕ) + t) + t).choose t : ℕ) : ℚ_[p]) * cR v (j' + t) := by
  simp only [Eop, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Emat,
    Matrix.of_apply]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, ite_mul]
  by_cases h : (j' : ℕ) + t ≤ M
  · rw [Finset.sum_eq_single ⟨j' + t, by omega⟩]
    · simp [cR, h]
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; simp; omega
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [cR, h]
    · intro b _; rw [if_neg]; omega

variable (p L M) in
lemma Pop_apply (w : ℤ) (v : V p L M) (y : Idx L M) :
    Pop p L M w v y = if wt L M y = w then v y else 0 := by
  simp only [Pop, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pmat, Matrix.of_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

variable (p L M) in
lemma Hop_apply (q c k r : ℕ) (v : V p L M) (y : Idx L M) :
    Hop p L M q c k r v y = (match y with
      | .inl i => ((Nt p q c k i : ℤ_[p]) : ℚ_[p])
      | .inr j => ((Nt p q c k ((j : ℕ) + r) : ℤ_[p]) : ℚ_[p])) * v y := by
  simp only [Hop, Matrix.mulVecLin_apply, Hmat, Matrix.mulVec_diagonal]
  cases y <;> rfl

/-! ### Coordinates of `ℓ`, `s`, `s̃` -/

lemma ell_inl (i : ℕ) (i' : Fin (L + 1)) :
    ell p L M i (.inl i') = if (i' : ℕ) = i then 1 else 0 := by
  unfold ell
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [Pi.single_apply, if_neg]; intro h; apply h2; simp at h; rw [h]
  · omega
  · rfl

lemma ell_inr (i : ℕ) (j' : Fin (M + 1)) : ell p L M i (.inr j') = 0 := by
  unfold ell; split_ifs <;> simp

lemma ess_inl (j : ℕ) (i' : Fin (L + 1)) : ess p L M j (.inl i') = 0 := by
  unfold ess; split_ifs <;> simp

lemma ess_inr (j : ℕ) (j' : Fin (M + 1)) :
    ess p L M j (.inr j') = if (j' : ℕ) = j then 1 else 0 := by
  unfold ess
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [Pi.single_apply, if_neg]; intro h; apply h2; simp at h; rw [h]
  · omega
  · rfl

lemma cL_ell (i n : ℕ) : cL (ell p L M i) n = if n = i ∧ n ≤ L then 1 else 0 := by
  unfold cL; split_ifs <;> simp_all [ell_inl]; omega

lemma cR_ell (i n : ℕ) : cR (ell p L M i) n = 0 := by
  unfold cR; split_ifs <;> simp [ell_inr]

lemma cL_ess (j n : ℕ) : cL (ess p L M j) n = 0 := by
  unfold cL; split_ifs <;> simp [ess_inl]

lemma cR_ess (j n : ℕ) : cR (ess p L M j) n = if n = j ∧ n ≤ M then 1 else 0 := by
  unfold cR; split_ifs <;> simp_all [ess_inr]; omega

lemma stilde_inl (r : ℕ) (x : ℚ_[p]) (j : ℕ) (i' : Fin (L + 1)) :
    stilde p L M r x j (.inl i') =
      if j ≤ M ∧ (i' : ℕ) = j + r then x * ((j + r).choose j : ℚ_[p]) else 0 := by
  unfold stilde
  split_ifs <;> simp_all [ell_inl, ess_inl]

lemma stilde_inr (r : ℕ) (x : ℚ_[p]) (j : ℕ) (j' : Fin (M + 1)) :
    stilde p L M r x j (.inr j') = if (j' : ℕ) = j then 1 else 0 := by
  unfold stilde
  split_ifs <;> simp_all [ell_inr, ess_inr]
  omega

lemma cL_stilde (r : ℕ) (x : ℚ_[p]) (j n : ℕ) :
    cL (stilde p L M r x j) n =
      if j ≤ M ∧ n = j + r ∧ n ≤ L then x * ((j + r).choose j : ℚ_[p]) else 0 := by
  unfold cL; split_ifs <;> simp_all [stilde_inl]; omega

lemma cR_stilde (r : ℕ) (x : ℚ_[p]) (j n : ℕ) :
    cR (stilde p L M r x j) n = if n = j ∧ n ≤ M then 1 else 0 := by
  unfold cR; split_ifs <;> simp_all [stilde_inr]; omega

/-! ### The action on the basis, exactly as in §0 -/

/-- `F t ℓ_i = C(i + t, t) • ℓ_{i + t}` (`= 0` if `i + t > λ`). -/
theorem F_ell (t i : ℕ) (hi : i ≤ L) :
    Fop p L M t (ell p L M i) = ((i + t).choose t : ℚ_[p]) • ell p L M (i + t) := by
  ext (i' | j')
  · rw [Fop_inl]; simp only [Pi.smul_apply, smul_eq_mul, ell_inl, cL_ell]
    split_ifs <;> first | omega | simp_all
  · rw [Fop_inr]; simp [ell_inr, cR_ell]

/-- `F t s_j = C(j + t, t) • s_{j + t}` (`= 0` if `j + t > μ`). -/
theorem F_ess (t j : ℕ) (hj : j ≤ M) :
    Fop p L M t (ess p L M j) = ((j + t).choose t : ℚ_[p]) • ess p L M (j + t) := by
  ext (i' | j')
  · rw [Fop_inl]; simp [ess_inl, cL_ess]
  · rw [Fop_inr]; simp only [Pi.smul_apply, smul_eq_mul, ess_inr, cR_ess]
    split_ifs <;> first | omega | simp_all

/-- `E t ℓ_i = C(λ − i + t, t) • ℓ_{i − t}` if `t ≤ i`, else `0`. -/
theorem E_ell (t i : ℕ) (hi : i ≤ L) :
    Eop p L M t (ell p L M i) =
      if t ≤ i then ((L - i + t).choose t : ℚ_[p]) • ell p L M (i - t) else 0 := by
  ext (i' | j')
  · rw [Eop_inl, cL_ell]
    by_cases h2 : t ≤ i
    · rw [if_pos h2, Pi.smul_apply, ell_inl, smul_eq_mul]
      by_cases h1 : (i' : ℕ) + t = i
      · rw [if_pos ⟨h1, by omega⟩, if_pos (by omega),
          show L - ((i' : ℕ) + t) + t = L - i + t by omega]
      · rw [if_neg (by tauto), if_neg (by omega)]; simp
    · rw [if_neg h2, if_neg (by omega)]; simp
  · rw [Eop_inr]; split_ifs <;> simp [ell_inr, cR_ell]

/-- `E t s_j = C(μ − j + t, t) • s_{j − t}` if `t ≤ j`, else `0`. -/
theorem E_ess (t j : ℕ) (hj : j ≤ M) :
    Eop p L M t (ess p L M j) =
      if t ≤ j then ((M - j + t).choose t : ℚ_[p]) • ess p L M (j - t) else 0 := by
  ext (i' | j')
  · rw [Eop_inl]; split_ifs <;> simp [ess_inl, cL_ess]
  · rw [Eop_inr, cR_ess]
    by_cases h2 : t ≤ j
    · rw [if_pos h2, Pi.smul_apply, ess_inr, smul_eq_mul]
      by_cases h1 : (j' : ℕ) + t = j
      · rw [if_pos ⟨h1, by omega⟩, if_pos (by omega),
          show M - ((j' : ℕ) + t) + t = M - j + t by omega]
      · rw [if_neg (by tauto), if_neg (by omega)]; simp
    · rw [if_neg h2, if_neg (by omega)]; simp

/-- `P w ℓ_i = ℓ_i` if `λ − 2i = w`, else `0`. -/
theorem P_ell (w : ℤ) (i : ℕ) (hi : i ≤ L) :
    Pop p L M w (ell p L M i) = if (L : ℤ) - 2 * i = w then ell p L M i else 0 := by
  ext (i' | j')
  · rw [Pop_apply]; simp only [wt]
    by_cases h : (i' : ℕ) = i
    · subst h; split_ifs <;> simp [ell_inl]
    · split_ifs <;> simp [ell_inl, h]
  · rw [Pop_apply]; split_ifs <;> simp [ell_inr]

/-- `P w s_j = s_j` if `μ − 2j = w`, else `0`. -/
theorem P_ess (w : ℤ) (j : ℕ) (hj : j ≤ M) :
    Pop p L M w (ess p L M j) = if (M : ℤ) - 2 * j = w then ess p L M j else 0 := by
  ext (i' | j')
  · rw [Pop_apply]; split_ifs <;> simp [ess_inl]
  · rw [Pop_apply]; simp only [wt]
    by_cases h : (j' : ℕ) = j
    · subst h; split_ifs <;> simp [ess_inr]
    · split_ifs <;> simp [ess_inr, h]

end ColouredSand.Glue
