module

public import RequestProject.Glue.Coords

/-!
# Membership in the glued lattice and its basis (CSG2, §0 and (G5)(a))

The "untwisting" map `Phi r x : V → V` subtracts from the `ℓ`-coordinates the glue
contribution: `(Phi v)(inl i) = v(inl i) − x C(i, i − r) v(inr (i − r))` (when
`r ≤ i ≤ μ + r`) and `(Phi v)(inr j) = v(inr j)`.  It sends `ℓ_i ↦ ℓ_i` and `s̃ x j ↦ s_j`, and
its inverse `Psi r x` sends `ℓ_i ↦ ℓ_i`, `s_j ↦ s̃ x j`.

* `mem_Lx_iff`: `v ∈ Lx x ↔` all coordinates of `Phi v` have norm `≤ 1` (are in `ℤ_[p]`).
* `glueBasis r x : Basis (Idx L M) ℤ_[p] (Lx x)` with `glueBasis (inl i) = ℓ_i` and
  `glueBasis (inr j) = s̃ x j` (`glueBasis_inl`, `glueBasis_inr`).  This is (G5)(a), for every
  `x : ℚ_[p]`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

lemma padic_smul_eq (c : ℤ_[p]) (z : ℚ_[p]) : c • z = (c : ℚ_[p]) * z := by
  rw [Algebra.smul_def, PadicInt.algebraMap_apply]

lemma padic_smul_apply (c : ℤ_[p]) (v : V p L M) (y : Idx L M) :
    (c • v) y = (c : ℚ_[p]) * v y := by
  rw [Pi.smul_apply, padic_smul_eq]

lemma padic_smul_vec (c : ℤ_[p]) (v : V p L M) : c • v = (c : ℚ_[p]) • v := by
  ext y; rw [padic_smul_apply]; rfl

/-- The glue factor `g(i) = C(i, i − r)` if `r ≤ i`, else `0`. -/
noncomputable def gl (r i : ℕ) : ℚ_[p] := if r ≤ i then ((i.choose (i - r) : ℕ) : ℚ_[p]) else 0

variable (p L M) in
/-- The untwisting map (`ℓ_i ↦ ℓ_i`, `s̃ x j ↦ s_j`). -/
noncomputable def Phi (r : ℕ) (x : ℚ_[p]) : V p L M →ₗ[ℚ_[p]] V p L M where
  toFun v := fun y => match y with
    | .inl i => v (.inl i) - x * gl r i * cR v (i - r)
    | .inr j => v (.inr j)
  map_add' v w := by
    ext (i | j)
    · simp only [Pi.add_apply, cR]; split_ifs <;> ring
    · rfl
  map_smul' c v := by
    ext (i | j)
    · simp only [Pi.smul_apply, smul_eq_mul, cR, RingHom.id_apply]; split_ifs <;> ring
    · rfl

variable (p L M) in
/-- The inverse of `Phi` (`ℓ_i ↦ ℓ_i`, `s_j ↦ s̃ x j`). -/
noncomputable def Psi (r : ℕ) (x : ℚ_[p]) : V p L M →ₗ[ℚ_[p]] V p L M where
  toFun v := fun y => match y with
    | .inl i => v (.inl i) + x * gl r i * cR v (i - r)
    | .inr j => v (.inr j)
  map_add' v w := by
    ext (i | j)
    · simp only [Pi.add_apply, cR]; split_ifs <;> ring
    · rfl
  map_smul' c v := by
    ext (i | j)
    · simp only [Pi.smul_apply, smul_eq_mul, cR, RingHom.id_apply]; split_ifs <;> ring
    · rfl

lemma Phi_inl (r : ℕ) (x : ℚ_[p]) (v : V p L M) (i : Fin (L + 1)) :
    Phi p L M r x v (.inl i) = v (.inl i) - x * gl r i * cR v (i - r) := rfl

lemma Phi_inr (r : ℕ) (x : ℚ_[p]) (v : V p L M) (j : Fin (M + 1)) :
    Phi p L M r x v (.inr j) = v (.inr j) := rfl

lemma Psi_inl (r : ℕ) (x : ℚ_[p]) (v : V p L M) (i : Fin (L + 1)) :
    Psi p L M r x v (.inl i) = v (.inl i) + x * gl r i * cR v (i - r) := rfl

lemma Psi_inr (r : ℕ) (x : ℚ_[p]) (v : V p L M) (j : Fin (M + 1)) :
    Psi p L M r x v (.inr j) = v (.inr j) := rfl

lemma cR_Phi (r : ℕ) (x : ℚ_[p]) (v : V p L M) (n : ℕ) : cR (Phi p L M r x v) n = cR v n := by
  unfold cR; split_ifs <;> rfl

lemma cR_Psi (r : ℕ) (x : ℚ_[p]) (v : V p L M) (n : ℕ) : cR (Psi p L M r x v) n = cR v n := by
  unfold cR; split_ifs <;> rfl

lemma Phi_Psi (r : ℕ) (x : ℚ_[p]) (v : V p L M) : Phi p L M r x (Psi p L M r x v) = v := by
  ext (i | j)
  · rw [Phi_inl, cR_Psi, Psi_inl]; ring
  · rfl

lemma Psi_Phi (r : ℕ) (x : ℚ_[p]) (v : V p L M) : Psi p L M r x (Phi p L M r x v) = v := by
  ext (i | j)
  · rw [Psi_inl, cR_Phi, Phi_inl]; ring
  · rfl

lemma Phi_ell (r : ℕ) (x : ℚ_[p]) (i : ℕ) : Phi p L M r x (ell p L M i) = ell p L M i := by
  ext (i' | j)
  · rw [Phi_inl, cR_ell]; ring
  · rfl

lemma choose_shift_aux (i j r : ℕ) (h : i = j + r) :
    ((i.choose (i - r) : ℕ) : ℚ_[p]) = ((j + r).choose j : ℕ) := by
  subst h; rw [show j + r - r = j by omega]

lemma Phi_stilde (r : ℕ) (x : ℚ_[p]) (j : ℕ) (hj : j ≤ M) :
    Phi p L M r x (stilde p L M r x j) = ess p L M j := by
  ext (i' | j')
  · rw [Phi_inl, cR_stilde, stilde_inl, ess_inl, gl]
    by_cases h : (i' : ℕ) = j + r
    · rw [if_pos ⟨hj, h⟩, if_pos (by omega), if_pos ⟨by omega, by omega⟩,
        choose_shift_aux (p := p) _ _ _ h]; ring
    · rw [if_neg (by tauto)]
      split_ifs <;> first | ring1 | (exfalso; omega)
  · rw [Phi_inr, stilde_inr, ess_inr]

lemma Psi_single_inl (r : ℕ) (x : ℚ_[p]) (i : Fin (L + 1)) :
    Psi p L M r x (Pi.single (.inl i) 1) = ell p L M i := by
  ext (i' | j')
  · rw [Psi_inl, ell_inl, cR]
    split_ifs with h1 h2 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff]
  · rw [Psi_inr, ell_inr]; simp

lemma Psi_single_inr (r : ℕ) (x : ℚ_[p]) (j : Fin (M + 1)) :
    Psi p L M r x (Pi.single (.inr j) 1) = stilde p L M r x j := by
  ext (i' | j')
  · rw [Psi_inl, stilde_inl, cR, gl]
    simp only [Pi.single_apply, reduceCtorEq, if_false, zero_add, Sum.inr.injEq]
    by_cases h : (i' : ℕ) = j + r
    · have hj := Nat.le_of_lt_succ j.2
      have e : (⟨(i' : ℕ) - r, by omega⟩ : Fin (M + 1)) = j := by ext; simp; omega
      rw [if_pos (show r ≤ (i' : ℕ) by omega), dif_pos (show (i' : ℕ) - r ≤ M by omega), if_pos e,
        if_pos ⟨hj, h⟩, choose_shift_aux (p := p) _ _ _ h]; ring
    · rw [if_neg (show ¬((j : ℕ) ≤ M ∧ (i' : ℕ) = j + r) by tauto)]
      split_ifs with h1 h2 h3
      all_goals first | ring1 | (exfalso; rw [Fin.ext_iff] at h3; simp at h3; omega)
  · rw [Psi_inr, stilde_inr]; simp [Pi.single_apply, Fin.ext_iff]

lemma ell_mem_Lx (r : ℕ) (x : ℚ_[p]) (i : ℕ) : ell p L M i ∈ Lx p L M r x := by
  by_cases hi : i ≤ L
  · apply Submodule.subset_span
    left; exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
  · rw [ell, dif_neg hi]; exact Submodule.zero_mem _

lemma stilde_mem_Lx (r : ℕ) (x : ℚ_[p]) (j : ℕ) : stilde p L M r x j ∈ Lx p L M r x := by
  by_cases hj : j ≤ M
  · apply Submodule.subset_span
    right; exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
  · rw [stilde, if_neg hj]; exact Submodule.zero_mem _

lemma Dlam_le_Lx (r : ℕ) (x : ℚ_[p]) : Dlam p L M ≤ Lx p L M r x := by
  rw [Dlam, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ell_mem_Lx r x i

/-- **Membership in `Lx x`**: `v ∈ Lx x` iff the untwisted vector `Phi v` has all its
coordinates in `ℤ_[p]`. -/
theorem mem_Lx_iff (r : ℕ) (x : ℚ_[p]) (v : V p L M) :
    v ∈ Lx p L M r x ↔ ∀ y, ‖Phi p L M r x v y‖ ≤ 1 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · rw [Phi_ell]; intro y
        rcases y with i' | j'
        · rw [ell_inl]; split_ifs <;> simp
        · rw [ell_inr]; simp
      · rw [Phi_stilde r x j (Nat.le_of_lt_succ j.2)]; intro y
        rcases y with i' | j'
        · rw [ess_inl]; simp
        · rw [ess_inr]; split_ifs <;> simp
    | zero => intro y; simp
    | add v w _ _ hv hw =>
      intro y; rw [map_add, Pi.add_apply]
      exact (Padic.nonarchimedean _ _).trans (max_le (hv y) (hw y))
    | smul c v _ hv =>
      intro y
      rw [LinearMap.map_smul_of_tower, padic_smul_apply, norm_mul]
      exact mul_le_one₀ (PadicInt.norm_le_one c) (norm_nonneg _) (hv y)
  · intro h
    set z : Idx L M → ℤ_[p] := fun y => ⟨Phi p L M r x v y, h y⟩ with hz
    have hv : v = ∑ y, z y • Psi p L M r x (Pi.single y 1) := by
      conv_lhs => rw [← Psi_Phi r x v, ← Finset.univ_sum_single (Phi p L M r x v)]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [show Pi.single y (Phi p L M r x v y) = (Phi p L M r x v y) • (Pi.single y 1 : V p L M) by
        rw [← Pi.single_smul, smul_eq_mul, mul_one], LinearMap.map_smul, padic_smul_vec]
    rw [hv]
    apply Submodule.sum_mem
    intro y _
    apply Submodule.smul_mem
    rcases y with i | j
    · rw [Psi_single_inl]; exact ell_mem_Lx r x i
    · rw [Psi_single_inr]; exact stilde_mem_Lx r x j

variable (p L M) in
/-- The coordinates in the basis `{ℓ_i} ∪ {s̃ x j}`. -/
noncomputable def glueEquiv (r : ℕ) (x : ℚ_[p]) :
    Lx p L M r x ≃ₗ[ℤ_[p]] (Idx L M → ℤ_[p]) where
  toFun v := fun y => ⟨Phi p L M r x (v : V p L M) y, (mem_Lx_iff r x (v : V p L M)).1 v.2 y⟩
  map_add' v w := by
    funext y
    apply Subtype.ext
    show Phi p L M r x ((v : V p L M) + w) y = Phi p L M r x v y + Phi p L M r x w y
    rw [map_add]; rfl
  map_smul' c v := by
    funext y
    apply Subtype.ext
    show Phi p L M r x (c • (v : V p L M)) y = (c : ℚ_[p]) * Phi p L M r x v y
    rw [LinearMap.map_smul_of_tower, padic_smul_apply]
  invFun z := ⟨Psi p L M r x (fun y => (z y : ℚ_[p])), by
    rw [mem_Lx_iff, Phi_Psi]; intro y; exact (z y).2⟩
  left_inv v := by
    apply Subtype.ext
    show Psi p L M r x (fun y => Phi p L M r x v y) = v
    exact Psi_Phi r x (v : V p L M)
  right_inv z := by
    funext y; apply Subtype.ext
    show Phi p L M r x (Psi p L M r x _) y = z y
    rw [Phi_Psi]

variable (p L M) in
/-- **The basis of `Lx x`** (G5)(a), for every `x : ℚ_[p]`. -/
noncomputable def glueBasis (r : ℕ) (x : ℚ_[p]) : Module.Basis (Idx L M) ℤ_[p] (Lx p L M r x) :=
  Module.Basis.ofEquivFun (glueEquiv p L M r x)

lemma glueBasis_coe (r : ℕ) (x : ℚ_[p]) (y : Idx L M) :
    (glueBasis p L M r x y : V p L M) = Psi p L M r x (Pi.single y 1) := by
  rw [glueBasis, Module.Basis.coe_ofEquivFun]
  show Psi p L M r x (fun y' => (((Pi.single y (1 : ℤ_[p]) : Idx L M → ℤ_[p]) y' : ℤ_[p]) : ℚ_[p])) = _
  have h : (fun y' => (((Pi.single y (1 : ℤ_[p]) : Idx L M → ℤ_[p]) y' : ℤ_[p]) : ℚ_[p])) = Pi.single y 1 := by
    funext y'
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h]

theorem glueBasis_inl (r : ℕ) (x : ℚ_[p]) (i : Fin (L + 1)) :
    (glueBasis p L M r x (.inl i) : V p L M) = ell p L M i := by
  rw [glueBasis_coe, Psi_single_inl]

theorem glueBasis_inr (r : ℕ) (x : ℚ_[p]) (j : Fin (M + 1)) :
    (glueBasis p L M r x (.inr j) : V p L M) = stilde p L M r x j := by
  rw [glueBasis_coe, Psi_single_inr]

lemma glueBasis_repr (r : ℕ) (x : ℚ_[p]) (v : Lx p L M r x) (y : Idx L M) :
    ((glueBasis p L M r x).repr v y : ℚ_[p]) = Phi p L M r x v y := by
  rw [glueBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

end ColouredSand.Glue
