module

public import RequestProject.Glue.Stability
public import RequestProject.Blocks.Block

/-!
# (G5) The basis and the operator, (G6) Lemma 8 on the lattice (CSG2, §1 (G5), (G6), §2 "*(G5)*")

Here `x₀ = xzero p r a = p^(−ν)`, `O = Oop p λ μ q c k r = Hq + F 1`.

* `G5a_basis`: the family `b (inl i) = ℓ_i`, `b (inr j) = s̃ x₀ j` is a `ℤ_[p]`-basis of `Lx x₀`
  (the basis `glueBasis`; in fact for every `x`, see `RequestProject/Glue/Lattice.lean`).
* `G5b_maps`: `O` maps `Lx x₀` into itself; `Orestr` is the restriction `O' : Lx x₀ → Lx x₀`
  (a `ℤ_[p]`-linear map).
* `G5b_matrix`: the matrix of `O'` in the basis `b` (Mathlib's `LinearMap.toMatrix`, column `y` =
  coordinates of `O (b y)`) is `Mblk p q c k r a`.
* `G6_B1`, `G6_B2`: the cokernel `Lx x₀ ⧸ range O'` is isomorphic (as an additive group) to the
  groups of `B1` (when `1 ≤ v_p(q)`, `1 ≤ c + k`) and `B2` (when `c = k = 0`).
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

/-! ### `O` on the generators -/

lemma Hop_ell (q c k r i : ℕ) :
    Hop p L M q c k r (ell p L M i) = ((Nt p q c k i : ℤ_[p]) : ℚ_[p]) • ell p L M i := by
  ext (i' | j')
  · rw [Hop_apply, Pi.smul_apply, ell_inl, smul_eq_mul]
    split_ifs with h
    · simp only [h]
    · simp
  · rw [Hop_apply, Pi.smul_apply, ell_inr]; simp

lemma Hop_stilde (q c k r : ℕ) (x : ℚ_[p]) (j : ℕ) :
    Hop p L M q c k r (stilde p L M r x j) =
      ((Nt p q c k (j + r) : ℤ_[p]) : ℚ_[p]) • stilde p L M r x j := by
  ext (i' | j')
  · rw [Hop_apply, Pi.smul_apply, stilde_inl, smul_eq_mul]
    split_ifs with h
    · simp only [h.2]
    · simp
  · rw [Hop_apply, Pi.smul_apply, stilde_inr, smul_eq_mul]
    split_ifs with h
    · simp only [h]
    · simp

lemma Phi_stilde_all (r : ℕ) (x : ℚ_[p]) (j : ℕ) :
    Phi p L M r x (stilde p L M r x j) = ess p L M j := by
  by_cases hj : j ≤ M
  · exact Phi_stilde r x j hj
  · rw [stilde, if_neg hj, map_zero, ess, dif_neg hj]

/-- `Phi (O ℓ_i) = N_i ℓ_i + (i + 1) ℓ_{i+1}`. -/
lemma Phi_Oop_ell (q c k r : ℕ) (x : ℚ_[p]) (i : ℕ) (hi : i ≤ L) :
    Phi p L M r x (Oop p L M q c k r (ell p L M i)) =
      ((Nt p q c k i : ℤ_[p]) : ℚ_[p]) • ell p L M i + ((i + 1 : ℕ) : ℚ_[p]) • ell p L M (i + 1) := by
  rw [Oop, LinearMap.add_apply, Hop_ell, F_ell 1 i hi, map_add, LinearMap.map_smul,
    LinearMap.map_smul, Phi_ell, Phi_ell, Nat.choose_one_right]

/-- `Phi (O s̃_j) = N_{j+r} s_j + (j + 1) s_{j+1} + (x β_F(j, 1)) ℓ_{j+r+1}`. -/
lemma Phi_Oop_stilde (q c k r : ℕ) (hLM : L = M + 2 * r) (x : ℚ_[p]) (j : ℕ) (hj : j ≤ M) :
    Phi p L M r x (Oop p L M q c k r (stilde p L M r x j)) =
      ((Nt p q c k (j + r) : ℤ_[p]) : ℚ_[p]) • ess p L M j +
        ((j + 1 : ℕ) : ℚ_[p]) • ess p L M (j + 1) +
        (x * (betaF L M r j 1 : ℚ_[p])) • ell p L M (j + r + 1) := by
  rw [Oop, LinearMap.add_apply, Hop_stilde, F_stilde r hLM x 1 j hj, map_add, map_add,
    LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, Phi_stilde_all, Phi_stilde_all,
    Phi_ell, Nat.choose_one_right, ← add_assoc]

/-! ### The numbers -/

lemma norm_xzero (r a : ℕ) : ‖xzero p r a‖ = (p : ℝ) ^ nu p r a := by
  rw [xzero, Padic.norm_p_zpow, neg_neg, zpow_natCast]

/-- `x₀ C(μ + r, μ) (μ + r + 1) = u` (the glue entry of `Mblk`). -/
lemma xzero_glue {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) :
    xzero p r a * (((mu p r a + r).choose (mu p r a) * (mu p r a + r + 1) : ℕ) : ℚ_[p]) =
      (uGlue p r a : ℚ_[p]) := by
  obtain ⟨hmu, _⟩ := mu_add (p := p) r a hrp hra
  have hdvd := (glue_exponent_N (p := p) hr1 hrp ha hra).2.1
  have hu : uGlue p r a * p ^ nu p r a =
      (mu p r a + r).choose (mu p r a) * (a + 1) * p := by
    unfold uGlue; exact Nat.div_mul_cancel hdvd
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [hmu, xzero, zpow_neg, zpow_natCast, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hp0)]
  have := congrArg (fun n : ℕ => (n : ℚ_[p])) hu
  push_cast at this ⊢
  rw [mul_comm ((p : ℚ_[p]) ^ _), this]; ring

/-- `x₀ β_F(j, 1)` is `0` for `j < μ` and the glue entry `u` for `j = μ`. -/
lemma xzero_betaF {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (j : ℕ) (hj : j ≤ mu p r a) :
    xzero p r a * (betaF (lam p r a) (mu p r a) r j 1 : ℚ_[p]) =
      if j = mu p r a then (uGlue p r a : ℚ_[p]) else 0 := by
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  unfold betaF
  by_cases h1 : j = mu p r a
  · subst h1
    rw [if_pos (by omega), if_neg (by omega), if_pos rfl, ← xzero_glue hr1 hrp ha hra, sub_zero,
      Nat.choose_one_right]
    push_cast; ring
  · rw [if_pos (by omega), if_pos (by omega), if_neg h1, choose_glue_comm, sub_self]; simp

/-! ### (G5) -/

/-- **(G5)(a) The basis.**  `b (inl i) = ℓ_i`, `b (inr j) = s̃ x₀ j` is a `ℤ_[p]`-basis of
`Lx x₀`. -/
theorem G5a_basis (r a : ℕ) :
    (∀ i : Fin (lam p r a + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inl i) : V p (lam p r a) (mu p r a)) =
        ell p (lam p r a) (mu p r a) i) ∧
    (∀ j : Fin (mu p r a + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inr j) : V p (lam p r a) (mu p r a)) =
        stilde p (lam p r a) (mu p r a) r (xzero p r a) j) :=
  ⟨glueBasis_inl r _, glueBasis_inr r _⟩

/-- **(G5)(b), first part.**  `O = Hq + F 1` maps `Lx x₀` into itself. -/
theorem G5b_maps {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    ∀ v ∈ Lx p (lam p r a) (mu p r a) r (xzero p r a),
      Oop p (lam p r a) (mu p r a) q c k r v ∈ Lx p (lam p r a) (mu p r a) r (xzero p r a) := by
  intro v hv
  have hS := (G1_stability_threshold hr1 hrp ha hra (xzero p r a)).2 (norm_xzero r a).le
  rw [Oop, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ (hS.1 1 le_rfl v hv).1
  refine map_mem_Lx r _ _ ?_ ?_ v hv
  · intro i _
    rw [Hop_ell]; exact intCoe_smul_mem _ (ell_mem_Lx r _ i)
  · intro j _
    rw [Hop_stilde]; exact intCoe_smul_mem _ (stilde_mem_Lx r _ j)

/-- The restriction `O' : Lx x₀ → Lx x₀` of `O = Hq + F 1` (a `ℤ_[p]`-linear map). -/
noncomputable def Orestr {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    Lx p (lam p r a) (mu p r a) r (xzero p r a) →ₗ[ℤ_[p]]
      Lx p (lam p r a) (mu p r a) r (xzero p r a) :=
  ((Oop p (lam p r a) (mu p r a) q c k r).restrictScalars ℤ_[p]).restrict
    (G5b_maps hr1 hrp ha hra q c k)

/-- **(G5)(b), second part.**  The matrix of `O'` in the basis `b` is `Mblk p q c k r a`. -/
theorem G5b_matrix {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    LinearMap.toMatrix (glueBasis p (lam p r a) (mu p r a) r (xzero p r a))
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a)) (Orestr hr1 hrp ha hra q c k) =
      Mblk p q c k r a := by
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  obtain ⟨hmu, _⟩ := mu_add (p := p) r a hrp hra
  ext y' y
  rw [LinearMap.toMatrix_apply]
  apply Subtype.ext
  rw [glueBasis_repr]
  show Phi p (lam p r a) (mu p r a) r (xzero p r a) (Oop p (lam p r a) (mu p r a) q c k r
    (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a))) y' = _
  rcases y with i | j
  · rw [glueBasis_inl, Phi_Oop_ell q c k r _ i (Nat.le_of_lt_succ i.2)]
    rcases y' with i' | j'
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ell_inl, ell_inl, smul_eq_mul, smul_eq_mul]
      simp only [Mblk, Matrix.of_apply]
      by_cases h1 : i' = i
      · rw [if_pos h1, if_pos (congrArg Fin.val h1), if_neg (by rw [h1]; omega)]; simp
      · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
        by_cases h2 : (i' : ℕ) = i + 1
        · rw [if_pos h2, if_pos h2]; push_cast; ring
        · rw [if_neg h2, if_neg h2]; simp
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ell_inr, ell_inr]
      simp [Mblk]
  · rw [glueBasis_inr, Phi_Oop_stilde q c k r hLM _ j (Nat.le_of_lt_succ j.2),
      xzero_betaF hr1 hrp ha hra j (Nat.le_of_lt_succ j.2)]
    rcases y' with i' | j'
    · rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ess_inl,
        ess_inl, ell_inl, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      simp only [Mblk, Matrix.of_apply]
      by_cases h1 : (j : ℕ) = mu p r a
      · rw [if_pos h1]
        by_cases h2 : (i' : ℕ) = mu p r a + r + 1
        · rw [if_pos (by omega), if_pos ⟨h1, h2⟩]; simp
        · rw [if_neg (by omega), if_neg (fun h => h2 h.2)]; simp
      · rw [if_neg h1]; simp [h1]
    · rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ess_inr,
        ess_inr, ell_inr, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      simp only [Mblk, Matrix.of_apply]
      by_cases h1 : j' = j
      · rw [if_pos h1, if_pos (congrArg Fin.val h1), if_neg (by rw [h1]; omega)]; simp
      · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
        by_cases h2 : (j' : ℕ) = j + 1
        · rw [if_pos h2, if_pos h2]; push_cast; ring
        · rw [if_neg h2, if_neg h2]; simp

/-! ### (G6) -/

/-- The cokernel of `O'` is the cokernel of `Mblk`. -/
noncomputable def cokerEquiv {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    (Lx p (lam p r a) (mu p r a) r (xzero p r a) ⧸
        LinearMap.range (Orestr hr1 hrp ha hra q c k)) ≃ₗ[ℤ_[p]]
      ((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) :=
  Submodule.Quotient.equiv _ _
    (glueBasis p (lam p r a) (mu p r a) r (xzero p r a)).equivFun (by
      set b := glueBasis p (lam p r a) (mu p r a) r (xzero p r a) with hb
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
      constructor
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        refine ⟨b.equivFun v, ?_⟩
        rw [← G5b_matrix hr1 hrp ha hra q c k]
        exact LinearMap.toMatrix_mulVec_repr _ _ _ v
      · rintro ⟨z, rfl⟩
        refine ⟨_, ⟨b.equivFun.symm z, rfl⟩, ?_⟩
        have h2 : ⇑(b.repr (b.equivFun.symm z)) = z := b.equivFun.apply_symm_apply z
        change ⇑(b.repr (Orestr hr1 hrp ha hra q c k (b.equivFun.symm z))) = _
        rw [← LinearMap.toMatrix_mulVec_repr b b, G5b_matrix hr1 hrp ha hra q c k, h2])

/-- **(G6) Lemma 8 on the lattice, case (B1)** (`1 ≤ v_p(q)`, `1 ≤ c + k`):
`Lx x₀ ⧸ range O' ≃+ (ℤ/p)^{2a} ⊕ ℤ/p^x ⊕ ℤ/p^y`. -/
theorem G6_B1 {q c k r a : ℕ} (hq : 1 ≤ padicValNat p q) (hck : 1 ≤ c + k) (hr1 : 1 ≤ r)
    (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty ((Lx p (lam p r a) (mu p r a) r (xzero p r a) ⧸
        LinearMap.range (Orestr hr1 hrp ha hra q c k)) ≃+
      (Fin (2 * a) → ZMod p) × ZMod (p ^ blkX p q c k r a) × ZMod (p ^ blkY p q c k r a)) := by
  obtain ⟨E⟩ := B1 (c := c) (k := k) hq hck hr1 hrp ha hra
  exact ⟨(cokerEquiv hr1 hrp ha hra q c k).toAddEquiv.trans E⟩

/-- **(G6) Lemma 8 on the lattice, case (B2)** (`c = k = 0`):
`Lx x₀ ⧸ range O' ≃+ ℤ_[p] ⊕ (ℤ/p)^{2a} ⊕ ℤ/p^{min E₁₂ E₂₂}`. -/
theorem G6_B2 {q c k r a : ℕ} (hq : 1 ≤ padicValNat p q) (hc : c = 0) (hk : k = 0)
    (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty ((Lx p (lam p r a) (mu p r a) r (xzero p r a) ⧸
        LinearMap.range (Orestr hr1 hrp ha hra q c k)) ≃+
      ℤ_[p] × (Fin (2 * a) → ZMod p) × ZMod (p ^ min (E12 p q c k r a) (E22 p q c k r a))) := by
  obtain ⟨E⟩ := B2 (c := c) (k := k) hq hc hk hr1 hrp ha hra
  exact ⟨(cokerEquiv hr1 hrp ha hra q c k).toAddEquiv.trans E⟩

end ColouredSand.Glue
