module

public import RequestProject.BlockOp.Operator
public import RequestProject.Glue.Operator

/-!
# `CSG6_operator_on_the_blocks.md`, Part E — the operator on one summand is a matrix of Lemma 8

Namespace `ColouredSand.BlockOp`.

## Encodings

* `opT p M m q c` is the operator of (K1) (`RequestProject/BlockOp/Operator.lean`).
* `DPLattice.delta ℤ_[p] λ` is `Δ(λ)`, with basis `Fin (λ + 1)` (`e_i` of weight `λ − 2i`,
  `F^{(1)} e_i = (i + 1) e_{i+1}`); `Tglue p r a` is the glued lattice of CSG3, with basis
  `Fin (λ + 1) ⊕ Fin (μ + 1)` (`λ = lam p r a`, `μ = mu p r a`).  The matrices `Mch`, `Mblk` are
  those of `RequestProject/Blocks/Defs.lean` (column `y` = image of the basis vector `y`), acting
  by `Matrix.mulVecLin`.
* The level offset is `k`; on a summand `T(λ)` of `V^{⊗m}`, `m = λ + 2k`.
* `coker f := (ι → ℤ_[p]) ⧸ LinearMap.range f`.
* As `opT` contains `half p` (with `2 * half p = 1` only for `p ≠ 2`), (E1)–(E3) assume
  `p ≠ 2`.  The file allows `p = 2` in (E1), but with the operator `opT` of (K1) this fails at
  `p = 2`: there `half 2 = 0` (`2` is not a unit of `ℤ_[2]`), and `E1_false_at_two` proves that
  (E1) is false for `λ = 0`, `k = 1`, `q = 1`, `c = 0`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.BlockOp

open ColouredSand.TiltP ColouredSand.Blocks ColouredSand.Glue DPLattice

variable {p : ℕ} [Fact p.Prime]

/-! ### (E1) -/

/-- `Mch = (matrix of F^{(1)} on Δ(λ)) + diag(N_i)` (auxiliary for (E1)). -/
lemma Mch_eq (q c k lam : ℕ) :
    Mch p q c k lam =
      deltaMatF (A := ℤ_[p]) lam 1 + Matrix.diagonal (fun i : Fin (lam + 1) => Nt p q c k i) := by
  ext i' i
  simp only [Mch, Matrix.of_apply, Matrix.add_apply, deltaMatF, Matrix.diagonal_apply]
  by_cases h1 : i' = i
  · subst h1; simp
  · rw [if_neg h1, if_neg h1, add_zero]
    by_cases h2 : (i' : ℕ) = i + 1
    · rw [if_pos h2, if_pos h2, Nat.choose_one_right]; push_cast; ring
    · rw [if_neg h2, if_neg h2]

/-- **(E1) simple blocks** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2` and every
`λ k q c`, `opT (Δ(λ)) (λ + 2k) q c = Mch p q c k λ` (as endomorphisms of
`Fin (λ + 1) → ℤ_[p]`).  The diagonal entry at `e_i` (weight `λ − 2i`) is
`q (c + k + i) = Nt p q c k i`. -/
theorem E1 (hp2 : p ≠ 2) (lam k q c : ℕ) :
    opT p (delta ℤ_[p] lam) (lam + 2 * k) q c = Matrix.mulVecLin (Mch p q c k lam) := by
  have h2 := two_mul_half (p := p) hp2
  refine LinearMap.ext fun v => funext fun (i : Fin (lam + 1)) => ?_
  rw [Mch_eq]
  change opT p (delta ℤ_[p] lam) (lam + 2 * k) q c v i = Matrix.mulVec (deltaMatF (A := ℤ_[p]) lam 1 +
    Matrix.diagonal (fun i : Fin (lam + 1) => Nt p q c k i)) v i
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, opT_apply]
  change Matrix.toLin' (deltaMatF lam 1) v i + _ = _
  simp only [Matrix.toLin'_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    DPLattice.Hop_apply, smul_eq_mul, Nt]
  change _ + (q : ℤ_[p]) * ((c : ℤ_[p]) * v i + half p * ((((lam + 2 * k : ℕ) : ℤ_[p])) * v i -
    ((weylWt lam i : ℤ) : ℤ_[p]) * v i)) = _
  simp only [weylWt]
  push_cast
  linear_combination ((q : ℤ_[p]) * ((k : ℤ_[p]) + (i : ℤ_[p])) * v i) * h2

/-- `2` is not a unit in `ℤ_[2]`, so `half 2 = 0` (auxiliary for the remark on (E1)). -/
lemma half_two : half 2 = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnu : ¬ IsUnit (2 : ℤ_[2]) := by
    rw [PadicInt.not_isUnit_iff]
    have h : ‖((2 : ℕ) : ℤ_[2])‖ ≠ 1 := by
      rw [Ne, PadicInt.norm_natCast_eq_one_iff]; decide
    have hle : ‖((2 : ℕ) : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    exact_mod_cast lt_of_le_of_ne hle h
  exact Ring.inverse_non_unit _ hnu

/-- **Remark on (E1)** of `CSG6_operator_on_the_blocks.md`: with the operator `opT` of (K1)
(which uses `half p = Ring.inverse 2`), (E1) fails at `p = 2`: for `λ = 0`, `k = 1`, `q = 1`,
`c = 0`, `opT (Δ(0)) 2 1 0 = 0` while `Mch 2 1 0 1 0 = (1)`.  Hence (E1)–(E3) are stated for
`p ≠ 2`. -/
theorem E1_false_at_two :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    opT 2 (delta ℤ_[2] 0) (0 + 2 * 1) 1 0 ≠ Matrix.mulVecLin (Mch 2 1 0 1 0) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => 1)) (show (delta ℤ_[2] 0).ι from (0 : Fin 1))
  rw [opT_apply, half_two] at this
  change _ = Matrix.mulVec (Mch 2 1 0 1 0) (fun _ => 1) (0 : Fin 1) at this
  have hF : (delta ℤ_[2] 0).Fd 1 (fun _ => 1) (0 : Fin 1) = 0 := by
    change deltaF 0 1 (fun _ => (1 : ℤ_[2])) (0 : Fin 1) = 0
    simp [deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, deltaMatF]
  simp only [Pi.add_apply, Pi.smul_apply, hF] at this
  simp [Matrix.mulVec, dotProduct, Mch, Nt] at this

/-! ### (E2) -/

/-- The vector `Σ_y v y • b y ∈ V` of a coordinate vector `v` in the basis
`b = glueBasis p λ μ r x₀` (auxiliary for (E2)). -/
def glueVec (r a : ℕ) (v : Idx (lam p r a) (mu p r a) → ℤ_[p]) : V p (lam p r a) (mu p r a) :=
  ∑ y, v y • (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a))

lemma glueVec_eq (r a : ℕ) (v : Idx (lam p r a) (mu p r a) → ℤ_[p]) :
    glueVec r a v =
      ((glueBasis p (lam p r a) (mu p r a) r (xzero p r a)).equivFun.symm v :
        V p (lam p r a) (mu p r a)) := by
  rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
  rfl

lemma glueVec_injective (r a : ℕ) : Function.Injective (glueVec (p := p) r a) := by
  intro v w h
  rw [glueVec_eq, glueVec_eq] at h
  exact (glueBasis p _ _ r _).equivFun.symm.injective (Subtype.ext h)

/-- **(E2) two Weyl factors** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, under
`GlueHyp p r a`, and every `k q c`, `opT (Tglue p r a) (λ + 2k) q c = Mblk p q c k r a`
(`λ = lam p r a`; both endomorphisms of `Fin (λ + 1) ⊕ Fin (μ + 1) → ℤ_[p]`).  Proof: both sides
are carried by `v ↦ Σ_y v y • b y` (`b = glueBasis … (xzero p r a)`) to `O = Hq + F 1`, the
left side by `T1_Fd` and `Hop_ell`, `Hop_stilde`, the right side by `G5b_matrix`. -/
theorem E2 (hp2 : p ≠ 2) {r a : ℕ} (h : GlueHyp p r a) (k q c : ℕ) :
    opT p (Tglue p r a) (lam p r a + 2 * k) q c = Matrix.mulVecLin (Mblk p q c k r a) := by
  obtain ⟨hr1, hrp, ha, hra⟩ := h
  have h2 := two_mul_half (p := p) hp2
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  set b := glueBasis p (lam p r a) (mu p r a) r (xzero p r a) with hb
  refine LinearMap.ext fun v => glueVec_injective r a ?_
  -- the right-hand side
  have hR : glueVec r a (Matrix.mulVecLin (Mblk p q c k r a) v) =
      Oop p (lam p r a) (mu p r a) q c k r (glueVec r a v) := by
    have hm := LinearMap.toMatrix_mulVec_repr b b (Orestr hr1 hrp ha hra q c k)
      (b.equivFun.symm v)
    rw [G5b_matrix hr1 hrp ha hra q c k] at hm
    have hv : ⇑(b.repr (b.equivFun.symm v)) = v := b.equivFun.apply_symm_apply v
    rw [hv] at hm
    rw [Matrix.mulVecLin_apply, hm, glueVec_eq, glueVec_eq]
    change ((b.equivFun.symm (b.equivFun _)) : V p (lam p r a) (mu p r a)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine Eq.trans ?_ hR.symm
  -- the left-hand side
  have hF : glueVec r a ((Tglue p r a).Fd 1 v) = Fop p (lam p r a) (mu p r a) 1 (glueVec r a v) :=
    T1_Fd ⟨hr1, hrp, ha, hra⟩ 1 v
  have hdiag : ∀ y : Idx (lam p r a) (mu p r a),
      (q : ℤ_[p]) * ((c : ℤ_[p]) + half p * (((lam p r a + 2 * k : ℕ) : ℤ_[p]) -
        (((Tglue p r a).wt y : ℤ) : ℤ_[p]))) =
      match y with
      | .inl i => Nt p q c k i
      | .inr j => Nt p q c k ((j : ℕ) + r) := by
    intro y
    rcases y with i | j
    · simp only [Tglue_wt_inl, Nt]; push_cast
      linear_combination ((q : ℤ_[p]) * ((k : ℤ_[p]) + (i : ℤ_[p]))) * h2
    · simp only [Tglue_wt_inr, Nt]
      rw [hLM]; push_cast
      linear_combination ((q : ℤ_[p]) * ((k : ℤ_[p]) + (j : ℤ_[p]) + (r : ℤ_[p]))) * h2
  have hH : glueVec r a (opT p (Tglue p r a) (lam p r a + 2 * k) q c v -
      (Tglue p r a).Fd 1 v) = Hop p (lam p r a) (mu p r a) q c k r (glueVec r a v) := by
    simp only [glueVec, map_sum, LinearMap.map_smul_of_tower]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hy := hdiag y
    rw [opT_apply, add_sub_cancel_left]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rcases y with i | j
    · have key : (q : ℤ_[p]) * ((c : ℤ_[p]) * v (.inl i) + half p *
          (((lam p r a + 2 * k : ℕ) : ℤ_[p]) * v (.inl i) - DPLattice.H (Tglue p r a) v (.inl i))) =
          v (.inl i) * Nt p q c k i := by
        have hy' : (q : ℤ_[p]) * ((c : ℤ_[p]) + half p * (((lam p r a + 2 * k : ℕ) : ℤ_[p]) -
            (((Tglue p r a).wt (.inl i) : ℤ) : ℤ_[p]))) = Nt p q c k i := hy
        rw [DPLattice.Hop_apply]; linear_combination v (.inl i) * hy'
      rw [glueBasis_inl, Hop_ell, key, mul_smul]
      congr 1
    · have key : (q : ℤ_[p]) * ((c : ℤ_[p]) * v (.inr j) + half p *
          (((lam p r a + 2 * k : ℕ) : ℤ_[p]) * v (.inr j) - DPLattice.H (Tglue p r a) v (.inr j))) =
          v (.inr j) * Nt p q c k (j + r) := by
        have hy' : (q : ℤ_[p]) * ((c : ℤ_[p]) + half p * (((lam p r a + 2 * k : ℕ) : ℤ_[p]) -
            (((Tglue p r a).wt (.inr j) : ℤ) : ℤ_[p]))) = Nt p q c k (j + r) := hy
        rw [DPLattice.Hop_apply]; linear_combination v (.inr j) * hy'
      rw [glueBasis_inr, Hop_stilde, key, mul_smul]
      congr 1
  have hlin : ∀ w w' : Idx (lam p r a) (mu p r a) → ℤ_[p],
      glueVec r a (w + w') = glueVec r a w + glueVec r a w' := fun w w' => by
    simp only [glueVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [Oop, LinearMap.add_apply, ← hF, ← hH, ← hlin, sub_add_cancel]

/-! ### (E3) -/

/-- Equal DP-lattices have isomorphic cokernels of `opT` (auxiliary for (E3)). -/
def cokerOfEq {M N : DPLattice ℤ_[p]} (h : M = N) (m q c : ℕ) :
    ((M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m q c)) ≃ₗ[ℤ_[p]]
      ((N.ι → ℤ_[p]) ⧸ LinearMap.range (opT p N m q c)) := by
  subst h; exact LinearEquiv.refl _ _

/-- (E3)(a), with `m = λ + 2k` given explicitly. -/
def E3a_equiv (hp2 : p ≠ 2) {lam : ℕ} (hs : IsSimpleWt p lam) (k q c : ℕ) :
    ((((Ttilt p lam).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p lam) (lam + 2 * k) q c))) ≃ₗ[ℤ_[p]]
      ((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) :=
  (cokerOfEq (Ttilt_of_simple p hs) _ q c).trans
    (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (E1 hp2 lam k q c)))

/-- (E3)(b), with `m = lam p r a + 2k` given explicitly. -/
def E3b_equiv (hp2 : p ≠ 2) {l : ℕ} (hns : ¬ IsSimpleWt p l)
    (hg : GlueHyp p (rT p l) (aT p l)) (k q c : ℕ) :
    ((((Ttilt p l).ι → ℤ_[p]) ⧸
        LinearMap.range (opT p (Ttilt p l) (lam p (rT p l) (aT p l) + 2 * k) q c))) ≃ₗ[ℤ_[p]]
      ((Fin (lam p (rT p l) (aT p l) + 1) ⊕ Fin (mu p (rT p l) (aT p l) + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mblk p q c k (rT p l) (aT p l)))) :=
  (cokerOfEq (Ttilt_of_not_simple p hns) _ q c).trans
    (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (E2 hp2 hg k q c)))

lemma m_eq_of_parity {lam m : ℕ} (hle : lam ≤ m) (hpar : lam % 2 = m % 2) :
    m = lam + 2 * ((m - lam) / 2) := by omega

/-- **(E3)(a)** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, `IsSimpleWt p λ`, `λ ≤ m`,
`λ ≡ m (mod 2)`, `k = (m − λ)/2` and every `q c`,
`coker (opT (Ttilt p λ) m q c) ≃ₗ[ℤ_[p]] coker (Mch p q c k λ)`.
(More general than the file: the bound `λ ≤ p² + p − 1` is not needed here.) -/
theorem E3a (hp2 : p ≠ 2) {lam m : ℕ} (hs : IsSimpleWt p lam) (hle : lam ≤ m)
    (hpar : lam % 2 = m % 2) (q c : ℕ) :
    Nonempty ((((Ttilt p lam).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p lam) m q c)) ≃ₗ[ℤ_[p]]
      ((Fin (lam + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mch p q c ((m - lam) / 2) lam)))) := by
  have hm := m_eq_of_parity hle hpar
  generalize (m - lam) / 2 = k at hm ⊢
  subst hm
  exact ⟨E3a_equiv hp2 hs k q c⟩

/-- **(E3)(b)** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, `λ ≤ p² + p − 1`,
`¬ IsSimpleWt p λ`, `λ ≤ m`, `λ ≡ m (mod 2)`, `k = (m − λ)/2` and every `q c`,
`coker (opT (Ttilt p λ) m q c) ≃ₗ[ℤ_[p]] coker (Mblk p q c k (rT p λ) (aT p λ))`
(the index type of the right side is `Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1)`, and
`lam p r a = λ` by CSG3 `T3`). -/
theorem E3b (hp2 : p ≠ 2) {l m : ℕ} (hl : l ≤ p ^ 2 + p - 1) (hns : ¬ IsSimpleWt p l)
    (hle : l ≤ m) (hpar : l % 2 = m % 2) (q c : ℕ) :
    Nonempty ((((Ttilt p l).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p l) m q c)) ≃ₗ[ℤ_[p]]
      ((Fin (lam p (rT p l) (aT p l) + 1) ⊕ Fin (mu p (rT p l) (aT p l) + 1) → ℤ_[p]) ⧸
        LinearMap.range
          (Matrix.mulVecLin (Mblk p q c ((m - l) / 2) (rT p l) (aT p l))))) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨-, hr1, hrp, ha, hra, hlam⟩ := TiltP.T3 hp hns hl
  have hm := m_eq_of_parity hle hpar
  generalize (m - l) / 2 = k at hm ⊢
  subst hm
  have e1 : (((Ttilt p l).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p l) (l + 2 * k) q c))
      ≃ₗ[ℤ_[p]] (((Ttilt p l).ι → ℤ_[p]) ⧸
        LinearMap.range (opT p (Ttilt p l) (lam p (rT p l) (aT p l) + 2 * k) q c)) :=
    Submodule.quotEquivOfEq _ _ (by rw [hlam])
  exact ⟨e1.trans (E3b_equiv hp2 hns ⟨hr1, hrp, ha, hra⟩ k q c)⟩

end ColouredSand.BlockOp
