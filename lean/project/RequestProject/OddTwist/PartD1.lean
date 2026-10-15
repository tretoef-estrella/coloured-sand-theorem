module

public import RequestProject.OddTwist.PartD

/-!
# `CSI1_the_odd_twist.md`: Part D, (D1) — `Φ_p(Δ_A(μ)) ≅ Δ_A(pμ + p − 1)`

`deltaMap p μ : Δ_A(λ) → Φ_p(Δ_A(μ))` (`λ = pμ + p − 1`) is `δ`, `e'_R ↦ c_R x_R`, and
`deltaInv p μ` is its inverse `x_R ↦ c_R^{-1} e'_R`; both are defined on basis vectors
(`Basis.constr`). The commutation with `F^{(1)}`, `E^{(1)}`, `H` is checked directly on the basis
vectors (`deltaMap_F`, `deltaMap_E`, `deltaMap_H`), and C20's `homOfOne` gives a morphism.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Doubling WeylFilt

open scoped Nat

variable (p : ℕ) [Fact p.Prime]

/-- (D1) `δ : Δ_A(λ) → Φ_p(Δ_A(μ))`, `e'_R ↦ c_R x_R` (defined on basis vectors). -/
def deltaMap (μ : ℕ) :
    ((delta ℤ_[p] (lam p μ)).ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × (delta ℤ_[p] μ).ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin (lam p μ + 1))).constr ℤ_[p] (fun R => cD p (R : ℕ) • xD p μ R)

/-- (D1) the inverse map `x_R ↦ c_R^{-1} e'_R` (defined on basis vectors). -/
def deltaInv (μ : ℕ) :
    (Fin p × (delta ℤ_[p] μ).ι → ℤ_[p]) →ₗ[ℤ_[p]] ((delta ℤ_[p] (lam p μ)).ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin p × Fin (μ + 1))).constr ℤ_[p]
    (fun x => cDinv p (xIdx p μ x : ℕ) • eD (lam p μ) (xIdx p μ x))

lemma deltaMap_eD (μ : ℕ) (R : Fin (lam p μ + 1)) :
    deltaMap p μ (eD (lam p μ) R) = cD p (R : ℕ) • xD p μ R := by
  show (Pi.basisFun ℤ_[p] (Fin (lam p μ + 1))).constr ℤ_[p] _ (Pi.single R 1) = _
  rw [← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma deltaInv_single (μ : ℕ) (x : Fin p × Fin (μ + 1)) :
    deltaInv p μ (Pi.single (x : Fin p × (delta ℤ_[p] μ).ι) 1) =
      cDinv p (xIdx p μ x : ℕ) • eD (lam p μ) (xIdx p μ x) := by
  show (Pi.basisFun ℤ_[p] (Fin p × Fin (μ + 1))).constr ℤ_[p] _ (Pi.single x 1) = _
  rw [← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma deltaInv_xD (μ : ℕ) (R : Fin (lam p μ + 1)) :
    deltaInv p μ (xD p μ R) = cDinv p (R : ℕ) • eD (lam p μ) R := by
  rw [xD_eq_single, deltaInv_single, xIdx_div_mod]

lemma deltaInv_deltaMap (μ : ℕ) : deltaInv p μ ∘ₗ deltaMap p μ = LinearMap.id := by
  refine ext_single fun R => ?_
  show deltaInv p μ (deltaMap p μ (eD (lam p μ) R)) = eD (lam p μ) R
  rw [deltaMap_eD, map_smul, deltaInv_xD, smul_smul, mul_comm (cD p _), cDinv_mul_cD, one_smul]

lemma deltaMap_deltaInv (μ : ℕ) : deltaMap p μ ∘ₗ deltaInv p μ = LinearMap.id := by
  refine ext_single fun x => ?_
  show deltaMap p μ (deltaInv p μ (Pi.single (x : Fin p × (delta ℤ_[p] μ).ι) 1)) = _
  rw [deltaInv_single, map_smul, deltaMap_eD, smul_smul, cDinv_mul_cD, one_smul, xD_xIdx]
  rfl

/-! ### Commutation with `F^{(1)}`, `E^{(1)}`, `H` -/

lemma deltaMap_F (μ : ℕ) (R : Fin (lam p μ + 1)) :
    deltaMap p μ ((delta ℤ_[p] (lam p μ)).Fd 1 (eD _ R)) =
      twFd p (delta ℤ_[p] μ) 1 (deltaMap p μ (eD _ R)) := by
  have hp := one_le_p p
  rw [deltaMap_eD, map_smul]
  set s := (R : ℕ) / p
  set j := (R : ℕ) % p
  have hRs : (R : ℕ) = p * s + j := (Nat.div_add_mod _ _).symm
  have hj : j < p := Nat.mod_lt _ (by omega)
  have hs : s < μ + 1 := div_lt_of_fin p μ R
  have hsμ : p * s ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
  rw [xD_eq p μ R ⟨s, hs⟩ j hRs hj]
  by_cases hj1 : j + 1 < p
  · have hR1 : (R : ℕ) + 1 < lam p μ + 1 := by
      show (R : ℕ) + 1 < p * μ + p - 1 + 1; omega
    rw [eD_F_lt _ R ⟨(R : ℕ) + 1, hR1⟩ rfl, map_smul, deltaMap_eD,
      xD_eq p μ ⟨(R : ℕ) + 1, hR1⟩ ⟨s, hs⟩ (j + 1) (by simp only; omega) hj1, F1_lt p _ hj1,
      smul_smul]
    congr 1
    exact succ_mul_cD_succ p (by omega)
  · have hjp : j = p - 1 := by omega
    have hmod : (R : ℕ) % p = p - 1 := hjp
    rw [hjp, F1_last]
    by_cases hsμ' : s = μ
    · have hRlam : (R : ℕ) = lam p μ := by
        show (R : ℕ) = p * μ + p - 1; rw [hRs, ← hsμ']; omega
      rw [eD_F_last _ R hRlam, eD_F_last μ ⟨s, hs⟩ hsμ']
      simp
    · have hs1 : s + 1 < μ + 1 := by omega
      have hR1 : (R : ℕ) + 1 < lam p μ + 1 := by
        show (R : ℕ) + 1 < p * μ + p - 1 + 1
        have : p * (s + 1) ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add_one] at this; omega
      have hRe : (R : ℕ) + 1 = p * (s + 1) := by rw [Nat.mul_add_one]; omega
      rw [eD_F_lt _ R ⟨(R : ℕ) + 1, hR1⟩ rfl, map_smul, deltaMap_eD,
        xD_eq p μ ⟨(R : ℕ) + 1, hR1⟩ ⟨s + 1, hs1⟩ 0 (by simp only; omega) (by omega),
        eD_F_lt μ ⟨s, hs⟩ ⟨s + 1, hs1⟩ rfl]
      simp only [map_smul, smul_smul]
      rw [cD_succ_wrap p hmod]
      congr 1
      have hc : (((R : ℕ) + 1 : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * ((s : ℤ_[p]) + 1) := by
        rw [hRe]; push_cast; ring
      rw [hc]; push_cast; ring

lemma deltaMap_E (μ : ℕ) (R : Fin (lam p μ + 1)) :
    deltaMap p μ ((delta ℤ_[p] (lam p μ)).Ed 1 (eD _ R)) =
      twEd p (delta ℤ_[p] μ) 1 (deltaMap p μ (eD _ R)) := by
  have hp := one_le_p p
  rw [deltaMap_eD, map_smul]
  set s := (R : ℕ) / p
  set j := (R : ℕ) % p
  have hRs : (R : ℕ) = p * s + j := (Nat.div_add_mod _ _).symm
  have hj : j < p := Nat.mod_lt _ (by omega)
  have hs : s < μ + 1 := div_lt_of_fin p μ R
  have hsμ : p * s ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
  have hRl : (R : ℕ) ≤ lam p μ := Nat.lt_succ_iff.mp R.isLt
  obtain ⟨t, ht⟩ : ∃ t, μ = s + t := ⟨μ - s, by omega⟩
  have hlam : lam p μ = p * s + p * t + p - 1 := by simp only [lam]; rw [ht, Nat.mul_add]
  rw [xD_eq p μ R ⟨s, hs⟩ j hRs hj]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, E1_zero]
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rw [eD_E_zero _ R (by rw [hRs, hs0, hj0]; simp), eD_E_zero μ ⟨s, hs⟩ hs0]
      simp
    · have hR1 : (R : ℕ) - 1 < lam p μ + 1 := by omega
      have hs1 : s - 1 < μ + 1 := by omega
      have hps : p ≤ p * s := Nat.le_mul_of_pos_right p hs0
      have hRe : (R : ℕ) - 1 = p * (s - 1) + (p - 1) := by rw [Nat.mul_sub_one]; omega
      have hmod : ((R : ℕ) - 1) % p = p - 1 := (div_mod_unique hRe (by omega)).2
      have hc : cD p (R : ℕ) = -cD p ((R : ℕ) - 1) := by
        have := cD_succ_wrap p hmod
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [eD_E_pos _ R ⟨(R : ℕ) - 1, hR1⟩ (by simp only; omega), map_smul, deltaMap_eD,
        xD_eq p μ ⟨(R : ℕ) - 1, hR1⟩ ⟨s - 1, hs1⟩ (p - 1) hRe (by omega),
        eD_E_pos μ ⟨s, hs⟩ ⟨s - 1, hs1⟩ (by simp only; omega)]
      simp only [map_smul, smul_smul]
      rw [hc]
      congr 1
      have e1 : lam p μ - (R : ℕ) + 1 = p * (t + 1) := by have := Nat.mul_add_one p t; omega
      have e2 : μ - s + 1 = t + 1 := by omega
      simp only [e1, e2]
      push_cast; ring
  · have hR1 : (R : ℕ) - 1 < lam p μ + 1 := by omega
    have hRe : (R : ℕ) - 1 = p * s + (j - 1) := by omega
    have hmod : ((R : ℕ) - 1) % p ≠ p - 1 := by
      rw [(div_mod_unique hRe (by omega)).2]; omega
    have hc := succ_mul_cD_succ p hmod
    rw [Nat.sub_add_cancel (by omega)] at hc
    rw [E1_pos p _ hj0 hj (wt_eD μ ⟨s, hs⟩), eD_FE, eD_E_pos _ R ⟨(R : ℕ) - 1, hR1⟩ (by simp only; omega),
      map_smul, deltaMap_eD, xD_eq p μ ⟨(R : ℕ) - 1, hR1⟩ ⟨s, hs⟩ (j - 1) hRe (by omega), ← hc]
    simp only [map_smul, smul_smul, ← add_smul]
    congr 1
    have e1 : lam p μ - (R : ℕ) + 1 + j = p * t + p := by omega
    have e1' : ((lam p μ - (R : ℕ) + 1 : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * t + p - j := by
      have : ((lam p μ - (R : ℕ) + 1 : ℕ) : ℤ_[p]) + j = (p : ℤ_[p]) * t + p := by
        exact_mod_cast e1
      linear_combination this
    have hRc : (((R : ℕ) : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * s + j := by rw [hRs]; push_cast; ring
    rw [e1', hRc]
    simp only [ht, Nat.add_sub_cancel_left]
    push_cast; ring

lemma deltaMap_H (μ : ℕ) (R : Fin (lam p μ + 1)) :
    deltaMap p μ (Hop (delta ℤ_[p] (lam p μ)).wt (eD _ R)) =
      Hop (twWt p (delta ℤ_[p] μ)) (deltaMap p μ (eD _ R)) := by
  rw [H_eD, map_smul, deltaMap_eD, map_smul, H_xD, smul_comm]

/-! ### The morphisms -/

/-- (D1) `δ` is a morphism of DP-lattices `Δ_A(λ) → Φ_p(Δ_A(μ))`. -/
def deltaHom (μ : ℕ) : Hom (delta ℤ_[p] (lam p μ)) (twist p (delta ℤ_[p] μ)) :=
  homOfOne (deltaMap p μ) (ext_single fun R => deltaMap_F p μ R)
    (ext_single fun R => deltaMap_E p μ R) (ext_single fun R => deltaMap_H p μ R)

/-- (D1) the isomorphism `Δ_A(λ) ≅ Φ_p(Δ_A(μ))` given by `δ` and its inverse. -/
def deltaIso (μ : ℕ) : Iso (delta ℤ_[p] (lam p μ)) (twist p (delta ℤ_[p] μ)) :=
  Iso.ofInverse (deltaHom p μ) (deltaInv p μ) (deltaInv_deltaMap p μ) (deltaMap_deltaInv p μ)

/-- (D1) `δ : Δ_A(pμ+p−1) → Φ_p(Δ_A(μ))`, `e'_R ↦ c_R x_R`, with `c_0 = 1`,
`c_{R+1} = c_R / (R+1)` if `R mod p ≤ p − 2` (then `R + 1` is a unit of `ℤ_[p]`; the division is
stated as `(R+1) · c_{R+1} = c_R`), `c_{R+1} = −c_R` if `R mod p = p − 1`, every `c_R` a unit;
`δ` is a morphism of DP-lattices, it is bijective, its inverse `x_R ↦ c_R^{-1} e'_R` is a
morphism, and the composites are the identities. -/
theorem D1 (μ : ℕ) :
    (∀ R : Fin (p * μ + p - 1 + 1), deltaMap p μ (eD (p * μ + p - 1) R) = cD p (R : ℕ) • xD p μ R) ∧
    cD p 0 = 1 ∧
    (∀ R : ℕ, R % p ≤ p - 2 →
      IsUnit (((R + 1 : ℕ)) : ℤ_[p]) ∧ (((R + 1 : ℕ)) : ℤ_[p]) * cD p (R + 1) = cD p R) ∧
    (∀ R : ℕ, R % p = p - 1 → cD p (R + 1) = -cD p R) ∧
    (∀ R : ℕ, IsUnit (cD p R)) ∧
    (∀ R : Fin (p * μ + p - 1 + 1), deltaInv p μ (xD p μ R) = cDinv p (R : ℕ) • eD (p * μ + p - 1) R) ∧
    ∃ (f : Hom (delta ℤ_[p] (p * μ + p - 1)) (twist p (delta ℤ_[p] μ)))
      (g : Hom (twist p (delta ℤ_[p] μ)) (delta ℤ_[p] (p * μ + p - 1))),
      f.toLin = deltaMap p μ ∧ g.toLin = deltaInv p μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  have hp := two_le_p p
  refine ⟨deltaMap_eD p μ, cD_zero p, fun R hR => ⟨isUnit_succ p (by omega),
    succ_mul_cD_succ p (by omega)⟩, fun R hR => cD_succ_wrap p hR, isUnit_cD p, deltaInv_xD p μ,
    (deltaIso p μ).hom, (deltaIso p μ).inv, rfl, rfl, ?_, (deltaIso p μ).hom_inv,
    (deltaIso p μ).inv_hom⟩
  refine ⟨fun x y h => ?_, fun y => ⟨deltaInv p μ y, ?_⟩⟩
  · change deltaMap p μ x = deltaMap p μ y at h
    have := congrArg (deltaInv p μ) h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, deltaInv_deltaMap] at this
  · exact LinearMap.congr_fun (deltaMap_deltaInv p μ) y

/-- (D1) `Φ_p(Δ_A(μ)) ≅ Δ_A(pμ + p − 1)` (C20's `Iso`: morphisms both ways whose composites are
the identities). -/
theorem D1_iso (μ : ℕ) :
    Nonempty (Iso (twist p (delta ℤ_[p] μ)) (delta ℤ_[p] (p * μ + p - 1))) :=
  ⟨⟨(deltaIso p μ).inv, (deltaIso p μ).hom, (deltaIso p μ).inv_hom, (deltaIso p μ).hom_inv⟩⟩

end ColouredSand.OddTwist
