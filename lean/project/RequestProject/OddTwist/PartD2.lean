module

public import RequestProject.OddTwist.PartD1

/-!
# `CSI1_the_odd_twist.md`: Part D, (D2) — `Φ_p(∇_A(μ)) ≅ ∇_A(pμ + p − 1)`

`nablaMap p μ : ∇_A(λ) → Φ_p(∇_A(μ))` (`λ = pμ + p − 1`) is `ν`, `w'_R ↦ d_R x_R`, and
`nablaInv p μ` is its inverse `x_R ↦ d_R^{-1} w'_R`; both are defined on basis vectors
(`Basis.constr`). The commutation with `F^{(1)}`, `E^{(1)}`, `H` is checked directly on the basis
vectors, and C20's `homOfOne` gives a morphism.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Doubling WeylFilt

open scoped Nat

variable (p : ℕ) [Fact p.Prime]

/-- (D2) `ν : ∇_A(λ) → Φ_p(∇_A(μ))`, `w'_R ↦ d_R x_R` (defined on basis vectors). -/
def nablaMap (μ : ℕ) :
    ((nabla ℤ_[p] (lam p μ)).ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × (nabla ℤ_[p] μ).ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin (lam p μ + 1))).constr ℤ_[p] (fun R => dN p μ (R : ℕ) • xN p μ R)

/-- (D2) the inverse map `x_R ↦ d_R^{-1} w'_R` (defined on basis vectors). -/
def nablaInv (μ : ℕ) :
    (Fin p × (nabla ℤ_[p] μ).ι → ℤ_[p]) →ₗ[ℤ_[p]] ((nabla ℤ_[p] (lam p μ)).ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin p × Fin (μ + 1))).constr ℤ_[p]
    (fun x => dNinv p μ (xIdx p μ x : ℕ) • eN (lam p μ) (xIdx p μ x))

lemma nablaMap_eN (μ : ℕ) (R : Fin (lam p μ + 1)) :
    nablaMap p μ (eN (lam p μ) R) = dN p μ (R : ℕ) • xN p μ R := by
  show (Pi.basisFun ℤ_[p] (Fin (lam p μ + 1))).constr ℤ_[p] _ (Pi.single R 1) = _
  rw [← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma nablaInv_single (μ : ℕ) (x : Fin p × Fin (μ + 1)) :
    nablaInv p μ (Pi.single (x : Fin p × (nabla ℤ_[p] μ).ι) 1) =
      dNinv p μ (xIdx p μ x : ℕ) • eN (lam p μ) (xIdx p μ x) := by
  show (Pi.basisFun ℤ_[p] (Fin p × Fin (μ + 1))).constr ℤ_[p] _ (Pi.single x 1) = _
  rw [← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma nablaInv_xN (μ : ℕ) (R : Fin (lam p μ + 1)) :
    nablaInv p μ (xN p μ R) = dNinv p μ (R : ℕ) • eN (lam p μ) R := by
  rw [xN_eq_single, nablaInv_single, xIdx_div_mod]

lemma nablaInv_nablaMap (μ : ℕ) : nablaInv p μ ∘ₗ nablaMap p μ = LinearMap.id := by
  refine ext_single fun R => ?_
  show nablaInv p μ (nablaMap p μ (eN (lam p μ) R)) = eN (lam p μ) R
  rw [nablaMap_eN, map_smul, nablaInv_xN, smul_smul, mul_comm (dN p μ _),
    dNinv_mul_dN p μ _ (Nat.lt_succ_iff.mp R.isLt), one_smul]

lemma nablaMap_nablaInv (μ : ℕ) : nablaMap p μ ∘ₗ nablaInv p μ = LinearMap.id := by
  refine ext_single fun x => ?_
  show nablaMap p μ (nablaInv p μ (Pi.single (x : Fin p × (nabla ℤ_[p] μ).ι) 1)) = _
  rw [nablaInv_single, map_smul, nablaMap_eN, smul_smul,
    dNinv_mul_dN p μ _ (Nat.lt_succ_iff.mp (xIdx p μ x).isLt), one_smul, xN_xIdx]
  rfl

/-! ### Commutation with `F^{(1)}`, `E^{(1)}`, `H` -/

lemma nablaMap_F (μ : ℕ) (R : Fin (lam p μ + 1)) :
    nablaMap p μ ((nabla ℤ_[p] (lam p μ)).Fd 1 (eN _ R)) =
      twFd p (nabla ℤ_[p] μ) 1 (nablaMap p μ (eN _ R)) := by
  have hp := one_le_p p
  rw [nablaMap_eN, map_smul]
  set s := (R : ℕ) / p
  set j := (R : ℕ) % p
  have hRs : (R : ℕ) = p * s + j := (Nat.div_add_mod _ _).symm
  have hj : j < p := Nat.mod_lt _ (by omega)
  have hs : s < μ + 1 := div_lt_of_fin p μ R
  have hsμ : p * s ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
  have hRl : (R : ℕ) ≤ lam p μ := Nat.lt_succ_iff.mp R.isLt
  obtain ⟨t, ht⟩ : ∃ t, μ = s + t := ⟨μ - s, by omega⟩
  have hlam : lam p μ = p * s + p * t + p - 1 := by simp only [lam]; rw [ht, Nat.mul_add]
  rw [xN_eq p μ R ⟨s, hs⟩ j hRs hj]
  by_cases hj1 : j + 1 < p
  · have hR1 : (R : ℕ) + 1 < lam p μ + 1 := by
      show (R : ℕ) + 1 < p * μ + p - 1 + 1; omega
    rw [eN_F_lt _ R ⟨(R : ℕ) + 1, hR1⟩ rfl, map_smul, nablaMap_eN,
      xN_eq p μ ⟨(R : ℕ) + 1, hR1⟩ ⟨s, hs⟩ (j + 1) (by simp only; omega) hj1, F1_lt p _ hj1,
      smul_smul]
    congr 1
    exact lam_sub_mul_dN_succ p μ hRl (by omega)
  · have hjp : j = p - 1 := by omega
    have hmod : (R : ℕ) % p = p - 1 := hjp
    rw [hjp, F1_last]
    by_cases hsμ' : s = μ
    · have hRlam : (R : ℕ) = lam p μ := by
        show (R : ℕ) = p * μ + p - 1; rw [hRs, ← hsμ']; omega
      rw [eN_F_last _ R hRlam, eN_F_last μ ⟨s, hs⟩ hsμ']
      simp
    · have hs1 : s + 1 < μ + 1 := by omega
      have hR1 : (R : ℕ) + 1 < lam p μ + 1 := by
        show (R : ℕ) + 1 < p * μ + p - 1 + 1
        have : p * (s + 1) ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add_one] at this; omega
      rw [eN_F_lt _ R ⟨(R : ℕ) + 1, hR1⟩ rfl, map_smul, nablaMap_eN,
        xN_eq p μ ⟨(R : ℕ) + 1, hR1⟩ ⟨s + 1, hs1⟩ 0 (by simp only; rw [Nat.mul_add_one]; omega)
          (by omega),
        eN_F_lt μ ⟨s, hs⟩ ⟨s + 1, hs1⟩ rfl]
      simp only [map_smul, smul_smul]
      rw [dN_succ_wrap p μ hmod]
      congr 1
      have e1 : lam p μ - (R : ℕ) = p * t := by omega
      have e2 : μ - s = t := by omega
      simp only [e1, e2]
      push_cast; ring

lemma nablaMap_E (μ : ℕ) (R : Fin (lam p μ + 1)) :
    nablaMap p μ ((nabla ℤ_[p] (lam p μ)).Ed 1 (eN _ R)) =
      twEd p (nabla ℤ_[p] μ) 1 (nablaMap p μ (eN _ R)) := by
  have hp := one_le_p p
  rw [nablaMap_eN, map_smul]
  set s := (R : ℕ) / p
  set j := (R : ℕ) % p
  have hRs : (R : ℕ) = p * s + j := (Nat.div_add_mod _ _).symm
  have hj : j < p := Nat.mod_lt _ (by omega)
  have hs : s < μ + 1 := div_lt_of_fin p μ R
  have hsμ : p * s ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
  have hRl : (R : ℕ) ≤ lam p μ := Nat.lt_succ_iff.mp R.isLt
  obtain ⟨t, ht⟩ : ∃ t, μ = s + t := ⟨μ - s, by omega⟩
  have hlam : lam p μ = p * s + p * t + p - 1 := by simp only [lam]; rw [ht, Nat.mul_add]
  rw [xN_eq p μ R ⟨s, hs⟩ j hRs hj]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, E1_zero]
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rw [eN_E_zero _ R (by rw [hRs, hs0, hj0]; simp), eN_E_zero μ ⟨s, hs⟩ hs0]
      simp
    · have hR1 : (R : ℕ) - 1 < lam p μ + 1 := by omega
      have hs1 : s - 1 < μ + 1 := by omega
      have hps : p ≤ p * s := Nat.le_mul_of_pos_right p hs0
      have hRe : (R : ℕ) - 1 = p * (s - 1) + (p - 1) := by rw [Nat.mul_sub_one]; omega
      have hmod : ((R : ℕ) - 1) % p = p - 1 := (div_mod_unique hRe (by omega)).2
      have hc : dN p μ (R : ℕ) = -dN p μ ((R : ℕ) - 1) := by
        have := dN_succ_wrap p μ hmod
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [eN_E_pos _ R ⟨(R : ℕ) - 1, hR1⟩ (by simp only; omega), map_smul, nablaMap_eN,
        xN_eq p μ ⟨(R : ℕ) - 1, hR1⟩ ⟨s - 1, hs1⟩ (p - 1) hRe (by omega),
        eN_E_pos μ ⟨s, hs⟩ ⟨s - 1, hs1⟩ (by simp only; omega)]
      simp only [map_smul, smul_smul]
      rw [hc]
      congr 1
      have hRc : (((R : ℕ) : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * s := by
        rw [hRs, hj0]; push_cast; ring
      rw [hRc]
      ring
  · have hR1 : (R : ℕ) - 1 < lam p μ + 1 := by omega
    have hRe : (R : ℕ) - 1 = p * s + (j - 1) := by omega
    have hmod : ((R : ℕ) - 1) % p ≠ p - 1 := by
      rw [(div_mod_unique hRe (by omega)).2]; omega
    have hc := lam_sub_mul_dN_succ p μ (R := (R : ℕ) - 1) (by omega) hmod
    rw [Nat.sub_add_cancel (n := (R : ℕ)) (m := 1) (by omega)] at hc
    rw [E1_pos p _ hj0 hj (wt_eN μ ⟨s, hs⟩), eN_FE,
      eN_E_pos _ R ⟨(R : ℕ) - 1, hR1⟩ (by simp only; omega),
      map_smul, nablaMap_eN, xN_eq p μ ⟨(R : ℕ) - 1, hR1⟩ ⟨s, hs⟩ (j - 1) hRe (by omega), ← hc]
    simp only [map_smul, smul_smul, ← add_smul]
    congr 1
    have e1 : lam p μ - ((R : ℕ) - 1) + j = p * t + p := by omega
    have e1' : ((lam p μ - ((R : ℕ) - 1) : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * t + p - j := by
      have : ((lam p μ - ((R : ℕ) - 1) : ℕ) : ℤ_[p]) + j = (p : ℤ_[p]) * t + p := by
        exact_mod_cast e1
      linear_combination this
    have hRc : (((R : ℕ) : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * s + j := by rw [hRs]; push_cast; ring
    rw [e1', hRc]
    simp only [ht, Nat.add_sub_cancel_left]
    push_cast; ring

lemma nablaMap_H (μ : ℕ) (R : Fin (lam p μ + 1)) :
    nablaMap p μ (Hop (nabla ℤ_[p] (lam p μ)).wt (eN _ R)) =
      Hop (twWt p (nabla ℤ_[p] μ)) (nablaMap p μ (eN _ R)) := by
  rw [H_eN, map_smul, nablaMap_eN, map_smul, H_xN, smul_comm]

/-! ### The morphisms -/

/-- (D2) `ν` is a morphism of DP-lattices `∇_A(λ) → Φ_p(∇_A(μ))`. -/
def nablaHom (μ : ℕ) : Hom (nabla ℤ_[p] (lam p μ)) (twist p (nabla ℤ_[p] μ)) :=
  homOfOne (nablaMap p μ) (ext_single fun R => nablaMap_F p μ R)
    (ext_single fun R => nablaMap_E p μ R) (ext_single fun R => nablaMap_H p μ R)

/-- (D2) the isomorphism `∇_A(λ) ≅ Φ_p(∇_A(μ))` given by `ν` and its inverse. -/
def nablaIso (μ : ℕ) : Iso (nabla ℤ_[p] (lam p μ)) (twist p (nabla ℤ_[p] μ)) :=
  Iso.ofInverse (nablaHom p μ) (nablaInv p μ) (nablaInv_nablaMap p μ) (nablaMap_nablaInv p μ)

/-- (D2) `ν : ∇_A(pμ+p−1) → Φ_p(∇_A(μ))`, `w'_R ↦ d_R x_R`, with `d_0 = 1`,
`d_{R+1} = d_R / (λ − R)` if `R mod p ≤ p − 2` (then `λ − R` is a unit of `ℤ_[p]`; the division
is stated as `(λ − R) · d_{R+1} = d_R`), `d_{R+1} = −d_R` if `R mod p = p − 1`, every `d_R`
(`R ≤ λ`) a unit; `ν` is a morphism of DP-lattices, it is bijective, its inverse
`x_R ↦ d_R^{-1} w'_R` is a morphism, and the composites are the identities. -/
theorem D2 (μ : ℕ) :
    (∀ R : Fin (p * μ + p - 1 + 1),
      nablaMap p μ (eN (p * μ + p - 1) R) = dN p μ (R : ℕ) • xN p μ R) ∧
    dN p μ 0 = 1 ∧
    (∀ R : ℕ, R ≤ p * μ + p - 1 → R % p ≤ p - 2 →
      IsUnit (((p * μ + p - 1 - R : ℕ)) : ℤ_[p]) ∧
      (((p * μ + p - 1 - R : ℕ)) : ℤ_[p]) * dN p μ (R + 1) = dN p μ R) ∧
    (∀ R : ℕ, R % p = p - 1 → dN p μ (R + 1) = -dN p μ R) ∧
    (∀ R : ℕ, R ≤ p * μ + p - 1 → IsUnit (dN p μ R)) ∧
    (∀ R : Fin (p * μ + p - 1 + 1),
      nablaInv p μ (xN p μ R) = dNinv p μ (R : ℕ) • eN (p * μ + p - 1) R) ∧
    ∃ (f : Hom (nabla ℤ_[p] (p * μ + p - 1)) (twist p (nabla ℤ_[p] μ)))
      (g : Hom (twist p (nabla ℤ_[p] μ)) (nabla ℤ_[p] (p * μ + p - 1))),
      f.toLin = nablaMap p μ ∧ g.toLin = nablaInv p μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  have hp := two_le_p p
  refine ⟨nablaMap_eN p μ, dN_zero p μ, fun R hRl hR => ⟨isUnit_lam_sub p hRl (by omega),
    lam_sub_mul_dN_succ p μ hRl (by omega)⟩, fun R hR => dN_succ_wrap p μ hR,
    fun R hR => isUnit_dN p μ R hR, nablaInv_xN p μ,
    (nablaIso p μ).hom, (nablaIso p μ).inv, rfl, rfl, ?_, (nablaIso p μ).hom_inv,
    (nablaIso p μ).inv_hom⟩
  refine ⟨fun x y h => ?_, fun y => ⟨nablaInv p μ y, ?_⟩⟩
  · change nablaMap p μ x = nablaMap p μ y at h
    have := congrArg (nablaInv p μ) h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, nablaInv_nablaMap] at this
  · exact LinearMap.congr_fun (nablaMap_nablaInv p μ) y

/-- (D2) `Φ_p(∇_A(μ)) ≅ ∇_A(pμ + p − 1)` (C20's `Iso`). -/
theorem D2_iso (μ : ℕ) :
    Nonempty (Iso (twist p (nabla ℤ_[p] μ)) (nabla ℤ_[p] (p * μ + p - 1))) :=
  ⟨⟨(nablaIso p μ).inv, (nablaIso p μ).hom, (nablaIso p μ).inv_hom, (nablaIso p μ).hom_inv⟩⟩

end ColouredSand.OddTwist
