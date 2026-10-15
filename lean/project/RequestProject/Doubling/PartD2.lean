module

public import RequestProject.Doubling.PartD1

/-!
# `C20_the_doubling_functor.md`: Part D, (D2) — `Φ(∇_A(μ)) ≅ ∇_A(2μ+1)`

`nablaMap μ : ∇_A(2μ+1) → Φ(∇_A(μ))` is `ν_μ`, `w'_R ↦ d_R x_R`, and `nablaInv μ` is its inverse
`x_R ↦ d_R^{-1} w'_R`. `d_R = dN μ R` is given in closed form (a product of inverses of the odd
integers `2μ+1−2k`) and satisfies the recursion of the file (`dN_rec`). The commutation with
`F^{(1)}`, `E^{(1)}`, `H` is checked directly on basis vectors; no complete reducibility is used.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset WeylFilt

variable {A : Type*} [CommRing A]

/-- (D2) `d_R = ∏_{0 ≤ k < ⌊(R+1)/2⌋} ⅟(2μ+1−2k)`. -/
def dN (μ R : ℕ) : A := ∏ k ∈ range ((R + 1) / 2), Ring.inverse (((2 * μ + 1 - 2 * k : ℕ)) : A)

/-- (D2) `d_R^{-1} = ∏_{0 ≤ k < ⌊(R+1)/2⌋} (2μ+1−2k)`. -/
def dNinv (μ R : ℕ) : A := ∏ k ∈ range ((R + 1) / 2), (((2 * μ + 1 - 2 * k : ℕ)) : A)

/-- (D2) the recursion of the file: `d_0 = 1`, `d_{2s+1} = d_{2s} · ⅟(2μ+1−2s)`,
`d_{2s+2} = d_{2s+1}`. -/
theorem dN_rec (μ : ℕ) :
    dN (A := A) μ 0 = 1 ∧
    (∀ s : ℕ, dN (A := A) μ (2 * s + 1) =
      dN μ (2 * s) * Ring.inverse (((2 * μ + 1 - 2 * s : ℕ)) : A)) ∧
    (∀ s : ℕ, dN (A := A) μ (2 * s + 2) = dN μ (2 * s + 1)) := by
  refine ⟨by simp [dN], fun s => ?_, fun s => ?_⟩
  · rw [dN, dN, show (2 * s + 1 + 1) / 2 = s + 1 by omega, show (2 * s + 1) / 2 = s by omega,
      prod_range_succ]
  · rw [dN, dN, show (2 * s + 2 + 1) / 2 = s + 1 by omega, show (2 * s + 1 + 1) / 2 = s + 1 by omega]

lemma dN_odd (μ s : ℕ) : dN (A := A) μ (2 * s + 1) =
    dN μ (2 * s) * Ring.inverse (((2 * μ + 1 - 2 * s : ℕ)) : A) := (dN_rec μ).2.1 s

lemma dN_even_succ (μ s : ℕ) : dN (A := A) μ (2 * s + 2) = dN μ (2 * s + 1) := (dN_rec μ).2.2 s

lemma isUnit_oddN [OddUnits A] (μ k : ℕ) (hk : k ≤ μ) :
    IsUnit (((2 * μ + 1 - 2 * k : ℕ)) : A) := by
  have := OddUnits.hodd (A := A) (μ - k)
  rwa [show 2 * (μ - k) + 1 = 2 * μ + 1 - 2 * k by omega] at this

lemma oddN_mul_inv [OddUnits A] (μ k : ℕ) (hk : k ≤ μ) :
    (((2 * μ + 1 - 2 * k : ℕ)) : A) * Ring.inverse (((2 * μ + 1 - 2 * k : ℕ)) : A) = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_oddN μ k hk)

lemma dNinv_mul_dN [OddUnits A] (μ R : ℕ) (hR : R < 2 * μ + 1 + 1) :
    dNinv (A := A) μ R * dN μ R = 1 := by
  rw [dNinv, dN, ← prod_mul_distrib]
  refine prod_eq_one fun k hk => ?_
  simp only [mem_range] at hk
  exact oddN_mul_inv μ k (by omega)

/-- (D2) `ν_μ : ∇_A(2μ+1) → Φ(∇_A(μ))`, `w'_R ↦ d_R x_R` (defined on basis vectors). -/
def nablaMap (μ : ℕ) : ((nabla A (2 * μ + 1)).ι → A) →ₗ[A] (Fin 2 × (nabla A μ).ι → A) :=
  (Pi.basisFun A (Fin (2 * μ + 1 + 1))).constr A (fun R => dN (A := A) μ (R : ℕ) • xN μ R)

/-- (D2) the inverse map `x_R ↦ d_R^{-1} w'_R` (defined on basis vectors). -/
def nablaInv (μ : ℕ) : (Fin 2 × (nabla A μ).ι → A) →ₗ[A] ((nabla A (2 * μ + 1)).ι → A) :=
  (Pi.basisFun A (Fin 2 × Fin (μ + 1))).constr A
    (fun p => dNinv (A := A) μ (xIdx μ p : ℕ) • eN (2 * μ + 1) (xIdx μ p))

lemma nablaMap_eN (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    nablaMap (A := A) μ (eN (2 * μ + 1) R) = dN (A := A) μ (R : ℕ) • xN μ R := by
  show (Pi.basisFun A (Fin (2 * μ + 1 + 1))).constr A _ (Pi.single R 1) = _
  rw [← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma nablaInv_single (μ : ℕ) (p : Fin 2 × Fin (μ + 1)) :
    nablaInv (A := A) μ (Pi.single (p : Fin 2 × (nabla A μ).ι) 1) =
      dNinv (A := A) μ (xIdx μ p : ℕ) • eN (2 * μ + 1) (xIdx μ p) := by
  show (Pi.basisFun A (Fin 2 × Fin (μ + 1))).constr A _ (Pi.single p 1) = _
  rw [← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma nablaInv_xN (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    nablaInv (A := A) μ (xN μ R) = dNinv (A := A) μ (R : ℕ) • eN (2 * μ + 1) R := by
  rw [xN_eq_single, nablaInv_single, xIdx_parR]

lemma nablaInv_nablaMap [OddUnits A] (μ : ℕ) :
    nablaInv (A := A) μ ∘ₗ nablaMap μ = LinearMap.id := by
  refine ext_single fun R => ?_
  show nablaInv μ (nablaMap μ (eN (2 * μ + 1) R)) = eN (2 * μ + 1) R
  rw [nablaMap_eN, map_smul, nablaInv_xN, smul_smul, mul_comm (dN _ _),
    dNinv_mul_dN μ _ (R : Fin (2 * μ + 1 + 1)).isLt, one_smul]

lemma nablaMap_nablaInv [OddUnits A] (μ : ℕ) :
    nablaMap (A := A) μ ∘ₗ nablaInv μ = LinearMap.id := by
  refine ext_single fun p => ?_
  show nablaMap μ (nablaInv μ (Pi.single (p : Fin 2 × (nabla A μ).ι) 1)) = _
  rw [nablaInv_single, map_smul, nablaMap_eN, smul_smul, dNinv_mul_dN μ _ (xIdx μ p).isLt,
    one_smul, xN_xIdx]
  rfl

/-! ### Commutation with `F^{(1)}`, `E^{(1)}`, `H` -/

lemma nablaMap_F [OddUnits A] (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    nablaMap μ ((nabla A (2 * μ + 1)).Fd 1 (eN _ R)) =
      phiFd (nabla A μ) 1 (nablaMap μ (eN _ R)) := by
  rw [nablaMap_eN, map_smul]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [eN_F_lt _ R ⟨2 * k + 1, by omega⟩ (by simp [hk]), map_smul, nablaMap_eN,
      xN_odd μ _ ⟨k, hs⟩ rfl, xN_even μ R ⟨k, hs⟩ hk, F1_b0, smul_smul]
    congr 1
    simp only [hk]
    rw [dN_odd, ← mul_assoc, mul_comm _ (dN μ (2 * k)), mul_assoc, oddN_mul_inv μ k (by omega),
      mul_one]
  · have hs : k < μ + 1 := by omega
    rw [xN_odd μ R ⟨k, hs⟩ hk, F1_b1]
    by_cases hkμ : k = μ
    · rw [eN_F_last _ R (by omega), map_zero, eN_F_last μ ⟨k, hs⟩ hkμ, map_zero, smul_zero,
        smul_zero]
    · have hs1 : k + 1 < μ + 1 := by omega
      rw [eN_F_lt _ R ⟨2 * k + 2, by omega⟩ (by simp [hk]), map_smul, nablaMap_eN,
        xN_even μ _ ⟨k + 1, hs1⟩ (by simp; ring), eN_F_lt μ ⟨k, hs⟩ ⟨k + 1, hs1⟩ rfl, map_smul,
        smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [hk]
      rw [dN_even_succ]
      have e1 : 2 * μ + 1 - (2 * k + 1) = 2 * (μ - k) := by omega
      rw [e1]; push_cast; ring

lemma nablaMap_E [OddUnits A] (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    nablaMap μ ((nabla A (2 * μ + 1)).Ed 1 (eN _ R)) =
      phiEd (nabla A μ) 1 (nablaMap μ (eN _ R)) := by
  rw [nablaMap_eN, map_smul]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [xN_even μ R ⟨k, hs⟩ hk, E1_b0]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [eN_E_zero _ R (by omega), map_zero, eN_E_zero μ ⟨0, hs⟩ rfl, map_zero, smul_zero,
        smul_zero]
    · have hs1 : k - 1 < μ + 1 := by omega
      rw [eN_E_pos _ R ⟨2 * k - 1, by omega⟩ (by simp; omega), map_smul, nablaMap_eN,
        xN_odd μ _ ⟨k - 1, hs1⟩ (by simp; omega), eN_E_pos μ ⟨k, hs⟩ ⟨k - 1, hs1⟩ (by simp; omega),
        map_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [hk]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring,
        dN_even_succ]
      push_cast; ring
  · have hs : k < μ + 1 := by omega
    rw [eN_E_pos _ R ⟨2 * k, by omega⟩ (by simp [hk]), map_smul, nablaMap_eN,
      xN_even μ _ ⟨k, hs⟩ rfl, xN_odd μ R ⟨k, hs⟩ hk, E1_b1' _ (wt_eN μ _), eN_FE]
    simp only [map_add, map_smul, smul_smul, smul_add]
    rw [← add_smul]
    congr 1
    simp only [hk]
    rw [dN_odd]
    obtain ⟨m, rfl⟩ : ∃ m, μ = k + m := ⟨μ - k, by omega⟩
    have e1 : 2 * (k + m) + 1 - 2 * k = 2 * m + 1 := by omega
    have hu := oddN_mul_inv (A := A) (k + m) k (by omega)
    simp only [e1, Nat.add_sub_cancel_left] at hu ⊢
    push_cast at hu ⊢
    linear_combination (-(2 * (k : A) + 1) * dN (k + m) (2 * k)) * hu

lemma nablaMap_H (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    nablaMap μ (Hop (nabla A (2 * μ + 1)).wt (eN _ R)) =
      Hop (phiWt (nabla A μ)) (nablaMap μ (eN _ R)) := by
  rw [H_eN, map_smul, nablaMap_eN, map_smul, H_xN, smul_comm]

/-! ### The morphisms -/

section hom

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (D2) `ν_μ` is a morphism of DP-lattices `∇_A(2μ+1) → Φ(∇_A(μ))`. -/
def nablaHom (μ : ℕ) : Hom (nabla A (2 * μ + 1)) (phi (nabla A μ)) :=
  homOfOne (nablaMap μ) (ext_single fun R => nablaMap_F μ R) (ext_single fun R => nablaMap_E μ R)
    (ext_single fun R => nablaMap_H μ R)

/-- (D2) the isomorphism `∇_A(2μ+1) ≅ Φ(∇_A(μ))` given by `ν_μ` and its inverse. -/
def nablaIso (μ : ℕ) : Iso (nabla A (2 * μ + 1)) (phi (nabla A μ)) :=
  Iso.ofInverse (nablaHom μ) (nablaInv μ) (nablaInv_nablaMap μ) (nablaMap_nablaInv μ)

/-- (D2) `ν_μ : ∇_A(2μ+1) → Φ(∇_A(μ))`, `w'_R ↦ d_R x_R` (`d_0 = 1`,
`d_{2s+1} = d_{2s} · ⅟(2μ+1−2s)`, `d_{2s+2} = d_{2s+1}`), is a morphism of DP-lattices, it is
bijective, its inverse `x_R ↦ d_R^{-1} w'_R` is a morphism, and the composites are the
identities; hence `Φ(∇_A(μ)) ≅ ∇_A(2μ+1)`. -/
theorem D2 (μ : ℕ) :
    (∀ R : Fin (2 * μ + 1 + 1), nablaMap (A := A) μ (eN (2 * μ + 1) R) = dN (A := A) μ (R : ℕ) • xN μ R) ∧
    (∀ R : Fin (2 * μ + 1 + 1),
      nablaInv (A := A) μ (xN μ R) = dNinv (A := A) μ (R : ℕ) • eN (2 * μ + 1) R) ∧
    (∀ R : ℕ, R < 2 * μ + 1 + 1 → dNinv (A := A) μ R * dN μ R = 1) ∧
    ∃ (f : Hom (nabla A (2 * μ + 1)) (phi (nabla A μ)))
      (g : Hom (phi (nabla A μ)) (nabla A (2 * μ + 1))),
      f.toLin = nablaMap μ ∧ g.toLin = nablaInv μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  refine ⟨nablaMap_eN μ, nablaInv_xN μ, dNinv_mul_dN μ, (nablaIso μ).hom, (nablaIso μ).inv, rfl,
    rfl, ?_, (nablaIso μ).hom_inv, (nablaIso μ).inv_hom⟩
  refine ⟨fun x y h => ?_, fun y => ⟨nablaInv μ y, ?_⟩⟩
  · change nablaMap μ x = nablaMap μ y at h
    have := congrArg (nablaInv μ) h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, nablaInv_nablaMap] at this
  · exact LinearMap.congr_fun (nablaMap_nablaInv μ) y

/-- (D2) `Φ(∇_A(μ)) ≅ ∇_A(2μ+1)`: morphisms both ways whose composites are the identities. -/
theorem D2_iso (μ : ℕ) : Nonempty (Iso (phi (nabla A μ)) (nabla A (2 * μ + 1))) :=
  ⟨⟨(nablaIso μ).inv, (nablaIso μ).hom, (nablaIso μ).inv_hom, (nablaIso μ).hom_inv⟩⟩

end hom

end Doubling
