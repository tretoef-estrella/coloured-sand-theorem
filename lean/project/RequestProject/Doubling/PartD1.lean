module

public import RequestProject.Doubling.PartD

/-!
# `C20_the_doubling_functor.md`: Part D, (D1) — `Φ(Δ_A(μ)) ≅ Δ_A(2μ+1)`

`deltaMap μ : Δ_A(2μ+1) → Φ(Δ_A(μ))` is `δ_μ`, `e'_R ↦ c_R x_R`, and `deltaInv μ` is its inverse
`x_R ↦ c_R^{-1} e'_R`. The commutation with `F^{(1)}`, `E^{(1)}`, `H` is checked directly on the
basis vectors (`deltaMap_F`, `deltaMap_E`, `deltaMap_H`); no complete reducibility is used.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset WeylFilt

open scoped Nat

variable {A : Type*} [CommRing A]

/-- (D1) `c_R`: `c_{2s} = ⅟(2s−1)!!`, `c_{2s+1} = ⅟(2s+1)!!`. -/
def cD (R : ℕ) : A := if R % 2 = 0 then dfi (R / 2) else dfi (R / 2 + 1)

lemma cD_even (R k : ℕ) (h : R = 2 * k) : cD (A := A) R = dfi k := by
  rw [cD, if_pos (by omega), show R / 2 = k by omega]

lemma cD_odd (R k : ℕ) (h : R = 2 * k + 1) : cD (A := A) R = dfi (k + 1) := by
  rw [cD, if_neg (by omega), show R / 2 = k by omega]

/-- (D1) `c_R^{-1}`: `(2s−1)!!` for `R = 2s`, `(2s+1)!!` for `R = 2s+1`. -/
def cDinv (R : ℕ) : A :=
  if R % 2 = 0 then (((2 * (R / 2) - 1)‼ : ℕ) : A) else (((2 * (R / 2) + 1)‼ : ℕ) : A)

lemma cDinv_mul_cD [OddUnits A] (R : ℕ) : cDinv (A := A) R * cD R = 1 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' R
  · rw [cD_even _ k rfl, cDinv, if_pos (by omega), show 2 * k / 2 = k by omega, mul_dfi]
  · rw [cD_odd _ k rfl, cDinv, if_neg (by omega), show (2 * k + 1) / 2 = k by omega,
      show 2 * k + 1 = 2 * (k + 1) - 1 by omega, mul_dfi]

/-- (D1) `δ_μ : Δ_A(2μ+1) → Φ(Δ_A(μ))`, `e'_R ↦ c_R x_R` (defined on basis vectors). -/
def deltaMap (μ : ℕ) : ((delta A (2 * μ + 1)).ι → A) →ₗ[A] (Fin 2 × (delta A μ).ι → A) :=
  (Pi.basisFun A (Fin (2 * μ + 1 + 1))).constr A (fun R => cD (A := A) (R : ℕ) • xD μ R)

/-- (D1) the inverse map `x_R ↦ c_R^{-1} e'_R` (defined on basis vectors). -/
def deltaInv (μ : ℕ) : (Fin 2 × (delta A μ).ι → A) →ₗ[A] ((delta A (2 * μ + 1)).ι → A) :=
  (Pi.basisFun A (Fin 2 × Fin (μ + 1))).constr A
    (fun p => cDinv (A := A) (xIdx μ p : ℕ) • eD (2 * μ + 1) (xIdx μ p))

lemma deltaMap_eD (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    deltaMap (A := A) μ (eD (2 * μ + 1) R) = cD (A := A) (R : ℕ) • xD μ R := by
  show (Pi.basisFun A (Fin (2 * μ + 1 + 1))).constr A _ (Pi.single R 1) = _
  rw [← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma deltaInv_single (μ : ℕ) (p : Fin 2 × Fin (μ + 1)) :
    deltaInv (A := A) μ (Pi.single (p : Fin 2 × (delta A μ).ι) 1) =
      cDinv (A := A) (xIdx μ p : ℕ) • eD (2 * μ + 1) (xIdx μ p) := by
  show (Pi.basisFun A (Fin 2 × Fin (μ + 1))).constr A _ (Pi.single p 1) = _
  rw [← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma deltaInv_xD (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    deltaInv (A := A) μ (xD μ R) = cDinv (A := A) (R : ℕ) • eD (2 * μ + 1) R := by
  rw [xD_eq_single, deltaInv_single, xIdx_parR]

lemma deltaInv_deltaMap [OddUnits A] (μ : ℕ) :
    deltaInv (A := A) μ ∘ₗ deltaMap μ = LinearMap.id := by
  refine ext_single fun R => ?_
  show deltaInv μ (deltaMap μ (eD (2 * μ + 1) R)) = eD (2 * μ + 1) R
  rw [deltaMap_eD, map_smul, deltaInv_xD, smul_smul, mul_comm (cD _), cDinv_mul_cD, one_smul]

lemma deltaMap_deltaInv [OddUnits A] (μ : ℕ) :
    deltaMap (A := A) μ ∘ₗ deltaInv μ = LinearMap.id := by
  refine ext_single fun p => ?_
  show deltaMap μ (deltaInv μ (Pi.single (p : Fin 2 × (delta A μ).ι) 1)) = _
  rw [deltaInv_single, map_smul, deltaMap_eD, smul_smul, cDinv_mul_cD, one_smul, xD_xIdx]
  rfl

/-! ### Commutation with `F^{(1)}`, `E^{(1)}`, `H` -/

lemma deltaMap_F [OddUnits A] (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    deltaMap μ ((delta A (2 * μ + 1)).Fd 1 (eD _ R)) =
      phiFd (delta A μ) 1 (deltaMap μ (eD _ R)) := by
  rw [deltaMap_eD, map_smul]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [eD_F_lt _ R ⟨2 * k + 1, by omega⟩ (by simp [hk]), map_smul, deltaMap_eD,
      xD_odd μ _ ⟨k, hs⟩ rfl, xD_even μ R ⟨k, hs⟩ hk, F1_b0, smul_smul, cD_odd _ k rfl,
      cD_even _ k hk]
    congr 1
    rw [hk]
    have := odd_mul_dfi_succ (A := A) k
    push_cast at this ⊢
    linear_combination this
  · have hs : k < μ + 1 := by omega
    rw [xD_odd μ R ⟨k, hs⟩ hk, F1_b1]
    by_cases hkμ : k = μ
    · rw [eD_F_last _ R (by omega), map_zero, eD_F_last μ ⟨k, hs⟩ hkμ, map_zero, smul_zero,
        smul_zero]
    · have hs1 : k + 1 < μ + 1 := by omega
      rw [eD_F_lt _ R ⟨2 * k + 2, by omega⟩ (by simp [hk]), map_smul, deltaMap_eD,
        xD_even μ _ ⟨k + 1, hs1⟩ (by simp; ring), eD_F_lt μ ⟨k, hs⟩ ⟨k + 1, hs1⟩ rfl, map_smul,
        smul_smul, smul_smul, smul_smul, cD_even _ (k + 1) (by simp; ring), cD_odd _ k hk]
      congr 1
      rw [hk]; push_cast; ring

lemma deltaMap_E [OddUnits A] (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    deltaMap μ ((delta A (2 * μ + 1)).Ed 1 (eD _ R)) =
      phiEd (delta A μ) 1 (deltaMap μ (eD _ R)) := by
  rw [deltaMap_eD, map_smul]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [xD_even μ R ⟨k, hs⟩ hk, E1_b0]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [eD_E_zero _ R (by omega), map_zero, eD_E_zero μ ⟨0, hs⟩ rfl, map_zero, smul_zero,
        smul_zero]
    · have hs1 : k - 1 < μ + 1 := by omega
      rw [eD_E_pos _ R ⟨2 * k - 1, by omega⟩ (by simp; omega), map_smul, deltaMap_eD,
        xD_odd μ _ ⟨k - 1, hs1⟩ (by simp; omega), eD_E_pos μ ⟨k, hs⟩ ⟨k - 1, hs1⟩ (by simp; omega),
        map_smul, smul_smul, smul_smul, smul_smul, cD_odd _ (k - 1) (by simp; omega),
        cD_even _ k hk, show k - 1 + 1 = k by omega]
      congr 1
      have e1 : 2 * μ + 1 - (R : ℕ) + 1 = 2 * (μ - k + 1) := by omega
      simp only [e1]
      push_cast; ring
  · have hs : k < μ + 1 := by omega
    rw [eD_E_pos _ R ⟨2 * k, by omega⟩ (by simp [hk]), map_smul, deltaMap_eD,
      xD_even μ _ ⟨k, hs⟩ rfl, xD_odd μ R ⟨k, hs⟩ hk, E1_b1' _ (wt_eD μ _), eD_FE,
      cD_even _ k rfl, cD_odd _ k hk]
    simp only [map_add, map_smul, smul_smul, smul_add]
    rw [← add_smul]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, μ = k + m := ⟨μ - k, by omega⟩
    have e1 : 2 * (k + m) + 1 - (R : ℕ) + 1 = 2 * m + 1 := by omega
    simp only [e1, Nat.add_sub_cancel_left]
    have := odd_mul_dfi_succ (A := A) k
    push_cast at this ⊢
    linear_combination (-(2 * (m : A) + 1)) * this

lemma deltaMap_H (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    deltaMap μ (Hop (delta A (2 * μ + 1)).wt (eD _ R)) =
      Hop (phiWt (delta A μ)) (deltaMap μ (eD _ R)) := by
  rw [H_eD, map_smul, deltaMap_eD, map_smul, H_xD, smul_comm]

/-! ### The morphisms -/

section hom

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (D1) `δ_μ` is a morphism of DP-lattices `Δ_A(2μ+1) → Φ(Δ_A(μ))`. -/
def deltaHom (μ : ℕ) : Hom (delta A (2 * μ + 1)) (phi (delta A μ)) :=
  homOfOne (deltaMap μ) (ext_single fun R => deltaMap_F μ R) (ext_single fun R => deltaMap_E μ R)
    (ext_single fun R => deltaMap_H μ R)

/-- (D1) the isomorphism `Δ_A(2μ+1) ≅ Φ(Δ_A(μ))` given by `δ_μ` and its inverse. -/
def deltaIso (μ : ℕ) : Iso (delta A (2 * μ + 1)) (phi (delta A μ)) :=
  Iso.ofInverse (deltaHom μ) (deltaInv μ) (deltaInv_deltaMap μ) (deltaMap_deltaInv μ)

/-- (D1) `δ_μ : Δ_A(2μ+1) → Φ(Δ_A(μ))`, `e'_R ↦ c_R x_R` (`c_{2s} = ⅟(2s−1)!!`,
`c_{2s+1} = ⅟(2s+1)!!`), is a morphism of DP-lattices, it is bijective, its inverse
`x_R ↦ c_R^{-1} e'_R` is a morphism, and the composites are the identities; hence
`Φ(Δ_A(μ)) ≅ Δ_A(2μ+1)`. -/
theorem D1 (μ : ℕ) :
    (∀ R : Fin (2 * μ + 1 + 1), deltaMap (A := A) μ (eD (2 * μ + 1) R) = cD (A := A) (R : ℕ) • xD μ R) ∧
    (∀ R : Fin (2 * μ + 1 + 1),
      deltaInv (A := A) μ (xD μ R) = cDinv (A := A) (R : ℕ) • eD (2 * μ + 1) R) ∧
    (∀ R : ℕ, cDinv (A := A) R * cD R = 1) ∧
    ∃ (f : Hom (delta A (2 * μ + 1)) (phi (delta A μ)))
      (g : Hom (phi (delta A μ)) (delta A (2 * μ + 1))),
      f.toLin = deltaMap μ ∧ g.toLin = deltaInv μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  refine ⟨deltaMap_eD μ, deltaInv_xD μ, cDinv_mul_cD, (deltaIso μ).hom, (deltaIso μ).inv, rfl,
    rfl, ?_, (deltaIso μ).hom_inv, (deltaIso μ).inv_hom⟩
  refine ⟨fun x y h => ?_, fun y => ⟨deltaInv μ y, ?_⟩⟩
  · change deltaMap μ x = deltaMap μ y at h
    have := congrArg (deltaInv μ) h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, deltaInv_deltaMap] at this
  · exact LinearMap.congr_fun (deltaMap_deltaInv μ) y

/-- (D1) `Φ(Δ_A(μ)) ≅ Δ_A(2μ+1)`: morphisms both ways whose composites are the identities. -/
theorem D1_iso (μ : ℕ) : Nonempty (Iso (phi (delta A μ)) (delta A (2 * μ + 1))) :=
  ⟨⟨(deltaIso μ).inv, (deltaIso μ).hom, (deltaIso μ).inv_hom, (deltaIso μ).hom_inv⟩⟩

end hom

end Doubling
