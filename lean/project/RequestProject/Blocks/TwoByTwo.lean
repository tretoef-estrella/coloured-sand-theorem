module

public import RequestProject.Blocks.Tools

/-!
# The 2×2 lemma (CSG1, §3, (L))

This file corresponds to **(L) the 2×2 lemma** of `CSG1_lemma_8_the_blocks.md`.

* `twoByTwo_nonempty` is the ring-independent core: over any commutative ring `R`, for an
  element `ϖ`, units `u₁ u₂ u₃` and naturals `eα eβ eγ`,
  `R² ⧸ span {(u₁ ϖ^{eα}, u₂ ϖ^{eβ}), (0, u₃ ϖ^{eγ})} ≅ R ⧸ (ϖ^x) × R ⧸ (ϖ^{eα+eγ−x})` with
  `x = min eα (min eβ eγ)`.  (This is more general than (L): any ring, any element, any
  units on all three entries.)
* `padicQuotEquiv n : ℤ_[p] ⧸ (p^n) ≃+ ZMod (p^n)`.
* `lemma_L` is (L) as stated: the matrix `[[p^{e₁}, w p^{e₂}], [0, p^{e₃}]]` acts on
  `Fin 2 → ℤ_[p]` by `Matrix.mulVecLin` (columns are images of basis vectors), its cokernel is
  `(Fin 2 → ℤ_[p]) ⧸ range`, and `≃+` is an isomorphism of additive groups.
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

section general

variable {R : Type*} [CommRing R]

lemma span_pair_diag (a b : R) :
    span R {((a, 0) : R × R), (0, b)} =
      Submodule.prod (Ideal.span {a} : Submodule R R) (Ideal.span {b} : Submodule R R) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ (rfl | rfl)
    · exact ⟨Ideal.subset_span rfl, zero_mem _⟩
    · exact ⟨zero_mem _, Ideal.subset_span rfl⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mem_span_pair]
    exact ⟨c, d, by ext <;> simp⟩

/-- `R² ⧸ span {(a,0), (0,b)} ≅ R ⧸ (a) × R ⧸ (b)`. -/
noncomputable def diagEquiv (a b : R) :
    ((R × R) ⧸ span R {((a, 0) : R × R), (0, b)}) ≃ₗ[R]
      (R ⧸ (Ideal.span {a} : Submodule R R)) × (R ⧸ (Ideal.span {b} : Submodule R R)) :=
  (Submodule.quotEquivOfEq _ _ (span_pair_diag a b)).trans (quotProdEquiv _ _)

/-- `R ⧸ (u ϖ^e) = R ⧸ (ϖ^e)` for a unit `u`. -/
noncomputable def unitPowQuot (u : Rˣ) (ϖ : R) (e : ℕ) :
    (R ⧸ (Ideal.span {(u : R) * ϖ ^ e} : Submodule R R)) ≃ₗ[R]
      (R ⧸ (Ideal.span {ϖ ^ e} : Submodule R R)) :=
  Submodule.quotEquivOfEq _ _ (Ideal.span_singleton_mul_left_unit u.isUnit _)

/-- **The 2×2 lemma, general form.** -/
theorem twoByTwo_nonempty (ϖ : R) (u₁ u₂ u₃ : Rˣ) (eα eβ eγ : ℕ) :
    Nonempty (((R × R) ⧸ span R {(((u₁ : R) * ϖ ^ eα, (u₂ : R) * ϖ ^ eβ) : R × R),
        (0, (u₃ : R) * ϖ ^ eγ)}) ≃ₗ[R]
      (R ⧸ (Ideal.span {ϖ ^ min eα (min eβ eγ)} : Submodule R R)) ×
        (R ⧸ (Ideal.span {ϖ ^ (eα + eγ - min eα (min eβ eγ))} : Submodule R R))) := by
  set α : R := u₁ * ϖ ^ eα
  set β : R := u₂ * ϖ ^ eβ
  set γ : R := u₃ * ϖ ^ eγ
  by_cases hA : eγ ≤ eα ∧ eγ ≤ eβ
  · -- the relation `γ z` clears the `z`-entry of the first relation
    have hmin : min eα (min eβ eγ) = eγ := by omega
    have hspan : span R {((α, β) : R × R), (0, γ)} = span R {((α, 0) : R × R), (0, γ)} := by
      have key : ((α, β) : R × R) = (α, 0) + ((u₂ * u₃⁻¹ : Rˣ) * ϖ ^ (eβ - eγ)) • (0, γ) := by
        ext
        · simp
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, zero_add, γ, β, Units.val_mul]
          rw [show (u₂ : R) * ϖ ^ eβ = u₂ * ϖ ^ (eβ - eγ + eγ) by rw [Nat.sub_add_cancel hA.2]]
          rw [pow_add]
          have : ((u₃⁻¹ : Rˣ) : R) * u₃ = 1 := by simp
          linear_combination (-(u₂ : R) * ϖ ^ (eβ - eγ) * ϖ ^ eγ) * this
      apply le_antisymm
      · rw [span_le]
        rintro _ (rfl | rfl)
        · rw [key]
          exact add_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
        · exact subset_span (by simp)
      · rw [span_le]
        rintro _ (rfl | rfl)
        · have : ((α, 0) : R × R) = (α, β) - ((u₂ * u₃⁻¹ : Rˣ) * ϖ ^ (eβ - eγ)) • (0, γ) := by
            rw [key]; abel
          rw [this]
          exact sub_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
        · exact subset_span (by simp)
    rw [hmin, show eα + eγ - eγ = eα by omega]
    exact ⟨(Submodule.quotEquivOfEq _ _ hspan).trans ((diagEquiv α γ).trans
      (((unitPowQuot u₁ ϖ eα).prodCongr (unitPowQuot u₃ ϖ eγ)).trans
        (LinearEquiv.prodComm R _ _)))⟩
  by_cases hB : eα ≤ eβ ∧ eα ≤ eγ
  · -- change of generators `g' = g + (β/α) z`
    have hmin : min eα (min eβ eγ) = eα := by omega
    set c : R := ((u₂ * u₁⁻¹ : Rˣ) : R) * ϖ ^ (eβ - eα)
    have hc : c * α = β := by
      simp only [c, α, β, Units.val_mul]
      rw [show (u₂ : R) * ϖ ^ eβ = u₂ * ϖ ^ (eβ - eα + eα) by rw [Nat.sub_add_cancel hB.1]]
      rw [pow_add]
      have : ((u₁⁻¹ : Rˣ) : R) * u₁ = 1 := by simp
      linear_combination ((u₂ : R) * ϖ ^ (eβ - eα) * ϖ ^ eα) * this
    let ψ : (R × R) →ₗ[R] (R × R) :=
      (LinearMap.fst R R R).prod (LinearMap.snd R R R - c • LinearMap.fst R R R)
    let ψ' : (R × R) →ₗ[R] (R × R) :=
      (LinearMap.fst R R R).prod (LinearMap.snd R R R + c • LinearMap.fst R R R)
    have hmap : (span R {((α, β) : R × R), (0, γ)}).map ψ = span R {((α, 0) : R × R), (0, γ)} := by
      rw [Submodule.map_span, Set.image_pair]
      congr 2
      · ext <;> simp [ψ, hc]
      · ext; simp [ψ]
    rw [hmin, show eα + eγ - eα = eγ by omega]
    exact ⟨(quotEquivOfSection _ _ ψ ψ' (fun w => by ext <;> simp [ψ, ψ'])
      (fun v => by simp [ψ, ψ']) hmap).trans ((diagEquiv α γ).trans
        ((unitPowQuot u₁ ϖ eα).prodCongr (unitPowQuot u₃ ϖ eγ)))⟩
  · -- `eβ` is the strict minimum: change of generators `z' = z + (α/β) g`
    have hmin : min eα (min eβ eγ) = eβ := by omega
    set c : R := ((u₁ * u₂⁻¹ : Rˣ) : R) * ϖ ^ (eα - eβ)
    have hc : c * β = α := by
      simp only [c, α, β, Units.val_mul]
      rw [show (u₁ : R) * ϖ ^ eα = u₁ * ϖ ^ (eα - eβ + eβ) by rw [Nat.sub_add_cancel (by omega)]]
      rw [pow_add]
      have : ((u₂⁻¹ : Rˣ) : R) * u₂ = 1 := by simp
      linear_combination ((u₁ : R) * ϖ ^ (eα - eβ) * ϖ ^ eβ) * this
    let ψ : (R × R) →ₗ[R] (R × R) :=
      (LinearMap.fst R R R - c • LinearMap.snd R R R).prod (LinearMap.snd R R R)
    let ψ' : (R × R) →ₗ[R] (R × R) :=
      (LinearMap.fst R R R + c • LinearMap.snd R R R).prod (LinearMap.snd R R R)
    set δ : R := ((u₁ * u₂⁻¹ * u₃ : Rˣ) : R) * ϖ ^ (eα + eγ - eβ)
    have hδ : c * γ = δ := by
      simp only [c, γ, δ, Units.val_mul]
      rw [show eα + eγ - eβ = (eα - eβ) + eγ by omega, pow_add]
      ring
    have hmap : (span R {((α, β) : R × R), (0, γ)}).map ψ = span R {((δ, 0) : R × R), (0, β)} := by
      rw [Submodule.map_span, Set.image_pair]
      have e1 : ψ (α, β) = (0, β) := by ext <;> simp [ψ, hc]
      have e2 : ψ (0, γ) = (-δ, γ) := by ext <;> simp [ψ, hδ]
      rw [e1, e2]
      have key : ((-δ, γ) : R × R) = -(δ, 0) + ((u₃ * u₂⁻¹ : Rˣ) * ϖ ^ (eγ - eβ)) • (0, β) := by
        ext
        · simp
        · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul, neg_zero, zero_add,
            γ, β, Units.val_mul]
          rw [show (u₃ : R) * ϖ ^ eγ = u₃ * ϖ ^ (eγ - eβ + eβ) by
            rw [Nat.sub_add_cancel (by omega)]]
          rw [pow_add]
          have : ((u₂⁻¹ : Rˣ) : R) * u₂ = 1 := by simp
          linear_combination (-(u₃ : R) * ϖ ^ (eγ - eβ) * ϖ ^ eβ) * this
      apply le_antisymm
      · rw [span_le]
        rintro _ (rfl | rfl)
        · exact subset_span (by simp)
        · rw [key]
          exact add_mem (neg_mem (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
      · rw [span_le]
        rintro _ (rfl | rfl)
        · have : ((δ, 0) : R × R) = -(-δ, γ) + ((u₃ * u₂⁻¹ : Rˣ) * ϖ ^ (eγ - eβ)) • (0, β) := by
            rw [key]; abel
          rw [this]
          exact add_mem (neg_mem (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
        · exact subset_span (by simp)
    rw [hmin]
    exact ⟨(quotEquivOfSection _ _ ψ ψ' (fun w => by ext <;> simp [ψ, ψ'])
      (fun v => by simp [ψ, ψ']) hmap).trans ((diagEquiv δ β).trans
        (((unitPowQuot (u₁ * u₂⁻¹ * u₃) ϖ (eα + eγ - eβ)).prodCongr
          (unitPowQuot u₂ ϖ eβ)).trans (LinearEquiv.prodComm R _ _)))⟩

end general

section padic

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_[p] ⧸ (p^n) ≃+ ZMod (p^n)`. -/
noncomputable def padicQuotEquiv (n : ℕ) :
    (ℤ_[p] ⧸ (Ideal.span {(p : ℤ_[p]) ^ n} : Submodule ℤ_[p] ℤ_[p])) ≃+ ZMod (p ^ n) :=
  ((Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))).toAddEquiv

/-- **(L) The 2×2 lemma.**  Over `ℤ_[p]`, for natural numbers `e₁ e₂ e₃` and a unit `w`, the
cokernel of `[[p^{e₁}, w p^{e₂}], [0, p^{e₃}]]` is `ℤ/p^x ⊕ ℤ/p^{e₁+e₃−x}`,
`x = min e₁ (min e₂ e₃)`. -/
theorem lemma_L (e₁ e₂ e₃ : ℕ) (w : ℤ_[p]) (hw : IsUnit w) :
    Nonempty (((Fin 2 → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin
        !![(p : ℤ_[p]) ^ e₁, w * (p : ℤ_[p]) ^ e₂; 0, (p : ℤ_[p]) ^ e₃])) ≃+
      ZMod (p ^ min e₁ (min e₂ e₃)) × ZMod (p ^ (e₁ + e₃ - min e₁ (min e₂ e₃)))) := by
  -- swap the two coordinates to reach the form of `twoByTwo_nonempty`
  let sw : (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] ℤ_[p] × ℤ_[p] :=
    { toFun := fun v => (v 1, v 0)
      invFun := fun x => ![x.2, x.1]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun v => by ext i; fin_cases i <;> rfl
      right_inv := fun x => rfl }
  have hrange : (LinearMap.range (Matrix.mulVecLin
      !![(p : ℤ_[p]) ^ e₁, w * (p : ℤ_[p]) ^ e₂; 0, (p : ℤ_[p]) ^ e₃])).map (sw : _ →ₗ[ℤ_[p]] _) =
      span ℤ_[p] {((((1 : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₃,
        ((hw.unit : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₂) : ℤ_[p] × ℤ_[p]),
        (0, ((1 : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₁)} := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    have : Set.range (sw ∘ (!![(p : ℤ_[p]) ^ e₁, w * (p : ℤ_[p]) ^ e₂; 0,
        (p : ℤ_[p]) ^ e₃]).col) = {((((1 : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₃,
        ((hw.unit : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₂) : ℤ_[p] × ℤ_[p]),
        (0, ((1 : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ e₁)} := by
      ext x
      simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff,
        Set.mem_singleton_iff, Fin.exists_fin_two]
      constructor
      · rintro (h | h) <;> [right; left] <;> rw [← h] <;> simp [sw, Matrix.col]
      · rintro (h | h) <;> [right; left] <;> rw [h] <;> simp [sw, Matrix.col]
    rw [LinearEquiv.coe_coe, this]
  obtain ⟨E⟩ := twoByTwo_nonempty (p : ℤ_[p]) 1 hw.unit 1 e₃ e₂ e₁
  have hmin : min e₃ (min e₂ e₁) = min e₁ (min e₂ e₃) := by omega
  rw [hmin, Nat.add_comm e₃ e₁] at E
  exact ⟨((Submodule.Quotient.equiv _ _ sw hrange).trans E).toAddEquiv.trans
    ((padicQuotEquiv _).prodCongr (padicQuotEquiv _))⟩

end padic

end ColouredSand.Blocks
