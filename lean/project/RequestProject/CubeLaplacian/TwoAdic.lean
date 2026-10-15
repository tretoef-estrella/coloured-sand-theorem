module

public import RequestProject.CubeLaplacian.Cokernel

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part D, (D1) — `T ⊗ ℤ_2 ≅ Syl_2 T`

`A = ℤ_[2]` is Mathlib's `PadicInt 2`; `T ⊗[ℤ] ℤ_[2]` is Mathlib's tensor product of
`ℤ`-modules.
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open TensorProduct

section D1

variable {T : Type*} [AddCommGroup T]

lemma zsmul_eq_of_dvd {a : ℕ} {y : T} (hy : (2 ^ a : ℕ) • y = 0) {i j : ℤ}
    (h : ((2 ^ a : ℕ) : ℤ) ∣ j - i) : i • y = j • y := by
  obtain ⟨c, hc⟩ := h
  have hj : j = i + c * ((2 ^ a : ℕ) : ℤ) := by linear_combination hc
  rw [hj, add_smul, mul_smul, natCast_zsmul, hy, smul_zero, add_zero]

lemma zsmul_eq_of_zmod {a : ℕ} {y : T} (hy : (2 ^ a : ℕ) • y = 0) {i j : ℤ}
    (h : (i : ZMod (2 ^ a)) = j) : i • y = j • y :=
  zsmul_eq_of_dvd hy (by exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub i j (2 ^ a)).1 h)

/-- (D1) from explicit data: `|T|` divides `2^a m` with `m` odd, `u m + v 2^a = 1`, and `2^a`
kills `Syl_2 T`. -/
lemma D1_of_data (a m : ℕ) (u v : ℤ) (huv : u * m + v * ((2 ^ a : ℕ) : ℤ) = 1)
    (hm : Nat.Coprime 2 m) (hN : ∀ t : T, (2 ^ a * m : ℕ) • t = 0)
    (h2 : ∀ y ∈ Syl2 T, (2 ^ a : ℕ) • y = 0) :
    Nonempty (T ⊗[ℤ] ℤ_[2] ≃+ Syl2 T) := by
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  have hk : ∀ t : T, (2 ^ a : ℕ) • ((u * m) • t) = 0 := by
    intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul,
      show ((2 ^ a : ℕ) : ℤ) * (u * m) = u * ((2 ^ a * m : ℕ) : ℤ) by push_cast; ring,
      mul_smul, natCast_zsmul, hN, smul_zero]
  let π : T →ₗ[ℤ] Syl2 T :=
    { toFun := fun t => ⟨(u * m) • t, ⟨a, hk t⟩⟩
      map_add' := fun t t' => Subtype.ext (smul_add _ _ _)
      map_smul' := fun c t => Subtype.ext (smul_comm _ _ _) }
  have hπ : ∀ t, (2 ^ a : ℕ) • π t = 0 := fun t => Subtype.ext (hk t)
  have hπS : ∀ y : Syl2 T, π y = y := by
    intro y
    apply Subtype.ext
    change (u * m) • (y : T) = y
    rw [zsmul_eq_of_dvd (h2 y y.2) (j := 1) ⟨v, by linear_combination -huv⟩, one_smul]
  let ρ : ℤ_[2] → ℤ := fun z => ((PadicInt.toZModPow a z).val : ℤ)
  have hρ : ∀ z, ((ρ z : ℤ) : ZMod (2 ^ a)) = PadicInt.toZModPow a z := by
    intro z; simp [ρ]
  let B : T →ₗ[ℤ] ℤ_[2] →ₗ[ℤ] Syl2 T :=
    LinearMap.mk₂ ℤ (fun t z => ρ z • π t)
      (fun t t' z => by dsimp only; rw [map_add, smul_add])
      (fun c t z => by dsimp only; rw [map_zsmul, smul_comm])
      (fun t z w => by
        dsimp only
        rw [← add_smul]
        exact zsmul_eq_of_zmod (hπ t) (by push_cast [hρ]; rw [map_add]))
      (fun c t z => by
        dsimp only
        rw [smul_smul]
        exact zsmul_eq_of_zmod (hπ t) (by push_cast [hρ]; rw [zsmul_eq_mul, map_mul,
          map_intCast]))
  let Φ : T ⊗[ℤ] ℤ_[2] →ₗ[ℤ] Syl2 T := TensorProduct.lift B
  let Ψ : Syl2 T →ₗ[ℤ] T ⊗[ℤ] ℤ_[2] :=
    (TensorProduct.mk ℤ T ℤ_[2]).flip 1 ∘ₗ (Syl2 T).subtype.toIntLinearMap
  have hΦ : ∀ t z, Φ (t ⊗ₜ z) = ρ z • π t := fun t z => by
    simp [Φ, B]
  have h1 : Φ ∘ₗ Ψ = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Ψ, LinearMap.flip_apply,
      TensorProduct.mk_apply, AddMonoidHom.coe_toIntLinearMap, AddSubgroup.coe_subtype]
    have hy : (2 ^ a : ℕ) • y = 0 := Subtype.ext (by simpa using h2 y y.2)
    rw [hΦ, hπS, zsmul_eq_of_zmod hy (i := ρ 1) (j := 1) (by push_cast [hρ]; rw [map_one]),
      one_smul]
  have hunit : IsUnit ((m : ℤ) : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff, Int.cast_natCast, PadicInt.norm_natCast_eq_one_iff]
    exact hm
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have h2' : Ψ ∘ₗ Φ = LinearMap.id := by
    refine TensorProduct.ext' fun t z => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hΦ, Ψ, LinearMap.flip_apply,
      TensorProduct.mk_apply, AddMonoidHom.coe_toIntLinearMap, AddSubgroup.coe_subtype,
      AddSubgroup.coe_zsmul]
    have hY : ((v * ((2 ^ a : ℕ) : ℤ)) • t) ⊗ₜ[ℤ] z = 0 := by
      have hz : z = (m : ℤ) • (w * z) := by
        rw [zsmul_eq_mul, ← mul_assoc, hw, one_mul]
      rw [hz, ← TensorProduct.smul_tmul, smul_smul,
        show (m : ℤ) * (v * ((2 ^ a : ℕ) : ℤ)) = v * ((2 ^ a * m : ℕ) : ℤ) by push_cast; ring,
        mul_smul, natCast_zsmul, hN, smul_zero, TensorProduct.zero_tmul]
    have hker : z - (ρ z : ℤ) • (1 : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ a} := by
      have := PadicInt.ker_toZModPow (p := 2) a
      rw [← this, RingHom.mem_ker, map_sub, zsmul_eq_mul, mul_one, map_intCast, hρ, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hker
    have hz : z = (ρ z : ℤ) • (1 : ℤ_[2]) + ((2 ^ a : ℕ) : ℤ) • c := by
      rw [zsmul_eq_mul] at hc
      rw [zsmul_eq_mul, zsmul_eq_mul]
      push_cast at hc ⊢
      linear_combination hc
    have ht : t = (u * m) • t + (v * ((2 ^ a : ℕ) : ℤ)) • t := by
      rw [← add_smul, huv, one_smul]
    have hX : ((u * m) • t) ⊗ₜ[ℤ] ((((2 ^ a : ℕ) : ℤ)) • c) = 0 := by
      rw [← TensorProduct.smul_tmul, natCast_zsmul, hk, TensorProduct.zero_tmul]
    conv_rhs => rw [ht, TensorProduct.add_tmul, hY, add_zero, hz, TensorProduct.tmul_add, hX,
      add_zero]
    rw [TensorProduct.smul_tmul]
    rfl
  exact ⟨(LinearEquiv.ofLinear Φ Ψ h1 h2').toAddEquiv⟩

/-- Part D, (D1): for every finite abelian group `T` (a finite `ℤ`-module),
`T ⊗_ℤ ℤ_[2] ≃+ Syl_2 T`. -/
theorem D1 (T : Type*) [AddCommGroup T] [Finite T] :
    Nonempty (T ⊗[ℤ] ℤ_[2] ≃+ Syl2 T) := by
  set N := Nat.card T
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  set a := N.factorization 2
  set m := N / 2 ^ a
  have hNam : 2 ^ a * m = N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have hm : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hN0
  have hcop : IsCoprime (m : ℤ) ((2 ^ a : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right a hm.symm)
  obtain ⟨u, v, huv⟩ := hcop
  refine D1_of_data a m u v huv hm (fun t => by rw [hNam]; exact card_nsmul_eq_zero') ?_
  rintro y ⟨k, hk⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (addOrderOf_dvd_of_nsmul_eq_zero hk)
  have hdvd : addOrderOf y ∣ 2 ^ a * m := hNam ▸ addOrderOf_dvd_natCard y
  rw [hj] at hdvd
  have : 2 ^ j ∣ 2 ^ a := (Nat.Coprime.pow_left j hm).dvd_of_dvd_mul_right hdvd
  rw [← hj] at this
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 this

end D1

end CubeLaplacian
