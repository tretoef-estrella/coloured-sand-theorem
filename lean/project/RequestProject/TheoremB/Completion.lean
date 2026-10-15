module

public import RequestProject.TheoremB.Basic

/-!
# (B1) Sylow subgroups and `p`-adic completion

This file corresponds to **(B1) Sylow and p-adic completion** of `CS3_theorem_B.md`.

## Encoding

* `Syl_p G` is `AddCommGroup.primaryComponent G p` (see `RequestProject/TheoremB/Basic.lean`);
  internally we use the same subgroup as a `ℤ`-submodule, `sylSub p G`.
* `ℤ_[p] ⊗[ℤ] G` is Mathlib's tensor product of `ℤ`-modules.
* "`≅` as abelian groups" is an additive isomorphism `≃+`; the cokernel isomorphism is
  `ℤ_[p]`-linear (`≃ₗ[ℤ_[p]]`).
* A cokernel `coker M` is `Q ⧸ LinearMap.range M`, and `M ⊗ ℤ_[p]` is the base change
  `M.baseChange ℤ_[p] : ℤ_[p] ⊗[ℤ] P →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Q`.  For free modules of finite rank
  given by an integer matrix `N`, `coker (M ⊗ ℤ_[p])` is concretely the cokernel of the same
  matrix acting on `ι → ℤ_[p]` (`coker_tensor_padic_matrix`).

## Main results

* `sylow_tensor_padic`: for a finite abelian group `G`, `Syl_p G ≅ ℤ_[p] ⊗[ℤ] G`.
* `coker_tensor_padic`: `ℤ_[p] ⊗ coker M ≅ coker (M ⊗ ℤ_[p])` for **every** `ℤ`-linear map `M`
  (more general than the file, which asks it for free modules of finite rank); it is a special
  case of `cokerBaseChange`, valid for any algebra `A` over any commutative ring `R`.
* `coker_tensor_padic_matrix`: the version for free modules of finite rank written with
  matrices.
-/

@[expose] public section

open TensorProduct

namespace ColouredSand.TheoremB

/-! ### Cokernels commute with base change -/

section baseChange

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- Right exactness of `A ⊗[R] -`: `A ⊗ coker M ≅ coker (A ⊗ M)` (as `A`-modules). -/
noncomputable def cokerBaseChange (M : P →ₗ[R] Q) :
    (A ⊗[R] (Q ⧸ LinearMap.range M)) ≃ₗ[A] (A ⊗[R] Q) ⧸ LinearMap.range (M.baseChange A) := by
  let g : A ⊗[R] Q →ₗ[A] A ⊗[R] (Q ⧸ LinearMap.range M) := (LinearMap.range M).mkQ.baseChange A
  have hg : Function.Surjective g := by
    have : ⇑g = ⇑((LinearMap.range M).mkQ.lTensor A) := LinearMap.baseChange_eq_ltensor _
    rw [this]
    exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = LinearMap.range (M.baseChange A) := by
    ext x
    have h1 := congrArg (x ∈ ·) (lTensor_mkQ A (LinearMap.range M))
    have h2 := congrArg (x ∈ ·) (LinearMap.lTensor_range (R := R) A (g := M))
    simp only [LinearMap.mem_ker, LinearMap.mem_range] at h1 h2 ⊢
    have hg' : g x = (LinearMap.range M).mkQ.lTensor A x := by
      exact congrFun (LinearMap.baseChange_eq_ltensor _) x
    rw [hg', h1, ← h2]
    simp only [LinearMap.baseChange_eq_ltensor]
  exact ((Submodule.quotEquivOfEq _ _ hker).symm.trans
    (LinearMap.quotKerEquivOfSurjective g hg)).symm

end baseChange

section padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- **(B1), second part.**  For a `ℤ`-linear map `M : P → Q`,
`ℤ_[p] ⊗ coker M ≅ coker (M ⊗ ℤ_[p])` as `ℤ_[p]`-modules.  (The file states this for free
modules of finite rank; it holds for all `ℤ`-modules.) -/
theorem coker_tensor_padic {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] (M : P →ₗ[ℤ] Q) :
    Nonempty ((ℤ_[p] ⊗[ℤ] (Q ⧸ LinearMap.range M)) ≃ₗ[ℤ_[p]]
      (ℤ_[p] ⊗[ℤ] Q) ⧸ LinearMap.range (M.baseChange ℤ_[p])) :=
  ⟨cokerBaseChange M⟩

/-- `A ⊗[R] (ι → R) ≅ ι → A`, `a ⊗ f ↦ a • (algebraMap ∘ f)`. -/
noncomputable def tensorPiEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] : A ⊗[R] (ι → R) ≃ₗ[A] (ι → A) :=
  TensorProduct.piScalarRight R A A ι

lemma tensorPiEquiv_tmul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : A) (f : ι → R) :
    tensorPiEquiv R A ι (a ⊗ₜ f) = fun i => f i • a :=
  by rw [tensorPiEquiv, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

/-- For free modules of finite rank: if `M' : (ι → A) → (κ → A)` is `A`-linear and agrees with
`M : (ι → R) → (κ → R)` on `R`-valued vectors, then `A ⊗ coker M ≅ coker M'`. -/
noncomputable def cokerBaseChangePi {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : (ι → R) →ₗ[R] (κ → R)) (M' : (ι → A) →ₗ[A] (κ → A))
    (h : ∀ f, M' (fun i => algebraMap R A (f i)) = fun k => algebraMap R A (M f k)) :
    (A ⊗[R] ((κ → R) ⧸ LinearMap.range M)) ≃ₗ[A] (κ → A) ⧸ LinearMap.range M' :=
  (cokerBaseChange M).trans
    (ColouredSand.Splitting.cokerEquivOfConj (M.baseChange A) M' (tensorPiEquiv R A ι)
      (tensorPiEquiv R A κ) (by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a f =>
          rw [LinearMap.baseChange_tmul, tensorPiEquiv_tmul, tensorPiEquiv_tmul]
          have : (fun i => f i • a) = a • (fun i => algebraMap R A (f i)) := by
            funext i; simp [Algebra.smul_def, mul_comm]
          rw [this, map_smul, h]
          funext k; simp [Algebra.smul_def, mul_comm]
        | add x y hx hy => simp only [map_add, hx, hy]))

/-- **(B1), second part, for free modules of finite rank.**  Let `N` be an integer matrix, viewed
as a `ℤ`-linear map `M : ℤ^ι → ℤ^κ`.  Then `ℤ_[p] ⊗ coker M ≅ coker (M ⊗ ℤ_[p])`, where
`M ⊗ ℤ_[p]` is the same matrix acting on `ℤ_[p]^ι`. -/
theorem coker_tensor_padic_matrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (N : Matrix κ ι ℤ) :
    Nonempty ((ℤ_[p] ⊗[ℤ] ((κ → ℤ) ⧸ LinearMap.range N.mulVecLin)) ≃ₗ[ℤ_[p]]
      (κ → ℤ_[p]) ⧸ LinearMap.range (N.map (Int.cast : ℤ → ℤ_[p])).mulVecLin) :=
  ⟨cokerBaseChangePi _ _ (fun f => by
    funext k
    simp [Matrix.mulVec, dotProduct])⟩

end padic

/-! ### `Syl_p G ≅ ℤ_[p] ⊗ G` for finite `G` -/

section sylow

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- If `p^a • y = 0`, then `k • y` only depends on `k mod p^a`. -/
lemma zsmul_eq_of_zmod {G : Type*} [AddCommGroup G] {a : ℕ} {y : G}
    (hy : ((p : ℤ) ^ a) • y = 0) {k l : ℤ} (hkl : (k : ZMod (p ^ a)) = (l : ZMod (p ^ a))) :
    k • y = l • y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkl
  obtain ⟨t, ht⟩ := hkl
  have : l = k + (p : ℤ) ^ a * t := by push_cast at ht; linarith
  rw [this, add_smul, mul_comm, mul_smul, hy, smul_zero, add_zero]

variable (G : Type*) [AddCommGroup G]

/-- Data for the proof: `|G| = p^a r`, `p ∤ r`, `s p^a + u r = 1`. -/
structure SylData (p : ℕ) (G : Type*) [AddCommGroup G] where
  a : ℕ
  r : ℕ
  s : ℤ
  u : ℤ
  hcard : Nat.card G = p ^ a * r
  hr : ¬ p ∣ r
  hsu : s * (p : ℤ) ^ a + u * r = 1

/-- Existence of the data. -/
noncomputable def sylData [Finite G] : SylData p G := by
  have hN : Nat.card G ≠ 0 := Nat.card_pos.ne'
  choose a r hr hcard using Nat.exists_eq_pow_mul_and_not_dvd hN p hp.out.ne_one
  have hcop : Nat.Coprime (p ^ a) r := Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hr)
  have hic := Nat.Coprime.isCoprime hcop
  choose s u hsu using hic
  exact ⟨a, r, s, u, hcard, hr, by push_cast at hsu; exact hsu⟩

variable {G}

instance (a : ℕ) : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

omit hp in
lemma card_smul_eq_zero (D : SylData p G) (x : G) : ((p : ℤ) ^ D.a * D.r) • x = 0 := by
  have h := card_nsmul_eq_zero' (x := x)
  rw [D.hcard] at h
  rw [← natCast_zsmul] at h
  exact_mod_cast h

omit hp in
/-- The projection `π = (u r) •` of `G` onto `Syl_p G`. -/
lemma proj_mem (D : SylData p G) (x : G) : ((p : ℤ) ^ D.a) • ((D.u * D.r) • x) = 0 := by
  rw [smul_smul, show (p : ℤ) ^ D.a * (D.u * D.r) = D.u * ((p : ℤ) ^ D.a * D.r) by ring,
    mul_smul, card_smul_eq_zero, smul_zero]

lemma syl_killed (D : SylData p G) {x : G} (hx : x ∈ sylSub p G) : ((p : ℤ) ^ D.a) • x = 0 := by
  obtain ⟨j, hj⟩ := hx
  have hdvd : p ^ j ∣ p ^ D.a * D.r := by rw [← hj, ← D.hcard]; exact addOrderOf_dvd_natCard x
  have hcop : Nat.Coprime (p ^ j) D.r := Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr D.hr)
  have h2 : p ^ j ∣ p ^ D.a := hcop.dvd_of_dvd_mul_right hdvd
  have h3 : (p ^ D.a) • x = 0 := by
    rw [← hj] at h2
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h2
  rw [← natCast_zsmul] at h3
  exact_mod_cast h3

lemma proj_id (D : SylData p G) {x : G} (hx : x ∈ sylSub p G) : (D.u * D.r) • x = x := by
  have h : D.u * D.r = 1 - D.s * (p : ℤ) ^ D.a := by linarith [D.hsu]
  rw [h, sub_smul, one_smul, mul_smul, syl_killed D hx, smul_zero, sub_zero]

/-- The bilinear map `(c, x) ↦ (c mod p^a) • π x`. -/
noncomputable def psiBil (D : SylData p G) : ℤ_[p] →ₗ[ℤ] G →ₗ[ℤ] G :=
  LinearMap.mk₂ ℤ (fun c x => (((PadicInt.toZModPow D.a c).val : ℕ) : ℤ) • ((D.u * D.r) • x))
    (fun c c' x => by
      dsimp only
      rw [← add_smul]
      refine zsmul_eq_of_zmod (proj_mem D x) ?_
      push_cast
      simp only [ZMod.natCast_zmod_val, map_add])
    (fun n c x => by
      dsimp only
      rw [smul_smul n]
      refine zsmul_eq_of_zmod (proj_mem D x) ?_
      push_cast
      simp only [ZMod.natCast_zmod_val, zsmul_eq_mul, map_mul, map_intCast])
    (fun c x y => by dsimp only; rw [smul_add, smul_add])
    (fun n c x => by dsimp only; rw [smul_comm (D.u * D.r) n x, smul_comm _ n])

/-- `ψ : ℤ_[p] ⊗ G → G`. -/
noncomputable def psi (D : SylData p G) : ℤ_[p] ⊗[ℤ] G →ₗ[ℤ] G := TensorProduct.lift (psiBil D)

lemma psi_tmul (D : SylData p G) (c : ℤ_[p]) (x : G) :
    psi D (c ⊗ₜ x) = (((PadicInt.toZModPow D.a c).val : ℕ) : ℤ) • ((D.u * D.r) • x) := rfl

lemma psi_mem (D : SylData p G) (z : ℤ_[p] ⊗[ℤ] G) : psi D z ∈ sylSub p G := by
  rw [mem_sylSub_iff]
  refine ⟨D.a, ?_⟩
  rw [← natCast_zsmul]
  push_cast
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => rw [psi_tmul, smul_comm, proj_mem, smul_zero]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/-- `(β · N) ⊗ x = 0` when `N • x = 0`. -/
lemma tmul_mul_eq_zero {x : G} {N : ℤ} (hN : N • x = 0) (β : ℤ_[p]) :
    (β * (N : ℤ_[p])) ⊗ₜ[ℤ] x = 0 := by
  rw [mul_comm, ← zsmul_eq_mul, TensorProduct.smul_tmul, hN, TensorProduct.tmul_zero]

lemma tmul_psi (D : SylData p G) (c : ℤ_[p]) (x : G) :
    (1 : ℤ_[p]) ⊗ₜ[ℤ] psi D (c ⊗ₜ x) = c ⊗ₜ x := by
  rw [psi_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, smul_smul, zsmul_eq_mul,
    mul_one]
  -- `c = c (u r) + c s p^a`
  have hru : IsUnit ((D.r : ℤ) : ℤ_[p]) :=
    ColouredSand.Strings.padicInt_isUnit_intCast (by exact_mod_cast D.hr)
  obtain ⟨w, hw⟩ := hru.exists_right_inv
  set v : ℤ_[p] := (((PadicInt.toZModPow D.a c).val : ℕ) : ℤ_[p])
  have hv : c - v ∈ Ideal.span {(p : ℤ_[p]) ^ D.a} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub]
    simp [v]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hv
  have hNx := card_smul_eq_zero D x
  have key : c = (((D.u * D.r : ℤ) : ℤ_[p]) * v) +
      ((b * D.u) * (((p : ℤ) ^ D.a * D.r : ℤ) : ℤ_[p]) +
        (c * D.s * w) * (((p : ℤ) ^ D.a * D.r : ℤ) : ℤ_[p])) := by
    have h1 : ((D.s : ℤ_[p]) * (p : ℤ_[p]) ^ D.a + D.u * D.r) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) D.hsu
    have hw' : ((D.r : ℤ) : ℤ_[p]) * w = 1 := hw
    push_cast at hw' ⊢
    linear_combination (-c) * h1 - ((D.u : ℤ_[p]) * D.r) * hb - (c * D.s * (p : ℤ_[p]) ^ D.a) * hw'
  have hcast : ((D.u * D.r * (((PadicInt.toZModPow D.a c).val : ℕ) : ℤ) : ℤ) : ℤ_[p]) =
      ((D.u * D.r : ℤ) : ℤ_[p]) * v := by
    simp only [v]; push_cast; ring
  rw [hcast]
  conv_rhs => rw [key]
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, tmul_mul_eq_zero hNx,
    tmul_mul_eq_zero hNx, add_zero, add_zero]

/-- **The isomorphism `Syl_p G ≅ ℤ_[p] ⊗ G`** (as `ℤ`-modules), `s ↦ 1 ⊗ s`. -/
noncomputable def sylTensorEquiv (G : Type*) [AddCommGroup G] [Finite G] :
    sylSub p G ≃ₗ[ℤ] ℤ_[p] ⊗[ℤ] G :=
  let D := sylData (p := p) G
  { toFun := fun s => (1 : ℤ_[p]) ⊗ₜ s.1
    invFun := fun z => ⟨psi D z, psi_mem D z⟩
    map_add' := fun _ _ => by simp [TensorProduct.tmul_add]
    map_smul' := fun _ _ => by simp [TensorProduct.tmul_smul]
    left_inv := fun s => by
      ext
      change psi D ((1 : ℤ_[p]) ⊗ₜ s.1) = s.1
      rw [psi_tmul]
      have hs := proj_id D s.2
      rw [hs]
      conv_rhs => rw [← one_smul ℤ s.1]
      refine zsmul_eq_of_zmod (syl_killed D s.2) ?_
      simp
    right_inv := fun z => by
      change (1 : ℤ_[p]) ⊗ₜ psi D z = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => exact tmul_psi D c x
      | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy] }

/-- **(B1), first part.**  For every finite abelian group `G` and prime `p`,
`Syl_p G ≅ ℤ_[p] ⊗[ℤ] G` as abelian groups (`Syl_p G = AddCommGroup.primaryComponent G p`). -/
theorem sylow_tensor_padic (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G] [Finite G] :
    Nonempty (AddCommGroup.primaryComponent G p ≃+ ℤ_[p] ⊗[ℤ] G) :=
  ⟨(sylTensorEquiv (p := p) G).toAddEquiv⟩

end sylow

end ColouredSand.TheoremB
