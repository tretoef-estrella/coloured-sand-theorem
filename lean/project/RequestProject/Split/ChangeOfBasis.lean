module

public import RequestProject.Split.Basic

/-!
# Part A of `C12_split_move.md`: the change of basis

* (A1) `A1_theta_thetaInv`, `A1_thetaInv_theta`, and the equivalence `thetaEquiv`
  (`A1_thetaEquiv_coe`).
* (A2) `A2_theta_comp_F`: `θ ∘ F^{VΦ} = F^Ψ ∘ θ`.
* (A3) `A3_thetaS_comp_G` (with the equivalence `thetaSEquiv`) and `A3_coker`.
-/

@[expose] public section

namespace Split

open DirectSum Finset Payment
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]

/-- Shorthand for generators of `M_{VΦ}` (*Setting* of `C12_split_move.md`). -/
local notation "lV" => DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N)
/-- Shorthand for generators of `M_Ψ` (*Setting* of `C12_split_move.md`). -/
local notation "lP" => DirectSum.lof A (ι × Fin 4) (NΨ N)

/-! ### Values on generators -/

/-- `θ(b_0b_0 x) = A x` (*Setting*, "The change of basis", of `C12_split_move.md`). -/
@[simp] lemma theta_lof00 (i : ι) (x : N i) : theta (A := A) (lV (i, 0, 0) x) = lP (i, 0) x := by
  simp [theta, DirectSum.toModule_lof]

/-- `θ(b_0b_1 x) = B x + C x` (*Setting*, "The change of basis", of `C12_split_move.md`). -/
@[simp] lemma theta_lof01 (i : ι) (x : N i) :
    theta (A := A) (lV (i, 0, 1) x) = lP (i, 1) x + lP (i, 2) x := by
  simp [theta, DirectSum.toModule_lof]

/-- `θ(b_1b_0 x) = C x` (*Setting*, "The change of basis", of `C12_split_move.md`). -/
@[simp] lemma theta_lof10 (i : ι) (x : N i) : theta (A := A) (lV (i, 1, 0) x) = lP (i, 2) x := by
  simp [theta, DirectSum.toModule_lof]

/-- `θ(b_1b_1 x) = Dd x` (*Setting*, "The change of basis", of `C12_split_move.md`). -/
@[simp] lemma theta_lof11 (i : ι) (x : N i) : theta (A := A) (lV (i, 1, 1) x) = lP (i, 3) x := by
  simp [theta, DirectSum.toModule_lof]

/-- `θ^{-1}(A x) = b_0b_0 x` (*Part A*, (A1), of `C12_split_move.md`). -/
@[simp] lemma thetaInv_lof0 (i : ι) (x : N i) : thetaInv (A := A) (lP (i, 0) x) = lV (i, 0, 0) x := by
  simp [thetaInv, DirectSum.toModule_lof]

/-- `θ^{-1}(B x) = b_0b_1 x − b_1b_0 x` (*Part A*, (A1), of `C12_split_move.md`). -/
@[simp] lemma thetaInv_lof1 (i : ι) (x : N i) :
    thetaInv (A := A) (lP (i, 1) x) = lV (i, 0, 1) x - lV (i, 1, 0) x := by
  simp [thetaInv, DirectSum.toModule_lof]

/-- `θ^{-1}(C x) = b_1b_0 x` (*Part A*, (A1), of `C12_split_move.md`). -/
@[simp] lemma thetaInv_lof2 (i : ι) (x : N i) : thetaInv (A := A) (lP (i, 2) x) = lV (i, 1, 0) x := by
  simp [thetaInv, DirectSum.toModule_lof]

/-- `θ^{-1}(Dd x) = b_1b_1 x` (*Part A*, (A1), of `C12_split_move.md`). -/
@[simp] lemma thetaInv_lof3 (i : ι) (x : N i) : thetaInv (A := A) (lP (i, 3) x) = lV (i, 1, 1) x := by
  simp [thetaInv, DirectSum.toModule_lof]


/-- `F^{VΦ}(b_0b_0 x) = b_1b_0 x + b_0b_1 x` (*Setting*, "The tensor model", of
`C12_split_move.md`). -/
@[simp] lemma FVΦ_lof00 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FVΦ F (lV (i, 0, 0) x) = lV (i, 1, 0) x + lV (i, 0, 1) x := by
  simp [FVΦ, DirectSum.toModule_lof]

/-- `F^{VΦ}(b_0b_1 x) = b_1b_1 x + 2 b_0b_0 (F x)` (*Setting*, "The tensor model", of
`C12_split_move.md`). -/
@[simp] lemma FVΦ_lof01 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FVΦ F (lV (i, 0, 1) x) = lV (i, 1, 1) x + (2 : A) • embVΦ A N 0 0 (F (DirectSum.lof A ι N i x)) := by
  simp [FVΦ, DirectSum.toModule_lof]

/-- `F^{VΦ}(b_1b_0 x) = b_1b_1 x` (*Setting*, "The tensor model", of `C12_split_move.md`). -/
@[simp] lemma FVΦ_lof10 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FVΦ F (lV (i, 1, 0) x) = lV (i, 1, 1) x := by
  simp [FVΦ, DirectSum.toModule_lof]

/-- `F^{VΦ}(b_1b_1 x) = 2 b_1b_0 (F x)` (*Setting*, "The tensor model", of
`C12_split_move.md`). -/
@[simp] lemma FVΦ_lof11 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FVΦ F (lV (i, 1, 1) x) = (2 : A) • embVΦ A N 1 0 (F (DirectSum.lof A ι N i x)) := by
  simp [FVΦ, DirectSum.toModule_lof]

/-- `F^Ψ(A x) = B x + 2 C x` (*Setting*, "The split model", of `C12_split_move.md`). -/
@[simp] lemma FΨ_lof0 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΨ F (lP (i, 0) x) = lP (i, 1) x + (2 : A) • lP (i, 2) x := by
  simp [FΨ, DirectSum.toModule_lof]

/-- `F^Ψ(B x) = 2 A(F x)` (*Setting*, "The split model", of `C12_split_move.md`). -/
@[simp] lemma FΨ_lof1 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΨ F (lP (i, 1) x) = (2 : A) • embΨ A N 0 (F (DirectSum.lof A ι N i x)) := by
  simp [FΨ, DirectSum.toModule_lof]

/-- `F^Ψ(C x) = Dd x` (*Setting*, "The split model", of `C12_split_move.md`). -/
@[simp] lemma FΨ_lof2 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΨ F (lP (i, 2) x) = lP (i, 3) x := by
  simp [FΨ, DirectSum.toModule_lof]

/-- `F^Ψ(Dd x) = 2 C(F x)` (*Setting*, "The split model", of `C12_split_move.md`). -/
@[simp] lemma FΨ_lof3 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΨ F (lP (i, 3) x) = (2 : A) • embΨ A N 2 (F (DirectSum.lof A ι N i x)) := by
  simp [FΨ, DirectSum.toModule_lof]

/-- `θ ∘ b_0b_0 = A` as maps `M → M_Ψ` (*Proof* of (A2) of `C12_split_move.md`). -/
lemma theta_comp_embVΦ00 : theta ∘ₗ embVΦ A N 0 0 = embΨ A N 0 := by
  apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
  simp [embVΦ, embΨ, DirectSum.toModule_lof]

/-- `θ ∘ b_1b_0 = C` as maps `M → M_Ψ` (*Proof* of (A2) of `C12_split_move.md`). -/
lemma theta_comp_embVΦ10 : theta ∘ₗ embVΦ A N 1 0 = embΨ A N 2 := by
  apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
  simp [embVΦ, embΨ, DirectSum.toModule_lof]

/-- **(A1)** of `C12_split_move.md`, first half: `θ ∘ θ^{-1} = id`. -/
theorem A1_theta_thetaInv : (theta : (⨁ q, NVΦ N q) →ₗ[A] _) ∘ₗ thetaInv = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨i, j⟩; refine LinearMap.ext fun x => ?_
  fin_cases j <;> simp

/-- **(A1)** of `C12_split_move.md`, second half: `θ^{-1} ∘ θ = id`. -/
theorem A1_thetaInv_theta : (thetaInv : (⨁ q, NΨ N q) →ₗ[A] _) ∘ₗ theta = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨i, e, e'⟩; refine LinearMap.ext fun x => ?_
  fin_cases e <;> fin_cases e' <;> simp

/-- **(A1)** of `C12_split_move.md`: `θ` as an `A`-linear equivalence `M_{VΦ} ≃ M_Ψ`, with
inverse `thetaInv`. -/
def thetaEquiv : (⨁ q, NVΦ N q) ≃ₗ[A] (⨁ q, NΨ N q) :=
  LinearEquiv.ofLinear theta thetaInv A1_theta_thetaInv A1_thetaInv_theta

/-- **(A1)** of `C12_split_move.md`: the underlying map of the equivalence `thetaEquiv` is `θ`
(and that of its inverse is `thetaInv`). -/
theorem A1_thetaEquiv_coe :
    ((thetaEquiv (A := A) (N := N)) : (⨁ q, NVΦ N q) →ₗ[A] (⨁ q, NΨ N q)) = theta ∧
      ((thetaEquiv (A := A) (N := N)).symm : (⨁ q, NΨ N q) →ₗ[A] (⨁ q, NVΦ N q)) = thetaInv :=
  ⟨rfl, rfl⟩

/-- **(A2)** of `C12_split_move.md`: `θ ∘ F^{VΦ} = F^Ψ ∘ θ`. -/
theorem A2_theta_comp_F (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) :
    theta ∘ₗ FVΦ F = FΨ F ∘ₗ (theta : (⨁ q, NVΦ N q) →ₗ[A] _) := by
  apply DirectSum.linearMap_ext; rintro ⟨i, e, e'⟩; refine LinearMap.ext fun x => ?_
  have h0 := LinearMap.congr_fun (theta_comp_embVΦ00 (A := A) (N := N))
  have h1 := LinearMap.congr_fun (theta_comp_embVΦ10 (A := A) (N := N))
  simp only [LinearMap.comp_apply] at h0 h1
  fin_cases e <;> fin_cases e' <;> simp [h0, h1, two_smul] <;> abel

/-! ### (A3): the slotwise change of basis -/

variable {S : Type*} [Fintype S] [LinearOrder S]

omit [DecidableEq ι] in
/-- The floors of the tensor model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flVΦ_00 (fl : ι → ℕ) (i : ι) : flVΦ fl (i, 0, 0) = 2 * fl i := by simp [flVΦ]
omit [DecidableEq ι] in
/-- The floors of the tensor model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flVΦ_01 (fl : ι → ℕ) (i : ι) : flVΦ fl (i, 0, 1) = 2 * fl i + 1 := by simp [flVΦ]
omit [DecidableEq ι] in
/-- The floors of the tensor model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flVΦ_10 (fl : ι → ℕ) (i : ι) : flVΦ fl (i, 1, 0) = 2 * fl i + 1 := by simp [flVΦ]
omit [DecidableEq ι] in
/-- The floors of the tensor model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flVΦ_11 (fl : ι → ℕ) (i : ι) : flVΦ fl (i, 1, 1) = 2 * fl i + 2 := by
  simp [flVΦ]
omit [DecidableEq ι] in
/-- The floors of the split model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flΨ_0 (fl : ι → ℕ) (i : ι) : flΨ fl (i, 0) = 2 * fl i := by simp [flΨ]
omit [DecidableEq ι] in
/-- The floors of the split model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flΨ_1 (fl : ι → ℕ) (i : ι) : flΨ fl (i, 1) = 2 * fl i + 1 := by simp [flΨ]
omit [DecidableEq ι] in
/-- The floors of the split model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flΨ_2 (fl : ι → ℕ) (i : ι) : flΨ fl (i, 2) = 2 * fl i + 1 := by simp [flΨ]
omit [DecidableEq ι] in
/-- The floors of the split model (*Setting* of `C12_split_move.md`). -/
@[simp] lemma flΨ_3 (fl : ι → ℕ) (i : ι) : flΨ fl (i, 3) = 2 * fl i + 2 := by simp [flΨ]

omit [Fintype S] in
/-- `θ_S (x ι_{s,q}) = (θ (x at q)) ι_s` (*Part A*, (A3), of `C12_split_move.md`). -/
@[simp] lemma thetaS_slotLof (s : S) (q : ι × Fin 2 × Fin 2) (x : N q.1) :
    thetaS (A := A) S (slotLof A (NVΦ N) S s q x) = slotEmb A (NΨ N) S s (theta (A := A) (lV q x)) := by
  simp [thetaS, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `θ_S^{-1} (x ι_{s,q}) = (θ^{-1} (x at q)) ι_s` (*Part A*, (A3), of `C12_split_move.md`). -/
@[simp] lemma thetaInvS_slotLof (s : S) (q : ι × Fin 4) (x : N q.1) :
    thetaInvS (A := A) S (slotLof A (NΨ N) S s q x) = slotEmb A (NVΦ N) S s (thetaInv (A := A) (lP q x)) := by
  simp [thetaInvS, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `θ_S ∘ ι_s = ι_s ∘ θ` (*Part A*, (A3), of `C12_split_move.md`). -/
lemma thetaS_slotEmb (s : S) (m : ⨁ q, NVΦ N q) :
    thetaS (A := A) S (slotEmb A (NVΦ N) S s m) = slotEmb A (NΨ N) S s (theta (A := A) m) := by
  have : (thetaS S ∘ₗ slotEmb A (NVΦ N) S s : (⨁ q, NVΦ N q) →ₗ[A] _) =
      slotEmb A (NΨ N) S s ∘ₗ theta := by
    apply DirectSum.linearMap_ext; intro q; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, slotEmb_lof, thetaS_slotLof]
  exact LinearMap.congr_fun this m

omit [Fintype S] in
/-- `θ_S^{-1} ∘ ι_s = ι_s ∘ θ^{-1}` (*Part A*, (A3), of `C12_split_move.md`). -/
lemma thetaInvS_slotEmb (s : S) (m : ⨁ q, NΨ N q) :
    thetaInvS (A := A) S (slotEmb A (NΨ N) S s m) = slotEmb A (NVΦ N) S s (thetaInv (A := A) m) := by
  have : (thetaInvS S ∘ₗ slotEmb A (NΨ N) S s : (⨁ q, NΨ N q) →ₗ[A] _) =
      slotEmb A (NVΦ N) S s ∘ₗ thetaInv := by
    apply DirectSum.linearMap_ext; intro q; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, slotEmb_lof, thetaInvS_slotLof]
  exact LinearMap.congr_fun this m

omit [Fintype S] in
/-- `FS F ∘ ι_s = ι_s ∘ F` (*Part A*, (A3), of `C12_split_move.md`). -/
lemma FS_slotEmb {κ : Type*} [DecidableEq κ] {P : κ → Type*} [∀ k, AddCommGroup (P k)]
    [∀ k, Module A (P k)] (F : (⨁ k, P k) →ₗ[A] (⨁ k, P k)) (s : S) (m : ⨁ k, P k) :
    FS F (slotEmb A P S s m) = slotEmb A P S s (F m) := by
  have : (FS F ∘ₗ slotEmb A P S s : (⨁ k, P k) →ₗ[A] _) = slotEmb A P S s ∘ₗ F := by
    apply DirectSum.linearMap_ext; intro q; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, slotEmb_lof, FS_slotLof]
  exact LinearMap.congr_fun this m

omit [Fintype S] in
/-- `θ_S ∘ θ_S^{-1} = id` (*Part A*, (A3), of `C12_split_move.md`). -/
lemma thetaS_thetaInvS :
    (thetaS S : Sys (NVΦ N) S →ₗ[A] _) ∘ₗ thetaInvS S = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨s, q⟩; refine LinearMap.ext fun x => ?_
  change thetaS (A := A) S (thetaInvS (A := A) S (slotLof A (NΨ N) S s q x)) =
    slotLof A (NΨ N) S s q x
  rw [thetaInvS_slotLof, thetaS_slotEmb]
  have := LinearMap.congr_fun (A1_theta_thetaInv (A := A) (N := N)) (lP q x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [this, slotEmb_lof]

omit [Fintype S] in
/-- `θ_S^{-1} ∘ θ_S = id` (*Part A*, (A3), of `C12_split_move.md`). -/
lemma thetaInvS_thetaS :
    (thetaInvS S : Sys (NΨ N) S →ₗ[A] _) ∘ₗ thetaS S = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨s, q⟩; refine LinearMap.ext fun x => ?_
  change thetaInvS (A := A) S (thetaS (A := A) S (slotLof A (NVΦ N) S s q x)) =
    slotLof A (NVΦ N) S s q x
  rw [thetaS_slotLof, thetaInvS_slotEmb]
  have := LinearMap.congr_fun (A1_thetaInv_theta (A := A) (N := N)) (lV q x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [this, slotEmb_lof]

variable (S) in
/-- **(A3)** of `C12_split_move.md`: the slotwise change of basis `θ_S` as an `A`-linear
equivalence `Sys_{VΦ} ≃ Sys_Ψ` (its underlying map is `thetaS`). -/
def thetaSEquiv : Sys (NVΦ N) S ≃ₗ[A] Sys (NΨ N) S :=
  LinearEquiv.ofLinear (thetaS S) (thetaInvS S) thetaS_thetaInvS thetaInvS_thetaS

omit [Fintype S] in
/-- **(A3)** of `C12_split_move.md`: the underlying map of `thetaSEquiv` is `θ_S`. -/
theorem A3_thetaSEquiv_coe :
    ((thetaSEquiv (A := A) (N := N) S) : Sys (NVΦ N) S →ₗ[A] Sys (NΨ N) S) = thetaS S := rfl

/-- `θ_S` commutes with the payment/coupling parts (it preserves floors) (*Proof* of (A3) of
`C12_split_move.md`). -/
lemma thetaS_comp_DS (fl : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    thetaS (A := A) S ∘ₗ DS (N := NVΦ N) (flVΦ fl) p κ =
      DS (N := NΨ N) (flΨ fl) p κ ∘ₗ thetaS (A := A) S := by
  apply DirectSum.linearMap_ext; rintro ⟨s', i, e, e'⟩; refine LinearMap.ext fun x => ?_
  change thetaS (A := A) S (DS (flVΦ fl) p κ (slotLof A (NVΦ N) S s' (i, e, e') x)) =
    DS (flΨ fl) p κ (thetaS (A := A) S (slotLof A (NVΦ N) S s' (i, e, e') x))
  rw [DS_slotLof, thetaS_slotLof]
  simp only [map_add, map_smul, map_sum, thetaS_slotLof]
  have he : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  have he' : e' = 0 ∨ e' = 1 := by fin_cases e' <;> simp
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;>
    simp only [theta_lof00, theta_lof01, theta_lof10, theta_lof11, map_add,
      slotEmb_lof, DS_slotLof, smul_add, Finset.sum_add_distrib, flVΦ_00, flVΦ_01, flVΦ_10,
      flVΦ_11, flΨ_0, flΨ_1, flΨ_2, flΨ_3]
  abel

/-- **(A3)** of `C12_split_move.md`: `θ_S ∘ G[fl^{VΦ}, F^{VΦ}, p, κ] = G[fl^Ψ, F^Ψ, p, κ] ∘ θ_S`
for every slot type `S` and all halved data `(p, κ)`. -/
theorem A3_thetaS_comp_G (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    thetaS S ∘ₗ G (flVΦ fl) (FVΦ F) p κ = G (flΨ fl) (FΨ F) p κ ∘ₗ thetaS S := by
  rw [G_eq, G_eq, LinearMap.comp_add, LinearMap.add_comp, thetaS_comp_DS]
  congr 1
  apply DirectSum.linearMap_ext; rintro ⟨s', q⟩; refine LinearMap.ext fun x => ?_
  change thetaS (A := A) S (FS (FVΦ F) (slotLof A (NVΦ N) S s' q x)) =
    FS (FΨ F) (thetaS (A := A) S (slotLof A (NVΦ N) S s' q x))
  rw [FS_slotLof, thetaS_slotLof, thetaS_slotEmb, FS_slotEmb]
  have := LinearMap.congr_fun (A2_theta_comp_F (A := A) (N := N) F)
    (DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) q x)
  simp only [LinearMap.comp_apply] at this
  rw [this]

/-- **(A3)** of `C12_split_move.md`, consequence: for every `c ∈ A`,
`coker(c · G_{VΦ}) ≅ coker(c · G_Ψ)`. -/
theorem A3_coker (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (c : A) :
    Nonempty ((Sys (NVΦ N) S ⧸ LinearMap.range (c • G (flVΦ fl) (FVΦ F) p κ)) ≃ₗ[A]
      (Sys (NΨ N) S ⧸ LinearMap.range (c • G (flΨ fl) (FΨ F) p κ))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (thetaSEquiv S) ?_⟩
  have hsurj : LinearMap.range (thetaS (A := A) (N := N) S) = ⊤ :=
    LinearMap.range_eq_top.2 (thetaSEquiv (A := A) (N := N) S).surjective
  rw [A3_thetaSEquiv_coe, ← LinearMap.range_comp, LinearMap.comp_smul, A3_thetaS_comp_G,
    ← LinearMap.smul_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]

end Split
