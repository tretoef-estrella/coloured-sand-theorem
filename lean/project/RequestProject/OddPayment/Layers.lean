module

public import RequestProject.OddPayment.Basic
public import RequestProject.OddPayment.Chain

/-!
# The computations of the *Proof* of (A1) of `CSI7_the_twist_move.md`

* `FSo F` (the `F`-part `x ι_{s',i} ↦ (F x) ι_{s'}` of a system) and `DSm M` (the payment part
  `x ι_{s',i} ↦ Σ_s M i s s' • x ι_{s,i}` given by a matrix `M i` for each index `i`), with
  `Gp_eq : Gp p fl F Q = FSo F + DSm (fun i => (p : A) • Q (fl i))`.
* `DSmHom`: `M ↦ DSm M` is a monoid homomorphism `(ι → Matrix S S A) →* Module.End A (M^S)`
  (row-vector convention: `DSm (M₁ * M₂) = DSm M₁ ∘ DSm M₂`).  This is why the product of the
  layers in step 3 is `Q (p f) * ⋯ * Q (p f + p − 1)`, floors increasing from left to right.
* `layerEquiv p : M_T^S ≃ (Fin p → M^S)`, `x at (s, (i, j)) ↦ x ι_{s,i}` in the `j`-th layer
  (`M_T^S = Sys (NT p N) S`).
* `layerProj_comp_Gp`: in the layers, `G_T = Gp p (flT p fl) (FT p F) Q` is the chain operator
  `chainOp p D E` of `Chain.lean`, with `D j = DSm (fun i => (p : A) • Q (p · fl i + j))` and
  `E = −(p : A) • FSo F` (step 1 of the *Proof*).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

omit [Fintype S] in
/-- `oslot` is `DirectSum.lof` at `(s, i)` (*Setting* of `CSI7_the_twist_move.md`). -/
lemma oslot_eq_lof (s : S) (i : ι) (x : N i) :
    oslot A N S s i x = DirectSum.lof A (S × ι) (fun q => N q.2) (s, i) x := rfl

omit [Fintype S] in
/-- `(x at i) ι_s = x ι_{s,i}` (*Setting* of `CSI7_the_twist_move.md`). -/
@[simp] lemma oslotE_lof (s : S) (i : ι) (x : N i) :
    oslotE A N S s (DirectSum.lof A ι N i x) = oslot A N S s i x := by
  simp [oslotE, DirectSum.toModule_lof]

/-- The value of the system on a generator (*Setting* of `CSI7_the_twist_move.md`):
`Gp (x ι_{s',i}) = (F x) ι_{s'} + Σ_s (p * Q (fl i) s s') • x ι_{s,i}`. -/
lemma Gp_oslot (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A)
    (s' : S) (i : ι) (x : N i) :
    Gp p fl F Q (oslot A N S s' i x) = oslotE A N S s' (F (DirectSum.lof A ι N i x)) +
      ∑ s, ((p : A) * Q (fl i) s s') • oslot A N S s i x := by
  simp [Gp, oslot_eq_lof, DirectSum.toModule_lof]

/-- The `F`-part of a system: `x ι_{s',i} ↦ (F x) ι_{s'}` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
def FSo (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : Payment.Sys N S →ₗ[A] Payment.Sys N S :=
  DirectSum.toModule A (S × ι) (Payment.Sys N S) (fun q =>
    oslotE A N S q.1 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.2)

omit [Fintype S] in
/-- `FSo F (x ι_{s,i}) = (F x) ι_s` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
@[simp] lemma FSo_oslot (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (s : S) (i : ι) (x : N i) :
    FSo F (oslot A N S s i x) = oslotE A N S s (F (DirectSum.lof A ι N i x)) := by
  simp [FSo, oslot_eq_lof, DirectSum.toModule_lof]

/-- The payment part given by matrices: `x ι_{s',i} ↦ Σ_s M i s s' • x ι_{s,i}` (*Proof* of (A1)
of `CSI7_the_twist_move.md`). -/
def DSm (M : ι → Matrix S S A) : Payment.Sys N S →ₗ[A] Payment.Sys N S :=
  DirectSum.toModule A (S × ι) (Payment.Sys N S) (fun q =>
    ∑ s, M q.2 s q.1 • oslot A N S s q.2)

/-- The value of `DSm` on a generator (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
@[simp] lemma DSm_oslot (M : ι → Matrix S S A) (s' : S) (i : ι) (x : N i) :
    DSm M (oslot A N S s' i x) = ∑ s, M i s s' • oslot A N S s i x := by
  simp [DSm, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
/-- Two endomorphisms of `M^S` agreeing on generators are equal. -/
lemma sys_ext {f g : Payment.Sys N S →ₗ[A] Payment.Sys N S}
    (h : ∀ s i (x : N i), f (oslot A N S s i x) = g (oslot A N S s i x)) : f = g := by
  apply DirectSum.linearMap_ext
  rintro ⟨s, i⟩
  exact LinearMap.ext fun x => h s i x

/-- `DSm 1 = id` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma DSm_one : DSm (1 : ι → Matrix S S A) = (1 : Module.End A (Payment.Sys N S)) := by
  refine sys_ext fun s' i x => ?_
  simp [Matrix.one_apply, ite_smul]

/-- `DSm (M₁ * M₂) = DSm M₁ ∘ DSm M₂` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma DSm_mul (M₁ M₂ : ι → Matrix S S A) :
    DSm (M₁ * M₂) = (DSm M₁ * DSm M₂ : Module.End A (Payment.Sys N S)) := by
  refine sys_ext fun s' i x => ?_
  simp only [DSm_oslot, Module.End.mul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/-- `DSm (a • M) = a • DSm M` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma DSm_smul (a : A) (M : ι → Matrix S S A) :
    DSm (a • M) = a • (DSm M : Payment.Sys N S →ₗ[A] Payment.Sys N S) := by
  refine sys_ext fun s' i x => ?_
  simp [Finset.smul_sum, smul_smul]

variable (A N S) in
/-- `M ↦ DSm M` as a monoid homomorphism (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
def DSmHom : (ι → Matrix S S A) →* Module.End A (Payment.Sys N S) where
  toFun := DSm
  map_one' := DSm_one
  map_mul' := DSm_mul

/-- A system is its `F`-part plus its payment part:
`Gp p fl F Q = FSo F + DSm (fun i => (p : A) • Q (fl i))` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma Gp_eq (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) :
    Gp p fl F Q = FSo F + DSm (fun i => (p : A) • Q (fl i)) := by
  refine sys_ext fun s' i x => ?_
  simp [Gp_oslot]

variable (p : ℕ)

/-- `x ι_{s,i} ↦ x at (s, (i, j))`: the `j`-th layer `M^S → M_T^S` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
def embL (j : Fin p) : Payment.Sys N S →ₗ[A] Payment.Sys (NT p N) S :=
  DirectSum.toModule A (S × ι) _ (fun q => oslot A (NT p N) S q.1 (q.2, j))

/-- The decomposition into layers `M_T^S → (Fin p → M^S)`, `x at (s, (i, j)) ↦ x ι_{s,i}` in the
`j`-th layer (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
def layerProj : Payment.Sys (NT p N) S →ₗ[A] (Fin p → Payment.Sys N S) :=
  DirectSum.toModule A (S × (ι × Fin p)) _ (fun q =>
    LinearMap.single A (fun _ => Payment.Sys N S) q.2.2 ∘ₗ oslot A N S q.1 q.2.1)

omit [Fintype S] in
/-- `embL j (x ι_{s,i}) = x at (s, (i, j))` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
@[simp] lemma embL_oslot (j : Fin p) (s : S) (i : ι) (x : N i) :
    embL (A := A) p j (oslot A N S s i x) = oslot A (NT p N) S s (i, j) x := by
  simp [embL, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `layerProj (x at (s, (i, j))) = Pi.single j (x ι_{s,i})` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
@[simp] lemma layerProj_oslot (s : S) (q : ι × Fin p) (x : N q.1) :
    layerProj (A := A) p (oslot A (NT p N) S s q x) = Pi.single q.2 (oslot A N S s q.1 x) := by
  simp [layerProj, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `Σ_j b_j (v_j)` on a single layer (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma lsum_embL_single (j : Fin p) (y : Payment.Sys N S) :
    LinearMap.lsum A (fun _ => Payment.Sys N S) A (embL (A := A) p) (Pi.single j y) =
      embL (A := A) p j y := by
  simp [Pi.single_apply, apply_ite]

/-- `M_T^S ≃ (Fin p → M^S)`: the decomposition into the `p` layers `b_0, …, b_{p−1}`
(*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
noncomputable def layerEquiv : Payment.Sys (NT p N) S ≃ₗ[A] (Fin p → Payment.Sys N S) :=
  LinearEquiv.ofLinear (layerProj p) (LinearMap.lsum A (fun _ => Payment.Sys N S) A (embL p))
    (by
      refine LinearMap.pi_ext' fun j => ?_
      apply DirectSum.linearMap_ext
      rintro ⟨s, i⟩
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp, LinearMap.coe_single]
      rw [← oslot_eq_lof, lsum_embL_single, embL_oslot]
      exact layerProj_oslot (A := A) p s (i, j) x)
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨s, q⟩
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp]
      erw [layerProj_oslot]
      rw [lsum_embL_single, embL_oslot]
      rfl)

omit [Fintype S] in
/-- The underlying linear map of `layerEquiv` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma layerEquiv_toLinearMap :
    (layerEquiv (A := A) (N := N) (S := S) p :
      Payment.Sys (NT p N) S →ₗ[A] (Fin p → Payment.Sys N S)) = layerProj p := rfl

/-- `FT (x at (i, j)) = x at (i, j+1)` for `j + 1 < p` (*Part T* of `CSI7_the_twist_move.md`). -/
lemma FT_lof_lt (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p) (h : j.val + 1 < p)
    (x : N i) :
    FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      DirectSum.lof A (ι × Fin p) (NT p N) (i, ⟨j.val + 1, h⟩) x := by
  simp [FT, DirectSum.toModule_lof, h]

/-- `FT (x at (i, p−1)) = −p • b_0 (F x)` (*Part T* of `CSI7_the_twist_move.md`). -/
lemma FT_lof_last (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p) (h : ¬ j.val + 1 < p)
    (x : N i) :
    FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      -(p : A) • embT A N p ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x)) := by
  simp [FT, DirectSum.toModule_lof, h]

omit [Fintype S] in
/-- `(b_j m) ι_s ↦ Pi.single j (m ι_s)` under the decomposition into layers (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma layerProj_oslotE_embT (s : S) (j : Fin p) (m : ⨁ i, N i) :
    layerProj (A := A) p (oslotE A (NT p N) S s (embT A N p j m)) =
      Pi.single j (oslotE A N S s m) := by
  have : (layerProj (A := A) p ∘ₗ oslotE A (NT p N) S s ∘ₗ embT A N p j :
      (⨁ i, N i) →ₗ[A] _) =
      LinearMap.single A (fun _ => Payment.Sys N S) j ∘ₗ oslotE A N S s := by
    apply DirectSum.linearMap_ext
    intro i
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embT, DirectSum.toModule_lof, oslotE_lof,
      LinearMap.coe_single]
    exact layerProj_oslot (A := A) p s (i, j) x
  simpa using LinearMap.congr_fun this m

/-- The layer operators `D j = DSm (fun i => (p : A) • Q (p · fl i + j))` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
def layerD (fl : ι → ℕ) (Q : ℕ → Matrix S S A) (j : ℕ) : Module.End A (Payment.Sys N S) :=
  DSm (fun i => (p : A) • Q (p * fl i + j))

/-- **Step 1 of the *Proof* of (A1)** of `CSI7_the_twist_move.md`: in the layers,
`G_T = Gp p (flT p fl) (FT p F) Q` is the chain operator with `D = layerD p fl Q` and
`E = −p • FSo F`. -/
lemma layerProj_comp_Gp (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) :
    layerProj (A := A) (N := N) (S := S) p ∘ₗ Gp p (flT p fl) (FT p F) Q =
      chainOp p (layerD p fl Q) (-(p : A) • FSo F) ∘ₗ layerProj p := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i, j⟩
  refine LinearMap.ext fun x => ?_
  change layerProj p (Gp p (flT p fl) (FT p F) Q (oslot A (NT p N) S s' (i, j) x)) =
    chainOp p (layerD p fl Q) (-(p : A) • FSo F) (layerProj p (oslot A (NT p N) S s' (i, j) x))
  have hsum : layerProj (A := A) p (∑ s, ((p : A) * Q (flT p fl (i, j)) s s') •
      oslot A (NT p N) S s (i, j) x) = Pi.single j (layerD p fl Q j.val (oslot A N S s' i x)) := by
    simp only [layerD, DSm_oslot, map_sum, map_smul, layerProj_oslot, flT, Matrix.smul_apply,
      smul_eq_mul]
    funext k
    by_cases hk : k = j
    · subst hk; simp [Finset.sum_apply]
    · simp [Finset.sum_apply, hk]
  rw [Gp_oslot, map_add, hsum, layerProj_oslot]
  dsimp only
  by_cases hj : j.val + 1 < p
  · rw [FT_lof_lt p F i j hj, oslotE_lof, chainOp_single_lt _ _ _ _ hj]
    exact congrArg (· + _) (layerProj_oslot (A := A) p s' (i, ⟨j.val + 1, hj⟩) x)
  · rw [FT_lof_last p F i j hj, map_smul, map_smul, layerProj_oslotE_embT, chainOp_single_last _ _ _ _ hj]
    simp only [LinearMap.smul_apply, FSo_oslot, neg_smul]
    rw [Pi.single_neg, Pi.single_smul]

end ColouredSand.OddTwist
