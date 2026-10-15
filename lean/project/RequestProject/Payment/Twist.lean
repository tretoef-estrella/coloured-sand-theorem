module

public import RequestProject.Payment.Basic
public import RequestProject.Payment.Block

/-!
# The computations of the *Proof* of Theorem A of `C11_payment_systems_twist.md`

* `G_eq`: a payment system splits as `G = FS F + DS fl p κ` (its `F`-part and its
  payment/coupling part).
* `DS_comp`: the coefficient identity of the *Proof*: with `T_0 = DS (2 fl) p κ` and
  `T_1 = DS (2 fl + 1) p κ` (the payment/coupling parts of `G_Φ` on the layers `e = 0`, `e = 1`),
  `T_0 ∘ T_1 = −2 · DS fl p' κ'`.  This is where the formulas for `p'` and `κ'` (including the
  middle sum over `s' < s < u`) are used.
* `splitEquiv`: `M_Φ^S ≃ B_0 × B_1 = M^S × M^S`.
* `projS_G_lof0`, `projS_G_lof1`: the two displayed formulas for `G_Φ(b_0 x ι_{s'})` and
  `G_Φ(b_1 x ι_{s'})`, i.e. in the decomposition `B_0 × B_1`, `G_Φ` is the block operator
  `(a, b) ↦ (T_0 a + 2 F b, a + T_1 b)`.
-/

@[expose] public section

namespace Payment

open DirectSum Finset
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [Fintype S] [LinearOrder S]

/-- The `F`-part of a payment system: `x ι_{s',i} ↦ (F x) ι_{s'}` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
def FS (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : Sys N S →ₗ[A] Sys N S :=
  DirectSum.toModule A (S × ι) (Sys N S) (fun q =>
    slotEmb A N S q.1 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.2)

/-- The payment/coupling part of a payment system with floor `g`:
`x ι_{s',i} ↦ 2 p_{s'}(g i) x ι_{s',i} + Σ_{s > s'} 2 κ_{s s'}(g i) x ι_{s,i}` (*Proof* of
Theorem A of `C11_payment_systems_twist.md`). -/
def DS (g : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) : Sys N S →ₗ[A] Sys N S :=
  DirectSum.toModule A (S × ι) (Sys N S) (fun q =>
    (2 * p q.1 (g q.2)) • slotLof A N S q.1 q.2
      + ∑ s ∈ Finset.univ.filter (q.1 < ·), (2 * κ s q.1 (g q.2)) • slotLof A N S s q.2)

omit [Fintype S] in
/-- `slotLof` is `DirectSum.lof` at `(s, i)` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma slotLof_eq (s : S) (i : ι) (x : N i) :
    slotLof A N S s i x = DirectSum.lof A (S × ι) (fun q => N q.2) (s, i) x := rfl

omit [Fintype S] in
/-- `FS F (x ι_{s,i}) = (F x) ι_s` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
@[simp] lemma FS_slotLof (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (s : S) (i : ι) (x : N i) :
    FS F (slotLof A N S s i x) = slotEmb A N S s (F (DirectSum.lof A ι N i x)) := by
  simp [FS, slotLof_eq, DirectSum.toModule_lof]

/-- The value of `DS` on a generator (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
@[simp] lemma DS_slotLof (g : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) (s' : S) (i : ι)
    (x : N i) :
    DS g p κ (slotLof A N S s' i x) = (2 * p s' (g i)) • slotLof A N S s' i x
      + ∑ s ∈ Finset.univ.filter (s' < ·), (2 * κ s s' (g i)) • slotLof A N S s i x := by
  simp [DS, slotLof_eq, DirectSum.toModule_lof]

/-- A payment system is its `F`-part plus its payment/coupling part:
`G[fl, F, p, κ] = FS F + DS fl p κ` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma G_eq (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) : G fl F p κ = FS F + DS fl p κ := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i⟩
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [← slotLof_eq, FS_slotLof, DS_slotLof]
  simp [G, slotLof_eq, DirectSum.toModule_lof, add_assoc]

/-- The coefficient computation of the *Proof* of Theorem A of
`C11_payment_systems_twist.md`: `T_0 ∘ T_1 = −2 · DS fl p' κ'`, where `T_e = DS (2 fl + e) p κ`.
On `x ι_{s'}`, the coefficient of `x ι_{s'}` is `4 p_{s'}(2f+1) p_{s'}(2f) = −2 · 2p'_{s'}(f)` and
that of `x ι_u` (`u > s'`) is `−2 · 2κ'_{u s'}(f)`. -/
lemma DS_comp (fl : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    DS (fun i => 2 * fl i) p κ ∘ₗ DS (fun i => 2 * fl i + 1) p κ =
      -(2 : A) • DS (N := N) fl (pT p) (κT p κ) := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i⟩
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [← slotLof_eq, DS_slotLof, DS_slotLof, map_add, map_smul, map_sum]
  simp only [map_smul, DS_slotLof, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm' (t' := Finset.univ.filter (s' < ·))
    (s' := fun u => Finset.univ.filter (fun s => s' < s ∧ s < u)) (h := by
      intro s u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.trans h2⟩
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩)]
  simp only [pT, κT, ← Finset.sum_smul]
  rw [add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · congr 1; ring
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [← add_smul, ← add_smul]
    congr 1
    have h4 : ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u),
        2 * κ s s' (2 * fl i + 1) * (2 * κ u s (2 * fl i)) =
        4 * ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u),
          κ s s' (2 * fl i + 1) * κ u s (2 * fl i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h4]; ring

/-- `B_e`: the copy of `M^S` inside `M_Φ^S` at the layer `e`, `x ι_{s,i} ↦ x at (s, (i, e))`
(*Proof* of Theorem A of `C11_payment_systems_twist.md`). -/
def embS (e : Fin 2) : Sys N S →ₗ[A] Sys (NΦ N) S :=
  DirectSum.toModule A (S × ι) _ (fun q => slotLof A (NΦ N) S q.1 (q.2, e))

/-- The decomposition `M_Φ^S → B_0 × B_1 = M^S × M^S`, `x at (s, (i, e)) ↦ x ι_{s,i}` in the
`e`-th factor (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
def projS : Sys (NΦ N) S →ₗ[A] Sys N S × Sys N S :=
  DirectSum.toModule A (S × (ι × Fin 2)) _ (fun q =>
    if q.2.2 = 0 then LinearMap.inl A _ _ ∘ₗ slotLof A N S q.1 q.2.1
    else LinearMap.inr A _ _ ∘ₗ slotLof A N S q.1 q.2.1)

omit [Fintype S] in
/-- `B_e (x ι_{s,i}) = x at (s, (i, e))` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
@[simp] lemma embS_slotLof (e : Fin 2) (s : S) (i : ι) (x : N i) :
    embS (A := A) e (slotLof A N S s i x) = slotLof A (NΦ N) S s (i, e) x := by
  simp [embS, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `b_0 x ι_{s,i} ↦ (x ι_{s,i}, 0)` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
@[simp] lemma projS_slotLof0 (s : S) (i : ι) (x : N i) :
    projS (A := A) (slotLof A (NΦ N) S s (i, 0) x) = (slotLof A N S s i x, 0) := by
  simp [projS, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `b_1 x ι_{s,i} ↦ (0, x ι_{s,i})` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
@[simp] lemma projS_slotLof1 (s : S) (i : ι) (x : N i) :
    projS (A := A) (slotLof A (NΦ N) S s (i, 1) x) = (0, slotLof A N S s i x) := by
  simp [projS, slotLof_eq, DirectSum.toModule_lof]

/-- `M_Φ^S = B_0 ⊕ B_1 ≃ M^S × M^S` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
noncomputable def splitEquiv : Sys (NΦ N) S ≃ₗ[A] Sys N S × Sys N S :=
  LinearEquiv.ofLinear projS (LinearMap.coprod (embS 0) (embS 1))
    (by
      apply LinearMap.prod_ext
      · apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        simp only [LinearMap.comp_apply, LinearMap.id_comp, LinearMap.coprod_apply,
          LinearMap.inl_apply, map_zero, add_zero]
        rw [← slotLof_eq, embS_slotLof, projS_slotLof0]
      · apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        simp only [LinearMap.comp_apply, LinearMap.id_comp, LinearMap.coprod_apply,
          LinearMap.inr_apply, map_zero, zero_add]
        rw [← slotLof_eq, embS_slotLof, projS_slotLof1])
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨s, i, e⟩
      refine LinearMap.ext fun x => ?_
      fin_cases e
      · simp only [LinearMap.comp_apply, LinearMap.id_comp]
        erw [projS_slotLof0]
        simp
        rfl
      · simp only [LinearMap.comp_apply, LinearMap.id_comp]
        erw [projS_slotLof1]
        simp
        rfl)

omit [Fintype S] in
/-- The underlying linear map of `splitEquiv` is `projS` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma splitEquiv_toLinearMap :
    (splitEquiv (A := A) (N := N) (S := S) : Sys (NΦ N) S →ₗ[A] Sys N S × Sys N S) = projS :=
  rfl

omit [Fintype S] in
/-- `(x at i) ι_s = x ι_{s,i}` (*Setting*, "Slots", of `C11_payment_systems_twist.md`). -/
@[simp] lemma slotEmb_lof (s : S) (i : ι) (x : N i) :
    slotEmb A N S s (DirectSum.lof A ι N i x) = slotLof A N S s i x := by
  simp [slotEmb, DirectSum.toModule_lof]

/-- `F^Φ(b_0 x) = b_1 x` (*Setting*, "The doubling `Φ`", of `C11_payment_systems_twist.md`). -/
@[simp] lemma FΦ_lof0 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΦ F (DirectSum.lof A (ι × Fin 2) (NΦ N) (i, 0) x) =
      DirectSum.lof A (ι × Fin 2) (NΦ N) (i, 1) x := by
  simp [FΦ, DirectSum.toModule_lof]

/-- `F^Φ(b_1 x) = 2 b_0 (F x)` (*Setting*, "The doubling `Φ`", of
`C11_payment_systems_twist.md`). -/
@[simp] lemma FΦ_lof1 (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (x : N i) :
    FΦ F (DirectSum.lof A (ι × Fin 2) (NΦ N) (i, 1) x) =
      (2 : A) • embΦ A N 0 (F (DirectSum.lof A ι N i x)) := by
  simp [FΦ, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `(b_0 m) ι_s ↦ (m ι_s, 0)` under `M_Φ^S ≃ B_0 × B_1` (*Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma projS_slotEmb_embΦ0 (s : S) (m : ⨁ i, N i) :
    projS (A := A) (slotEmb A (NΦ N) S s (embΦ A N 0 m)) = (slotEmb A N S s m, 0) := by
  have : (projS (A := A) ∘ₗ slotEmb A (NΦ N) S s ∘ₗ embΦ A N 0 : (⨁ i, N i) →ₗ[A] _) =
      LinearMap.inl A _ _ ∘ₗ slotEmb A N S s := by
    apply DirectSum.linearMap_ext
    intro i
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embΦ, DirectSum.toModule_lof, slotEmb_lof,
      LinearMap.inl_apply]
    exact projS_slotLof0 s i x
  simpa using LinearMap.congr_fun this m

/-- The formula `G_Φ(b_0 x ι_{s'}) = b_1 x ι_{s'} + 2p_{s'}(2f) b_0 x ι_{s'}
+ Σ_{s>s'} 2κ_{ss'}(2f) b_0 x ι_s` of the *Proof* of Theorem A of
`C11_payment_systems_twist.md`, read in `B_0 × B_1`. -/
lemma projS_G_lof0 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (s' : S) (i : ι) (x : N i) :
    projS (A := A) (G (flΦ fl) (FΦ F) p κ (slotLof A (NΦ N) S s' (i, 0) x)) =
      blockOp (DS (N := N) (fun i => 2 * fl i) p κ) (DS (fun i => 2 * fl i + 1) p κ) (FS F)
        (projS (A := A) (slotLof A (NΦ N) S s' (i, 0) x)) := by
  rw [G_eq, LinearMap.add_apply, FS_slotLof, DS_slotLof, projS_slotLof0, blockOp_apply,
    FΦ_lof0, slotEmb_lof]
  simp only [map_add, map_sum, map_smul, projS_slotLof0, projS_slotLof1, DS_slotLof, flΦ]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- The formula `G_Φ(b_1 x ι_{s'}) = 2 b_0 (F x) ι_{s'} + 2p_{s'}(2f+1) b_1 x ι_{s'}
+ Σ_{s>s'} 2κ_{ss'}(2f+1) b_1 x ι_s` of the *Proof* of Theorem A of
`C11_payment_systems_twist.md`, read in `B_0 × B_1`. -/
lemma projS_G_lof1 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (s' : S) (i : ι) (x : N i) :
    projS (A := A) (G (flΦ fl) (FΦ F) p κ (slotLof A (NΦ N) S s' (i, 1) x)) =
      blockOp (DS (N := N) (fun i => 2 * fl i) p κ) (DS (fun i => 2 * fl i + 1) p κ) (FS F)
        (projS (A := A) (slotLof A (NΦ N) S s' (i, 1) x)) := by
  rw [G_eq, LinearMap.add_apply, FS_slotLof, DS_slotLof, projS_slotLof1, blockOp_apply,
    FΦ_lof1, map_smul]
  simp only [map_add, map_sum, map_smul, projS_slotEmb_embΦ0, projS_slotLof1,
    DS_slotLof, flΦ, FS_slotLof]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end Payment
