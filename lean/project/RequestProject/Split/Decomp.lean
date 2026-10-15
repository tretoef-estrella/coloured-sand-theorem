module

public import RequestProject.Split.ChangeOfBasis
public import RequestProject.Split.Block

/-!
# The computations of the *Proof* of Theorem B of `C12_split_move.md`

* `splitΨ`: `Sys_Ψ ≃ A ⊕ B ⊕ C ⊕ Dd = M^S × M^S × M^S × M^S`.
* `projΨ_comp_G`: in that decomposition, `G_Ψ` is the block operator `blk4 D0 D1 D2 (FS F)` with
  `D_k = DS (2 fl + k) p κ` (the four displayed formulas of the *Proof*).
* `split2`: `M^{S×{A,C}} ≃ A ⊕ C = M^S × M^S`.
* `proj2_comp_G`: in that decomposition, `G''` is the block operator `blkH (FS F) D1 E0 E1` with
  `E0 = DS fl p' κ'` and `E1` the same at the floors `(2f+1, 2f+2)`.
-/

@[expose] public section

namespace Split

open DirectSum Finset Payment
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [LinearOrder S]

/-! ### The decomposition `Sys_Ψ = A ⊕ B ⊕ C ⊕ Dd` -/

variable (A N S) in
/-- The four inclusions `M^S → M^S × M^S × M^S × M^S` (labels `A, B, C, Dd`) (*Proof* of
Theorem B of `C12_split_move.md`). -/
def inj4 (k : Fin 4) : Sys N S →ₗ[A] (Sys N S × Sys N S × Sys N S × Sys N S) :=
  (![LinearMap.inl A _ _, LinearMap.inr A _ _ ∘ₗ LinearMap.inl A _ _,
      LinearMap.inr A _ _ ∘ₗ LinearMap.inr A _ _ ∘ₗ LinearMap.inl A _ _,
      LinearMap.inr A _ _ ∘ₗ LinearMap.inr A _ _ ∘ₗ LinearMap.inr A _ _] :
    Fin 4 → (Sys N S →ₗ[A] (Sys N S × Sys N S × Sys N S × Sys N S))) k

omit [DecidableEq ι] [LinearOrder S] in
/-- The inclusion with label `A` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma inj4_0 (v : Sys N S) : inj4 A N S 0 v = (v, 0, 0, 0) := rfl
omit [DecidableEq ι] [LinearOrder S] in
/-- The inclusion with label `B` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma inj4_1 (v : Sys N S) : inj4 A N S 1 v = (0, v, 0, 0) := rfl
omit [DecidableEq ι] [LinearOrder S] in
/-- The inclusion with label `C` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma inj4_2 (v : Sys N S) : inj4 A N S 2 v = (0, 0, v, 0) := rfl
omit [DecidableEq ι] [LinearOrder S] in
/-- The inclusion with label `Dd` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma inj4_3 (v : Sys N S) : inj4 A N S 3 v = (0, 0, 0, v) := rfl

variable (A N S) in
/-- `Sys_Ψ → M^S × M^S × M^S × M^S`, `x ι_{s,(i,J)} ↦ x ι_{s,i}` in the `J`-th factor (*Proof* of
Theorem B of `C12_split_move.md`). -/
def projΨ : Sys (NΨ N) S →ₗ[A] (Sys N S × Sys N S × Sys N S × Sys N S) :=
  DirectSum.toModule A (S × (ι × Fin 4)) _ (fun q => inj4 A N S q.2.2 ∘ₗ slotLof A N S q.1 q.2.1)

variable (A N S) in
/-- The copy of `M^S` with label `J` inside `Sys_Ψ`, `x ι_{s,i} ↦ x ι_{s,(i,J)}` (*Proof* of
Theorem B of `C12_split_move.md`). -/
def embΨS (k : Fin 4) : Sys N S →ₗ[A] Sys (NΨ N) S :=
  DirectSum.toModule A (S × ι) _ (fun q => slotLof A (NΨ N) S q.1 (q.2, k))

/-- `projΨ (x ι_{s,(i,J)}) = inj_J (x ι_{s,i})` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma projΨ_slotLof (s : S) (i : ι) (k : Fin 4) (x : N i) :
    projΨ A N S (slotLof A (NΨ N) S s (i, k) x) = inj4 A N S k (slotLof A N S s i x) := by
  simp [projΨ, slotLof_eq, DirectSum.toModule_lof]

/-- `embΨS J (x ι_{s,i}) = x ι_{s,(i,J)}` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma embΨS_slotLof (k : Fin 4) (s : S) (i : ι) (x : N i) :
    embΨS A N S k (slotLof A N S s i x) = slotLof A (NΨ N) S s (i, k) x := by
  simp [embΨS, slotLof_eq, DirectSum.toModule_lof]

/-- `projΨ ∘ embΨS J = inj_J` (*Proof* of Theorem B of `C12_split_move.md`). -/
lemma projΨ_comp_embΨS (k : Fin 4) : projΨ A N S ∘ₗ embΨS A N S k = inj4 A N S k := by
  apply DirectSum.linearMap_ext; rintro ⟨s, i⟩; refine LinearMap.ext fun x => ?_
  change projΨ A N S (embΨS A N S k (slotLof A N S s i x)) = inj4 A N S k (slotLof A N S s i x)
  rw [embΨS_slotLof, projΨ_slotLof]

variable (A N S) in
/-- The inverse of `projΨ` (*Proof* of Theorem B of `C12_split_move.md`). -/
def embΨ4 : (Sys N S × Sys N S × Sys N S × Sys N S) →ₗ[A] Sys (NΨ N) S :=
  (embΨS A N S 0).coprod ((embΨS A N S 1).coprod ((embΨS A N S 2).coprod (embΨS A N S 3)))

/-- `projΨ ∘ embΨ4 = id` (*Proof* of Theorem B of `C12_split_move.md`). -/
lemma projΨ_comp_embΨ4 : projΨ A N S ∘ₗ embΨ4 A N S = LinearMap.id := by
  have h := projΨ_comp_embΨS (A := A) (N := N) (S := S)
  refine LinearMap.ext fun v => ?_
  obtain ⟨a, b, c, d⟩ := v
  have ha := LinearMap.congr_fun (h 0) a
  have hb := LinearMap.congr_fun (h 1) b
  have hc := LinearMap.congr_fun (h 2) c
  have hd := LinearMap.congr_fun (h 3) d
  simp only [LinearMap.comp_apply] at ha hb hc hd
  simp only [embΨ4, LinearMap.comp_apply, LinearMap.coprod_apply, map_add, ha, hb, hc, hd,
    inj4_0, inj4_1, inj4_2, inj4_3, LinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add]

/-- `embΨ4 ∘ projΨ = id` (*Proof* of Theorem B of `C12_split_move.md`). -/
lemma embΨ4_comp_projΨ : embΨ4 A N S ∘ₗ projΨ A N S = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨s, i, k⟩; refine LinearMap.ext fun x => ?_
  change embΨ4 A N S (projΨ A N S (slotLof A (NΨ N) S s (i, k) x)) = slotLof A (NΨ N) S s (i, k) x
  rw [projΨ_slotLof]
  fin_cases k <;> simp [embΨ4]

variable (A N S) in
/-- `Sys_Ψ = A ⊕ B ⊕ C ⊕ Dd ≃ M^S × M^S × M^S × M^S` (*Proof* of Theorem B of
`C12_split_move.md`). -/
def splitΨ : Sys (NΨ N) S ≃ₗ[A] (Sys N S × Sys N S × Sys N S × Sys N S) :=
  LinearEquiv.ofLinear (projΨ A N S) (embΨ4 A N S) projΨ_comp_embΨ4 embΨ4_comp_projΨ

/-- `projΨ ((J m) ι_s) = inj_J (m ι_s)` for `m ∈ M` (*Proof* of Theorem B of
`C12_split_move.md`). -/
lemma projΨ_slotEmb_embΨ (k : Fin 4) (s : S) (m : ⨁ i, N i) :
    projΨ A N S (slotEmb A (NΨ N) S s (embΨ A N k m)) = inj4 A N S k (slotEmb A N S s m) := by
  have : (projΨ A N S ∘ₗ slotEmb A (NΨ N) S s ∘ₗ embΨ A N k : (⨁ i, N i) →ₗ[A] _) =
      inj4 A N S k ∘ₗ slotEmb A N S s := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embΨ, DirectSum.toModule_lof, slotEmb_lof]
    exact projΨ_slotLof s i k x
  exact LinearMap.congr_fun this m

variable [Fintype S]

/-- The four displayed formulas of the *Proof* of Theorem B of `C12_split_move.md`: in the
decomposition `A ⊕ B ⊕ C ⊕ Dd`, `G_Ψ` is the block operator
`(a, b, c, d) ↦ (D0 a + 2 F b, a + D1 b, 2 a + D1 c + 2 F d, c + D2 d)`. -/
lemma projΨ_comp_G (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    projΨ A N S ∘ₗ G (flΨ fl) (FΨ F) p κ =
      blk4 (DS (N := N) (fun i => 2 * fl i) p κ) (DS (fun i => 2 * fl i + 1) p κ)
        (DS (fun i => 2 * fl i + 2) p κ) (FS F) ∘ₗ projΨ A N S := by
  apply DirectSum.linearMap_ext; rintro ⟨s', i, k⟩; refine LinearMap.ext fun x => ?_
  change projΨ A N S (G (flΨ fl) (FΨ F) p κ (slotLof A (NΨ N) S s' (i, k) x)) =
    blk4 (DS (N := N) (fun i => 2 * fl i) p κ) (DS (fun i => 2 * fl i + 1) p κ)
        (DS (fun i => 2 * fl i + 2) p κ) (FS F) (projΨ A N S (slotLof A (NΨ N) S s' (i, k) x))
  rw [G_eq, LinearMap.add_apply, FS_slotLof, DS_slotLof, projΨ_slotLof]
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl | rfl
  · simp only [FΨ_lof0, map_add, map_smul, slotEmb_lof, map_sum,
      projΨ_slotLof, inj4_0, inj4_1, inj4_2, flΨ_0, blk4_apply, DS_slotLof, map_zero]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  · simp only [FΨ_lof1, map_add, map_smul, projΨ_slotEmb_embΨ, map_sum,
      projΨ_slotLof, inj4_0, inj4_1, flΨ_1, blk4_apply, DS_slotLof, FS_slotLof, map_zero]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  · simp only [FΨ_lof2, map_add, map_smul, slotEmb_lof, map_sum,
      projΨ_slotLof, inj4_2, inj4_3, flΨ_2, blk4_apply, DS_slotLof, map_zero]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  · simp only [FΨ_lof3, map_add, map_smul, projΨ_slotEmb_embΨ,
      map_sum, projΨ_slotLof, inj4_2, inj4_3, flΨ_3, blk4_apply, DS_slotLof, FS_slotLof,
      map_zero]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end Split
