module

public import RequestProject.Tensor2.VTensor

/-!
# `C23_the_tensor_product.md`: (P4) associativity, (P5) distributivity, (P8) the unit

Encodings (namespace `Tensor2`), reusing C18 (`one`, `DataEquiv`), C20 (`Doubling.Iso`,
`Doubling.Iso.ofDataEquiv`) and C22 (`Lemma35.dsum`, with `inlL x = Sum.elim x 0`,
`inrL y = Sum.elim 0 y` and the blockwise `blk`):

* "Reindexing along a bijection `e : M.ι ≃ N.ι`" is the linear map
  `LinearMap.funLeft A A e.symm : f ↦ f ∘ e⁻¹`, which sends the basis vector `δ_x` to `δ_{e x}`
  (`funLeft_symm_single`); its inverse is `LinearMap.funLeft A A e : g ↦ g ∘ e`
  (`δ_{e x} ↦ δ_x`). `isoOfReindex e …` is the isomorphism `M ≅ N` with these two underlying
  linear maps (built with C20's `Iso.ofDataEquiv`).
* (P4) `assocIso M N P : (M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)` reindexes along `Equiv.prodAssoc`,
  `((i, j), k) ↦ (i, (j, k))`.
* (P5) `distribRightIso M N P : dsum M N ⊗ P ≅ dsum (M ⊗ P) (N ⊗ P)` reindexes along
  `Equiv.sumProdDistrib`, `(inl i, k) ↦ inl (i, k)`, `(inr j, k) ↦ inr (j, k)`;
  `distribLeftIso M N P : M ⊗ dsum N P ≅ dsum (M ⊗ N) (M ⊗ P)` reindexes along
  `Equiv.prodSumDistrib`, `(i, inl j) ↦ inl (i, j)`, `(i, inr k) ↦ inr (i, k)`.
* (P8) `unitLeftIso M : one A ⊗ M ≅ M` reindexes along `Equiv.uniqueProd`, `((), i) ↦ i`;
  `unitRightIso M : M ⊗ one A ≅ M` reindexes along `Equiv.prodUnique`, `(i, ()) ↦ i`.
-/

@[expose] public section

noncomputable section

namespace Tensor2

open DPLattice Finset WeylFilt Doubling Lemma35

variable {A : Type*} [CommRing A]

/-! ### Reindexing -/

lemma funLeft_symm_single {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (x : ι) :
    LinearMap.funLeft A A e.symm (Pi.single x 1) = Pi.single (e x) 1 := by
  funext y
  simp only [LinearMap.funLeft_apply, Pi.single_apply,
    Equiv.symm_apply_eq]

lemma funLeft_single {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (x : ι) :
    LinearMap.funLeft A A e (Pi.single (e x) 1) = Pi.single x 1 := by
  funext y
  simp only [LinearMap.funLeft_apply, Pi.single_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- (P4), (P5), (P8): the isomorphism `M ≅ N` given by reindexing along a bijection
`e : M.ι ≃ N.ι` which preserves weights and intertwines `F^{(r)}`, `E^{(r)}`; the underlying
linear maps are `f ↦ f ∘ e⁻¹` and `g ↦ g ∘ e`. -/
def isoOfReindex {M N : DPLattice A} (e : M.ι ≃ N.ι) (hw : ∀ i, N.wt (e i) = M.wt i)
    (hF : ∀ r, N.Fd r ∘ₗ LinearMap.funLeft A A e.symm = LinearMap.funLeft A A e.symm ∘ₗ M.Fd r)
    (hE : ∀ r, N.Ed r ∘ₗ LinearMap.funLeft A A e.symm = LinearMap.funLeft A A e.symm ∘ₗ M.Ed r) :
    Iso M N :=
  Iso.ofDataEquiv e ⟨hw, fun r f => LinearMap.congr_fun (hF r) f,
    fun r f => LinearMap.congr_fun (hE r) f⟩

lemma isoOfReindex_hom {M N : DPLattice A} (e : M.ι ≃ N.ι) (hw) (hF) (hE) :
    (isoOfReindex (A := A) (M := M) (N := N) e hw hF hE).hom.toLin =
      LinearMap.funLeft A A e.symm := rfl

lemma isoOfReindex_inv {M N : DPLattice A} (e : M.ι ≃ N.ι) (hw) (hF) (hE) :
    (isoOfReindex (A := A) (M := M) (N := N) e hw hF hE).inv.toLin =
      LinearMap.funLeft A A e := rfl

/-! ### (P4) Associativity -/

section assoc

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι] [DecidableEq κ]
  [DecidableEq μ]

omit [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] in
lemma funLeft_assoc_tprod (x : ι → A) (y : κ → A) (z : μ → A) :
    LinearMap.funLeft A A (Equiv.prodAssoc ι κ μ).symm (tprod (tprod x y) z) =
      tprod x (tprod y z) := by
  funext ⟨i, j, k⟩
  simp [mul_assoc]

lemma assoc_comm (D : ℕ → Module.End A (ι → A)) (G : ℕ → Module.End A (κ → A))
    (K : ℕ → Module.End A (μ → A)) (r : ℕ) :
    coFd D (coFd G K) r ∘ₗ LinearMap.funLeft A A (Equiv.prodAssoc ι κ μ).symm =
      LinearMap.funLeft A A (Equiv.prodAssoc ι κ μ).symm ∘ₗ coFd (coFd D G) K r := by
  refine ext_single fun ⟨⟨i, j⟩, k⟩ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, funLeft_symm_single, Equiv.prodAssoc_apply,
    single_prod_eq_tprod, single_prod_eq_tprod, single_prod_eq_tprod, single_prod_eq_tprod,
    coFd_tprod, coFd_tprod, map_sum]
  simp only [coFd_tprod, tprod_sum_left, tprod_sum_right, map_sum, funLeft_assoc_tprod]
  have h := Finset.sum_range_diag_flip (r + 1) (fun b c =>
    tprod (D b (Pi.single i 1)) (tprod (G c (Pi.single j 1)) (K (r - b - c) (Pi.single k 1))))
  simp only at h
  symm
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => by
    rw [show r - a = r - b - (a - b) by simp at ha hb; omega], h]
  refine sum_congr rfl fun b hb => ?_
  simp only [mem_range] at hb
  rw [show r + 1 - b = r - b + 1 by omega]

end assoc

section P4

variable (M N P : DPLattice A)

/-- (P4) `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`, reindexing along `((i, j), k) ↦ (i, (j, k))`. -/
def assocIso : Iso (tensor (tensor M N) P) (tensor M (tensor N P)) :=
  isoOfReindex (Equiv.prodAssoc M.ι N.ι P.ι) (fun _ => (add_assoc _ _ _).symm)
    (fun r => assoc_comm M.Fd N.Fd P.Fd r) (fun r => assoc_comm M.Ed N.Ed P.Ed r)

/-- (P4) the statement of the file: `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`; the underlying linear maps are
the reindexing along `((i, j), k) ↦ (i, (j, k))` (`f ↦ f ∘ e⁻¹`, so
`δ_{((i,j),k)} ↦ δ_{(i,(j,k))}`) and its inverse (`δ_{(i,(j,k))} ↦ δ_{((i,j),k)}`). -/
theorem P4 :
    (assocIso M N P).hom.toLin = LinearMap.funLeft A A (Equiv.prodAssoc M.ι N.ι P.ι).symm ∧
    (assocIso M N P).inv.toLin = LinearMap.funLeft A A (Equiv.prodAssoc M.ι N.ι P.ι) ∧
    (∀ i j k, (assocIso M N P).hom.toLin (Pi.single ((i, j), k) 1) = Pi.single (i, (j, k)) 1) ∧
    (∀ i j k, (assocIso M N P).inv.toLin (Pi.single (i, (j, k)) 1) = Pi.single ((i, j), k) 1) :=
  ⟨rfl, rfl, fun i j k => funLeft_symm_single (Equiv.prodAssoc M.ι N.ι P.ι) ((i, j), k),
    fun i j k => funLeft_single (Equiv.prodAssoc M.ι N.ι P.ι) ((i, j), k)⟩

end P4

/-! ### (P5) Distributivity -/

section distrib

variable {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι']
  [DecidableEq κ]

lemma blk_inlL_apply {ι₁ ι₂ κ₁ κ₂ : Type*} (f : (ι₁ → A) →ₗ[A] (ι₂ → A))
    (g : (κ₁ → A) →ₗ[A] (κ₂ → A)) (x : ι₁ → A) : blk f g (inlL x) = inlL (f x) :=
  LinearMap.congr_fun (blk_comp_inlL f g) x

lemma blk_inrL_apply {ι₁ ι₂ κ₁ κ₂ : Type*} (f : (ι₁ → A) →ₗ[A] (ι₂ → A))
    (g : (κ₁ → A) →ₗ[A] (κ₂ → A)) (y : κ₁ → A) : blk f g (inrL y) = inrL (g y) :=
  LinearMap.congr_fun (blk_comp_inrL f g) y

omit [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] in
lemma funLeft_sumProd_inl (x : ι → A) (z : κ → A) :
    LinearMap.funLeft A A (Equiv.sumProdDistrib ι ι' κ).symm (tprod (inlL x) z) =
      inlL (tprod x z) := by
  funext p
  rcases p with ⟨i, k⟩ | ⟨i, k⟩ <;> simp

omit [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] in
lemma funLeft_sumProd_inr (x : ι' → A) (z : κ → A) :
    LinearMap.funLeft A A (Equiv.sumProdDistrib ι ι' κ).symm (tprod (inrL x) z) =
      inrL (tprod x z) := by
  funext p
  rcases p with ⟨i, k⟩ | ⟨i, k⟩ <;> simp

omit [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] in
lemma funLeft_prodSum_inl (x : κ → A) (z : ι → A) :
    LinearMap.funLeft A A (Equiv.prodSumDistrib κ ι ι').symm (tprod x (inlL z)) =
      inlL (tprod x z) := by
  funext p
  rcases p with ⟨k, i⟩ | ⟨k, i⟩ <;> simp

omit [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] in
lemma funLeft_prodSum_inr (x : κ → A) (z : ι' → A) :
    LinearMap.funLeft A A (Equiv.prodSumDistrib κ ι ι').symm (tprod x (inrL z)) =
      inrL (tprod x z) := by
  funext p
  rcases p with ⟨k, i⟩ | ⟨k, i⟩ <;> simp

lemma distribRight_comm (D : ℕ → Module.End A (ι → A)) (D' : ℕ → Module.End A (ι' → A))
    (K : ℕ → Module.End A (κ → A)) (r : ℕ) :
    blk (coFd D K r) (coFd D' K r) ∘ₗ LinearMap.funLeft A A (Equiv.sumProdDistrib ι ι' κ).symm =
      LinearMap.funLeft A A (Equiv.sumProdDistrib ι ι' κ).symm ∘ₗ
        coFd (fun a => blk (D a) (D' a)) K r := by
  refine ext_single fun ⟨x, k⟩ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, funLeft_symm_single,
    single_prod_eq_tprod, coFd_tprod, map_sum]
  rcases x with i | i
  · rw [Equiv.sumProdDistrib_apply_left, single_inl, blk_inlL_apply, single_prod_eq_tprod,
      coFd_tprod, map_sum]
    simp only [single_inl, blk_inlL_apply, funLeft_sumProd_inl]
  · rw [Equiv.sumProdDistrib_apply_right, single_inr, blk_inrL_apply, single_prod_eq_tprod,
      coFd_tprod, map_sum]
    simp only [single_inr, blk_inrL_apply, funLeft_sumProd_inr]

lemma distribLeft_comm (K : ℕ → Module.End A (κ → A)) (D : ℕ → Module.End A (ι → A))
    (D' : ℕ → Module.End A (ι' → A)) (r : ℕ) :
    blk (coFd K D r) (coFd K D' r) ∘ₗ LinearMap.funLeft A A (Equiv.prodSumDistrib κ ι ι').symm =
      LinearMap.funLeft A A (Equiv.prodSumDistrib κ ι ι').symm ∘ₗ
        coFd K (fun a => blk (D a) (D' a)) r := by
  refine ext_single fun ⟨k, x⟩ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, funLeft_symm_single,
    single_prod_eq_tprod, coFd_tprod, map_sum]
  rcases x with i | i
  · rw [Equiv.prodSumDistrib_apply_left, single_inl, blk_inlL_apply, single_prod_eq_tprod,
      coFd_tprod, map_sum]
    simp only [single_inl, blk_inlL_apply, funLeft_prodSum_inl]
  · rw [Equiv.prodSumDistrib_apply_right, single_inr, blk_inrL_apply, single_prod_eq_tprod,
      coFd_tprod, map_sum]
    simp only [single_inr, blk_inrL_apply, funLeft_prodSum_inr]

end distrib

section P5

variable (M N P : DPLattice A)

/-- (P5) `dsum M N ⊗ P ≅ dsum (M ⊗ P) (N ⊗ P)`, reindexing along `(inl i, k) ↦ inl (i, k)`,
`(inr j, k) ↦ inr (j, k)`. -/
def distribRightIso : Iso (tensor (dsum M N) P) (dsum (tensor M P) (tensor N P)) :=
  isoOfReindex (Equiv.sumProdDistrib M.ι N.ι P.ι) (fun p => by rcases p with ⟨i | i, k⟩ <;> rfl)
    (fun r => distribRight_comm M.Fd N.Fd P.Fd r) (fun r => distribRight_comm M.Ed N.Ed P.Ed r)

/-- (P5) `M ⊗ dsum N P ≅ dsum (M ⊗ N) (M ⊗ P)`, reindexing along `(i, inl j) ↦ inl (i, j)`,
`(i, inr k) ↦ inr (i, k)`. -/
def distribLeftIso : Iso (tensor M (dsum N P)) (dsum (tensor M N) (tensor M P)) :=
  isoOfReindex (Equiv.prodSumDistrib M.ι N.ι P.ι) (fun p => by rcases p with ⟨i, j | j⟩ <;> rfl)
    (fun r => distribLeft_comm M.Fd N.Fd P.Fd r) (fun r => distribLeft_comm M.Ed N.Ed P.Ed r)

/-- (P5) the statement of the file: `dsum M N ⊗ P ≅ dsum (M ⊗ P) (N ⊗ P)` along
`(inl i, k) ↦ inl (i, k)`, `(inr j, k) ↦ inr (j, k)`, and `M ⊗ dsum N P ≅ dsum (M ⊗ N) (M ⊗ P)`
along `(i, inl j) ↦ inl (i, j)`, `(i, inr k) ↦ inr (i, k)`. The underlying linear maps are these
reindexings (`f ↦ f ∘ e⁻¹`) and their inverses (`g ↦ g ∘ e`); on basis vectors they are as
stated. -/
theorem P5 :
    ((distribRightIso M N P).hom.toLin =
        LinearMap.funLeft A A (Equiv.sumProdDistrib M.ι N.ι P.ι).symm ∧
      (distribRightIso M N P).inv.toLin =
        LinearMap.funLeft A A (Equiv.sumProdDistrib M.ι N.ι P.ι) ∧
      (∀ i k, (distribRightIso M N P).hom.toLin (Pi.single (Sum.inl i, k) 1) =
        Pi.single (Sum.inl (i, k)) 1) ∧
      (∀ j k, (distribRightIso M N P).hom.toLin (Pi.single (Sum.inr j, k) 1) =
        Pi.single (Sum.inr (j, k)) 1) ∧
      (∀ i k, (distribRightIso M N P).inv.toLin (Pi.single (Sum.inl (i, k)) 1) =
        Pi.single (Sum.inl i, k) 1) ∧
      (∀ j k, (distribRightIso M N P).inv.toLin (Pi.single (Sum.inr (j, k)) 1) =
        Pi.single (Sum.inr j, k) 1)) ∧
    ((distribLeftIso M N P).hom.toLin =
        LinearMap.funLeft A A (Equiv.prodSumDistrib M.ι N.ι P.ι).symm ∧
      (distribLeftIso M N P).inv.toLin =
        LinearMap.funLeft A A (Equiv.prodSumDistrib M.ι N.ι P.ι) ∧
      (∀ i j, (distribLeftIso M N P).hom.toLin (Pi.single (i, Sum.inl j) 1) =
        Pi.single (Sum.inl (i, j)) 1) ∧
      (∀ i k, (distribLeftIso M N P).hom.toLin (Pi.single (i, Sum.inr k) 1) =
        Pi.single (Sum.inr (i, k)) 1) ∧
      (∀ i j, (distribLeftIso M N P).inv.toLin (Pi.single (Sum.inl (i, j)) 1) =
        Pi.single (i, Sum.inl j) 1) ∧
      (∀ i k, (distribLeftIso M N P).inv.toLin (Pi.single (Sum.inr (i, k)) 1) =
        Pi.single (i, Sum.inr k) 1)) :=
  ⟨⟨rfl, rfl, fun i k => funLeft_symm_single (Equiv.sumProdDistrib M.ι N.ι P.ι) (Sum.inl i, k),
      fun j k => funLeft_symm_single (Equiv.sumProdDistrib M.ι N.ι P.ι) (Sum.inr j, k),
      fun i k => funLeft_single (Equiv.sumProdDistrib M.ι N.ι P.ι) (Sum.inl i, k),
      fun j k => funLeft_single (Equiv.sumProdDistrib M.ι N.ι P.ι) (Sum.inr j, k)⟩,
    ⟨rfl, rfl, fun i j => funLeft_symm_single (Equiv.prodSumDistrib M.ι N.ι P.ι) (i, Sum.inl j),
      fun i k => funLeft_symm_single (Equiv.prodSumDistrib M.ι N.ι P.ι) (i, Sum.inr k),
      fun i j => funLeft_single (Equiv.prodSumDistrib M.ι N.ι P.ι) (i, Sum.inl j),
      fun i k => funLeft_single (Equiv.prodSumDistrib M.ι N.ι P.ι) (i, Sum.inr k)⟩⟩

end P5

/-! ### (P8) The unit -/

section unit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma funLeft_uniqueProd_tprod (m : ι → A) :
    LinearMap.funLeft A A (Equiv.uniqueProd ι Unit).symm (tprod (Pi.single () 1) m) = m := by
  funext i
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma funLeft_prodUnique_tprod (m : ι → A) :
    LinearMap.funLeft A A (Equiv.prodUnique ι Unit).symm (tprod m (Pi.single () 1)) = m := by
  funext i
  simp

lemma unitLeft_comm (D : ℕ → Module.End A (ι → A)) (r : ℕ) :
    D r ∘ₗ LinearMap.funLeft A A (Equiv.uniqueProd ι Unit).symm =
      LinearMap.funLeft A A (Equiv.uniqueProd ι Unit).symm ∘ₗ coFd (oneFd A) D r := by
  refine ext_single fun ⟨u, i⟩ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, funLeft_symm_single, Equiv.uniqueProd_apply,
    single_prod_eq_tprod, coFd_tprod, sum_range_succ', sum_eq_zero fun a _ => by
      simp [oneFd], zero_add]
  simp only [oneFd, if_true, Module.End.one_apply, Nat.sub_zero]
  rw [Subsingleton.elim u (), funLeft_uniqueProd_tprod]

lemma unitRight_comm (D : ℕ → Module.End A (ι → A)) (r : ℕ) :
    D r ∘ₗ LinearMap.funLeft A A (Equiv.prodUnique ι Unit).symm =
      LinearMap.funLeft A A (Equiv.prodUnique ι Unit).symm ∘ₗ coFd D (oneFd A) r := by
  refine ext_single fun ⟨i, u⟩ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, funLeft_symm_single, Equiv.prodUnique_apply,
    single_prod_eq_tprod, coFd_tprod, sum_range_succ, sum_eq_zero fun a ha => by
      simp only [mem_range] at ha
      simp [oneFd, show r - a ≠ 0 by omega], zero_add]
  simp only [oneFd, Nat.sub_self, if_true, Module.End.one_apply]
  rw [Subsingleton.elim u (), funLeft_prodUnique_tprod]

end unit

section P8

variable (M : DPLattice A)

/-- (P8) `one A ⊗ M ≅ M`, reindexing along `((), i) ↦ i`. -/
def unitLeftIso : Iso (tensor (one A) M) M :=
  isoOfReindex (M := tensor (one A) M) (N := M) (Equiv.uniqueProd M.ι Unit)
    (fun _ => (zero_add _).symm) (fun r => unitLeft_comm M.Fd r) (fun r => unitLeft_comm M.Ed r)

/-- (P8) `M ⊗ one A ≅ M`, reindexing along `(i, ()) ↦ i`. -/
def unitRightIso : Iso (tensor M (one A)) M :=
  isoOfReindex (M := tensor M (one A)) (N := M) (Equiv.prodUnique M.ι Unit)
    (fun _ => (add_zero _).symm) (fun r => unitRight_comm M.Fd r)
    (fun r => unitRight_comm M.Ed r)

/-- (P8) the statement of the file: `one A ⊗ M ≅ M` along `((), i) ↦ i` and `M ⊗ one A ≅ M`
along `(i, ()) ↦ i`; the underlying linear maps are these reindexings and their inverses, so on
basis vectors `δ_{((),i)} ↦ δ_i ↦ δ_{((),i)}` and `δ_{(i,())} ↦ δ_i ↦ δ_{(i,())}`. -/
theorem P8 :
    (unitLeftIso M).hom.toLin = LinearMap.funLeft A A (Equiv.uniqueProd M.ι Unit).symm ∧
    (unitLeftIso M).inv.toLin = LinearMap.funLeft A A (Equiv.uniqueProd M.ι Unit) ∧
    (∀ i, (unitLeftIso M).hom.toLin (Pi.single ((), i) 1) = Pi.single i 1) ∧
    (∀ i, (unitLeftIso M).inv.toLin (Pi.single i 1) = Pi.single ((), i) 1) ∧
    (unitRightIso M).hom.toLin = LinearMap.funLeft A A (Equiv.prodUnique M.ι Unit).symm ∧
    (unitRightIso M).inv.toLin = LinearMap.funLeft A A (Equiv.prodUnique M.ι Unit) ∧
    (∀ i, (unitRightIso M).hom.toLin (Pi.single (i, ()) 1) = Pi.single i 1) ∧
    (∀ i, (unitRightIso M).inv.toLin (Pi.single i 1) = Pi.single (i, ()) 1) :=
  ⟨rfl, rfl, fun i => funLeft_symm_single (Equiv.uniqueProd M.ι Unit) ((), i),
    fun i => funLeft_single (Equiv.uniqueProd M.ι Unit) ((), i), rfl, rfl,
    fun i => funLeft_symm_single (Equiv.prodUnique M.ι Unit) (i, ()),
    fun i => funLeft_single (Equiv.prodUnique M.ι Unit) (i, ())⟩

end P8

end Tensor2
