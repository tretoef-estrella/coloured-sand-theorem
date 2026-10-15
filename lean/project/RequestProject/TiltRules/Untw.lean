module

public import RequestProject.TiltRules.Tools

/-!
# Untwisted models of `Δ(l)`, of the glued lattices, of `⊕` and of `V ⊗ −`
(auxiliary for `CSG4_tensor_rules.md`, §3)

## Encoding

(`K = ℚ_[p]`; see `RequestProject/TiltRules/Tools.lean` for `Untw` and `IsGen`.)

* `untwGlue p L M r x h : Untw (glueDP p L M r x h) (Idx L M)`: the coordinates `c` of `glueDP`
  (in the basis `ℓ_i, s̃_j` of the glued lattice) are sent to the vector `Psi c = Σ c_y b_y` of
  `V p L M`; the operators become `Fop`, `Eop`, and the lattice becomes `Lx p L M r x`.
* `untwDelta l : Untw (delta ℤ_[p] l) (Fin (l + 1))`: `θ = id`, operators `deltaF`, `deltaE`
  over `K`, lattice the integral vectors (`range coeL`).
* `untwDsum U W`: blockwise (`θ = blk θ_U θ_W`), lattice
  `{z | z ∘ inl ∈ Λ_U ∧ z ∘ inr ∈ Λ_W}`.
* `untwTensor U`: slotwise (`θ = sliceEquiv θ_U`), operators the coproducts `tensorFd`,
  `tensorEd`, lattice `{v | slice 0 v ∈ Λ_U ∧ slice 1 v ∈ Λ_U}` (this is `V ⊗ Λ_U`).
* Generators (`IsGen`): `ℓ_0, s̃_0` for `Lx` (`isGen_glue`, when `L = M + 2 r`), `e_0` for
  `Δ(l)` (`isGen_delta`), the union of the generators for `⊕` (`isGen_dsum`), and
  `b_ε ⊗ g_i` for `V ⊗ −` (`isGen_tensor`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-! ### Scalars of norm `≤ 1` -/

lemma smul_mem_of_norm {X : Type} {Λ : Submodule ℤ_[p] (X → ℚ_[p])} {c : ℚ_[p]} (hc : ‖c‖ ≤ 1)
    {v : X → ℚ_[p]} (hv : v ∈ Λ) : c • v ∈ Λ := by
  let c' : ℤ_[p] := ⟨c, hc⟩
  have : c • v = c' • v := by
    funext y; simp [c', Algebra.smul_def, PadicInt.algebraMap_apply]
  rw [this]; exact Λ.smul_mem _ hv

lemma natCast_smul_mem {X : Type} {Λ : Submodule ℤ_[p] (X → ℚ_[p])} (n : ℕ)
    {v : X → ℚ_[p]} (hv : v ∈ Λ) : (n : ℚ_[p]) • v ∈ Λ :=
  smul_mem_of_norm (IsUltrametricDist.norm_natCast_le_one ℚ_[p] n) hv

/-! ### The glued lattice -/

variable (p) in
/-- The untwisted model of `glueDP p L M r x h`: `θ = Psi`, operators `Fop`, `Eop`, lattice
`Lx p L M r x`. -/
def untwGlue (L M r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    Untw (glueDP p L M r x h) (Idx L M) where
  FK t := (PhiE p L M r x).toLinearMap ∘ₗ Fop p L M t ∘ₗ (PhiE p L M r x).symm.toLinearMap
  EK t := (PhiE p L M r x).toLinearMap ∘ₗ Eop p L M t ∘ₗ (PhiE p L M r x).symm.toLinearMap
  mF := glueDP_models_F r x h
  mE := glueDP_models_E r x h
  dp := IsDP.conj (isDP_V p L M) (PhiE p L M r x)
      (fun _ _ hv => inWt_Phi r x h.wt_ok hv) (fun _ _ hv => inWt_Psi r x h.wt_ok hv)
  θ := (PhiE p L M r x).symm
  FX := Fop p L M
  EX := Eop p L M
  θF t v := (PhiE p L M r x).symm_apply_apply _
  θE t v := (PhiE p L M r x).symm_apply_apply _
  Λ := Lx p L M r x
  hΛ v := by
    rw [mem_range_coeL_iff]
    show (∀ i : Idx L M, ‖v i‖ ≤ 1) ↔ Psi p L M r x v ∈ Lx p L M r x
    rw [mem_Lx_iff, Phi_Psi]

/-! ### Weyl lattices -/

variable (p) in
/-- The untwisted model of `Δ(l)`: the identity. -/
def untwDelta (l : ℕ) : Untw (delta ℤ_[p] l) (Fin (l + 1)) where
  FK t := deltaF l t
  EK t := deltaE l t
  mF := delta_models_F l
  mE := delta_models_E l
  dp := delta_isDP l
  θ := LinearEquiv.refl _ _
  FX t := deltaF l t
  EX t := deltaE l t
  θF _ _ := rfl
  θE _ _ := rfl
  Λ := LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (l + 1)))
  hΛ _ := Iff.rfl

/-! ### Direct sums -/

/-- The blockwise linear equivalence. -/
def blkEquiv {ι ι' κ κ' : Type*} (e : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' → ℚ_[p]))
    (f : (κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ' → ℚ_[p])) : (ι ⊕ κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' ⊕ κ' → ℚ_[p]) :=
  LinearEquiv.ofLinear (blk e.toLinearMap f.toLinearMap) (blk e.symm.toLinearMap f.symm.toLinearMap)
    (by rw [blk_comp, LinearEquiv.comp_symm, LinearEquiv.comp_symm, blk_id])
    (by rw [blk_comp, LinearEquiv.symm_comp, LinearEquiv.symm_comp, blk_id])

@[simp] lemma blkEquiv_apply {ι ι' κ κ' : Type*} (e : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' → ℚ_[p]))
    (f : (κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ' → ℚ_[p])) (z : ι ⊕ κ → ℚ_[p]) :
    blkEquiv e f z = blk e.toLinearMap f.toLinearMap z := rfl

lemma mem_range_coeL_sum {ι κ : Type*} (v : ι ⊕ κ → ℚ_[p]) :
    v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (ι ⊕ κ)) ↔
      v ∘ Sum.inl ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] ι) ∧
        v ∘ Sum.inr ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] κ) := by
  simp only [mem_range_coeL_iff, Sum.forall, Function.comp]

/-- The untwisted model of `M ⊕ N`. -/
def untwDsum {M N : DPLattice ℤ_[p]} {X Y : Type} (U : Untw M X) (W : Untw N Y) :
    Untw (dsum M N) (X ⊕ Y) where
  FK t := blk (U.FK t) (W.FK t)
  EK t := blk (U.EK t) (W.EK t)
  mF := blk_models U.mF W.mF
  mE := blk_models U.mE W.mE
  dp := dsum_isDP (⟨M.ι, M.wt, U.FK, U.EK, U.dp⟩ : DPLattice ℚ_[p]) ⟨N.ι, N.wt, W.FK, W.EK, W.dp⟩
  θ := blkEquiv U.θ W.θ
  FX t := blk (U.FX t) (W.FX t)
  EX t := blk (U.EX t) (W.EX t)
  θF t v := by
    funext y; rcases y with i | j
    · exact congrFun (U.θF t (v ∘ Sum.inl)) i
    · exact congrFun (W.θF t (v ∘ Sum.inr)) j
  θE t v := by
    funext y; rcases y with i | j
    · exact congrFun (U.θE t (v ∘ Sum.inl)) i
    · exact congrFun (W.θE t (v ∘ Sum.inr)) j
  Λ := Submodule.comap ((fstL : (X ⊕ Y → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) U.Λ ⊓
    Submodule.comap ((sndL : (X ⊕ Y → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) W.Λ
  hΛ v := by
    have := mem_range_coeL_sum (ι := M.ι) (κ := N.ι) v
    rw [U.hΛ, W.hΛ] at this
    exact this

lemma mem_untwDsum {M N : DPLattice ℤ_[p]} {X Y : Type} (U : Untw M X) (W : Untw N Y)
    (z : X ⊕ Y → ℚ_[p]) : z ∈ (untwDsum U W).Λ ↔ z ∘ Sum.inl ∈ U.Λ ∧ z ∘ Sum.inr ∈ W.Λ :=
  Iff.rfl

/-! ### `V ⊗ −` -/

lemma slice0_tensorFd {ι : Type*} {A : Type*} [CommRing A] (F : ℕ → Module.End A (ι → A))
    (t : ℕ) (v : Fin 2 × ι → A) : slice 0 (tensorFd F t v) = F t (slice 0 v) := by
  simp [tensorFd]

lemma slice1_tensorFd {ι : Type*} {A : Type*} [CommRing A] (F : ℕ → Module.End A (ι → A))
    (t : ℕ) (v : Fin 2 × ι → A) :
    slice 1 (tensorFd F t v) = F t (slice 1 v) + pred F t (slice 0 v) := by
  simp [tensorFd]

lemma slice0_tensorEd {ι : Type*} {A : Type*} [CommRing A] (E : ℕ → Module.End A (ι → A))
    (t : ℕ) (v : Fin 2 × ι → A) :
    slice 0 (tensorEd E t v) = E t (slice 0 v) + pred E t (slice 1 v) := by
  simp [tensorEd]

lemma slice1_tensorEd {ι : Type*} {A : Type*} [CommRing A] (E : ℕ → Module.End A (ι → A))
    (t : ℕ) (v : Fin 2 × ι → A) : slice 1 (tensorEd E t v) = E t (slice 1 v) := by
  simp [tensorEd]

lemma pred_conj {ι κ : Type*} {A : Type*} [CommRing A] (F : ℕ → Module.End A (ι → A))
    (G : ℕ → Module.End A (κ → A)) (φ : (ι → A) →ₗ[A] (κ → A)) (h : ∀ t v, φ (F t v) = G t (φ v))
    (t : ℕ) (v : ι → A) : φ (pred F t v) = pred G t (φ v) := by
  rcases t with _ | t
  · simp
  · simp [h]

lemma sliceMap_tensorFd {ι κ : Type*} {A : Type*} [CommRing A] (F : ℕ → Module.End A (ι → A))
    (G : ℕ → Module.End A (κ → A)) (φ : (ι → A) →ₗ[A] (κ → A)) (h : ∀ t v, φ (F t v) = G t (φ v))
    (t : ℕ) (v : Fin 2 × ι → A) : sliceMap φ (tensorFd F t v) = tensorFd G t (sliceMap φ v) := by
  apply ext_slice
  · rw [slice0_sliceMap, slice0_tensorFd, slice0_tensorFd, slice0_sliceMap, h]
  · rw [slice1_sliceMap, slice1_tensorFd, slice1_tensorFd, slice1_sliceMap, slice0_sliceMap,
      map_add, h, pred_conj F G φ h]

lemma sliceMap_tensorEd {ι κ : Type*} {A : Type*} [CommRing A] (F : ℕ → Module.End A (ι → A))
    (G : ℕ → Module.End A (κ → A)) (φ : (ι → A) →ₗ[A] (κ → A)) (h : ∀ t v, φ (F t v) = G t (φ v))
    (t : ℕ) (v : Fin 2 × ι → A) : sliceMap φ (tensorEd F t v) = tensorEd G t (sliceMap φ v) := by
  apply ext_slice
  · rw [slice0_sliceMap, slice0_tensorEd, slice0_tensorEd, slice0_sliceMap, slice1_sliceMap,
      map_add, h, pred_conj F G φ h]
  · rw [slice1_sliceMap, slice1_tensorEd, slice1_tensorEd, slice1_sliceMap, h]

lemma mem_range_coeL_prod {ι : Type*} (v : Fin 2 × ι → ℚ_[p]) :
    v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × ι)) ↔
      slice 0 v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] ι) ∧
        slice 1 v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] ι) := by
  simp only [mem_range_coeL_iff, slice_apply]
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h0, h1⟩ ⟨e, i⟩
    fin_cases e
    · exact h0 i
    · exact h1 i

/-- The untwisted model of `V ⊗ M`. -/
def untwTensor {M : DPLattice ℤ_[p]} {X : Type} (U : Untw M X) : Untw (tensorV M) (Fin 2 × X) where
  FK := tensorFd U.FK
  EK := tensorEd U.EK
  mF := tensor_models_F U.mF
  mE := tensor_models_E U.mE
  dp := (tensorV (⟨M.ι, M.wt, U.FK, U.EK, U.dp⟩ : DPLattice ℚ_[p])).isDP
  θ := sliceEquiv U.θ
  FX := tensorFd U.FX
  EX := tensorEd U.EX
  θF t v := sliceMap_tensorFd U.FK U.FX U.θ.toLinearMap U.θF t v
  θE t v := sliceMap_tensorEd U.EK U.EX U.θ.toLinearMap U.θE t v
  Λ := Submodule.comap ((slice 0 : (Fin 2 × X → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) U.Λ ⊓
    Submodule.comap ((slice 1 : (Fin 2 × X → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) U.Λ
  hΛ v := by
    have := mem_range_coeL_prod (ι := M.ι) v
    rw [U.hΛ, U.hΛ] at this
    refine this.trans ?_
    show _ ↔ slice 0 (sliceMap U.θ.toLinearMap v) ∈ U.Λ ∧ slice 1 (sliceMap U.θ.toLinearMap v) ∈ U.Λ
    rw [slice0_sliceMap, slice1_sliceMap]; rfl

lemma mem_untwTensor {M : DPLattice ℤ_[p]} {X : Type} (U : Untw M X) (v : Fin 2 × X → ℚ_[p]) :
    v ∈ (untwTensor U).Λ ↔ slice 0 v ∈ U.Λ ∧ slice 1 v ∈ U.Λ := Iff.rfl

/-! ### Generators -/

/-- Generators of the glued lattice: `ℓ_0` and `s̃_0` (for `L = M + 2 r`). -/
theorem isGen_glue (L M r : ℕ) (x : ℚ_[p]) (hLM : L = M + 2 * r) :
    IsGen (Fop p L M) (Lx p L M r x) ![ell p L M 0, stilde p L M r x 0] := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact ell_mem_Lx r x 0
    · exact stilde_mem_Lx r x 0
  · rw [Lx, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · apply Submodule.subset_span
      refine ⟨((i : ℕ), 0), ?_⟩
      simp only [Matrix.cons_val_zero]
      rw [F_ell _ 0 (Nat.zero_le _), Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul]
    · apply Submodule.subset_span
      refine ⟨((j : ℕ), 1), ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      have hj := Nat.le_of_lt_succ j.2
      unfold stilde
      rw [if_pos (Nat.zero_le _), if_pos hj, map_add, map_smul, F_ess _ 0 (Nat.zero_le _),
        F_ell _ _ (by omega), smul_smul]
      simp only [Nat.zero_add, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_smul,
        mul_one]
      rw [add_comm r (j : ℕ), Nat.choose_symm_add]

/-- Generators of `Δ(l)`: `e_0`. -/
theorem isGen_delta (l : ℕ) :
    IsGen (fun t => (deltaF l t : Module.End ℚ_[p] (Fin (l + 1) → ℚ_[p])))
      (LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (l + 1))))
      (fun _ : Unit => (Pi.single 0 1 : Fin (l + 1) → ℚ_[p])) := by
  refine ⟨fun _ => ⟨Pi.single 0 1, coeL_single 0⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [coeL_eq_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [show (z k • (Pi.single k 1 : Fin (l + 1) → ℚ_[p])) =
      z k • (deltaF l k (Pi.single 0 1) : Fin (l + 1) → ℚ_[p]) by
    congr 1; funext m
    rw [deltaF_single_apply, Pi.single_apply]
    simp only [Fin.val_zero, Nat.zero_add, Nat.choose_self, Nat.cast_one]
    by_cases h : m = k
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨((k : ℕ), ()), rfl⟩)

/-- Generators of `M ⊕ N`. -/
theorem isGen_dsum {X Y I J : Type} {F : ℕ → Module.End ℚ_[p] (X → ℚ_[p])}
    {G : ℕ → Module.End ℚ_[p] (Y → ℚ_[p])} {Λ : Submodule ℤ_[p] (X → ℚ_[p])}
    {Λ' : Submodule ℤ_[p] (Y → ℚ_[p])} {g : I → X → ℚ_[p]} {g' : J → Y → ℚ_[p]}
    (hg : IsGen F Λ g) (hg' : IsGen G Λ' g') :
    IsGen (fun t => blk (F t) (G t))
      (Submodule.comap ((fstL : (X ⊕ Y → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) Λ ⊓
        Submodule.comap ((sndL : (X ⊕ Y → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) Λ')
      (Sum.elim (fun i => inlL (g i)) (fun j => inrL (g' j))) := by
  refine ⟨fun k => ?_, ?_⟩
  · rcases k with i | j
    · refine ⟨hg.1 i, ?_⟩
      show (Sum.elim (g i) 0 : X ⊕ Y → ℚ_[p]) ∘ Sum.inr ∈ Λ'
      exact Λ'.zero_mem
    · refine ⟨?_, hg'.1 j⟩
      show (Sum.elim 0 (g' j) : X ⊕ Y → ℚ_[p]) ∘ Sum.inl ∈ Λ
      exact Λ.zero_mem
  · rintro z ⟨hz1, hz2⟩
    set S := Set.range fun q : ℕ × (I ⊕ J) =>
      blk (F q.1) (G q.1) (Sum.elim (fun i => inlL (g i)) (fun j => inrL (g' j)) q.2)
    have h1 : ∀ u ∈ Submodule.span ℤ_[p] (Set.range fun q : ℕ × I => F q.1 (g q.2)),
        (inlL u : X ⊕ Y → ℚ_[p]) ∈ Submodule.span ℤ_[p] S := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨t, i⟩, rfl⟩ := hw
        apply Submodule.subset_span
        refine ⟨(t, Sum.inl i), ?_⟩
        show blk (F t) (G t) (inlL (g i)) = _
        rw [← LinearMap.comp_apply, blk_comp_inlL]; rfl
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
      | smul c v _ hv =>
        rw [show (inlL (c • v) : X ⊕ Y → ℚ_[p]) = c • inlL v from
          LinearMap.map_smul_of_tower _ c v]
        exact Submodule.smul_mem _ c hv
    have h2 : ∀ u ∈ Submodule.span ℤ_[p] (Set.range fun q : ℕ × J => G q.1 (g' q.2)),
        (inrL u : X ⊕ Y → ℚ_[p]) ∈ Submodule.span ℤ_[p] S := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨t, j⟩, rfl⟩ := hw
        apply Submodule.subset_span
        refine ⟨(t, Sum.inr j), ?_⟩
        show blk (F t) (G t) (inrL (g' j)) = _
        rw [← LinearMap.comp_apply, blk_comp_inrL]; rfl
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
      | smul c v _ hv =>
        rw [show (inrL (c • v) : X ⊕ Y → ℚ_[p]) = c • inrL v from
          LinearMap.map_smul_of_tower _ c v]
        exact Submodule.smul_mem _ c hv
    have hz : z = inlL (z ∘ Sum.inl) + inrL (z ∘ Sum.inr) := by
      funext y; rcases y with i | j <;> simp
    rw [hz]
    exact Submodule.add_mem _ (h1 _ (hg.2 hz1)) (h2 _ (hg'.2 hz2))

/-- Generators of `V ⊗ M`: the `b_ε ⊗ g_i`. -/
theorem isGen_tensor {X I : Type} {F : ℕ → Module.End ℚ_[p] (X → ℚ_[p])}
    {Λ : Submodule ℤ_[p] (X → ℚ_[p])} {g : I → X → ℚ_[p]} (hg : IsGen F Λ g) :
    IsGen (tensorFd F)
      (Submodule.comap ((slice 0 : (Fin 2 × X → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) Λ ⊓
        Submodule.comap ((slice 1 : (Fin 2 × X → ℚ_[p]) →ₗ[ℚ_[p]] _).restrictScalars ℤ_[p]) Λ)
      (fun q : Fin 2 × I => bvec q.1 (g q.2)) := by
  refine ⟨fun ⟨e, i⟩ => ?_, ?_⟩
  · fin_cases e
    · refine ⟨?_, ?_⟩
      · show slice 0 (bvec 0 (g i)) ∈ Λ
        rw [slice_bvec_self]; exact hg.1 i
      · show slice 1 (bvec 0 (g i)) ∈ Λ
        rw [slice1_bvec0]; exact Λ.zero_mem
    · refine ⟨?_, ?_⟩
      · show slice 0 (bvec 1 (g i)) ∈ Λ
        rw [slice0_bvec1]; exact Λ.zero_mem
      · show slice 1 (bvec 1 (g i)) ∈ Λ
        rw [slice_bvec_self]; exact hg.1 i
  · rintro z ⟨hz0, hz1⟩
    set S := Set.range fun q : ℕ × (Fin 2 × I) => tensorFd F q.1 (bvec q.2.1 (g q.2.2))
    have hb1 : ∀ t i, bvec 1 (F t (g i)) ∈ Submodule.span ℤ_[p] S := by
      intro t i
      apply Submodule.subset_span
      exact ⟨(t, (1, i)), tensorFd_bvec1 F t (g i)⟩
    have hb0 : ∀ t i, bvec 0 (F t (g i)) ∈ Submodule.span ℤ_[p] S := by
      intro t i
      have h0 : tensorFd F t (bvec 0 (g i)) ∈ Submodule.span ℤ_[p] S :=
        Submodule.subset_span ⟨(t, (0, i)), rfl⟩
      rw [tensorFd_bvec0] at h0
      have h1 : bvec 1 (pred F t (g i)) ∈ Submodule.span ℤ_[p] S := by
        rcases t with _ | s
        · rw [pred_zero, LinearMap.zero_apply, map_zero]; exact Submodule.zero_mem _
        · rw [pred_succ]; exact hb1 s i
      have := Submodule.sub_mem _ h0 h1
      simpa using this
    have hgen : ∀ (e : Fin 2) u, u ∈ Submodule.span ℤ_[p] (Set.range fun q : ℕ × I => F q.1 (g q.2)) →
        bvec e u ∈ Submodule.span ℤ_[p] S := by
      intro e u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨t, i⟩, rfl⟩ := hw
        fin_cases e
        · exact hb0 t i
        · exact hb1 t i
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
      | smul c v _ hv =>
        rw [show bvec e (c • v) = c • bvec e v from LinearMap.map_smul_of_tower _ c v]
        exact Submodule.smul_mem _ c hv
    rw [eq_bvec_slice z]
    exact Submodule.add_mem _ (hgen 0 _ (hg.2 hz0)) (hgen 1 _ (hg.2 hz1))

end ColouredSand.TiltRules
