module

public import RequestProject.Twist.All

/-!
# `C22_lemma_35_over_F2.md`: Part S — the direct sum of DP-lattices

Encodings (namespace `Lemma35`), reusing C18 (`DPLattice`, `IsDP`, `H`, `Hom`) and C19
(`WeylFilt.Hom.id`, `WeylFilt.Hom.comp`):

* Vectors of `M ⊕ N` are functions `M.ι ⊕ N.ι → A`; for such a `z`, `z ∘ Sum.inl` is its
  `M`-component and `z ∘ Sum.inr` its `N`-component.
* `blk f g` is the blockwise linear map `f ⊕ g`: `(blk f g z) ∘ inl = f (z ∘ inl)` and
  `(blk f g z) ∘ inr = g (z ∘ inr)`, i.e. `blk f g z = Sum.elim (f (z ∘ inl)) (g (z ∘ inr))`.
* `dsum M N` is `M ⊕ N`: basis `M.ι ⊕ N.ι`, weights `Sum.elim M.wt N.wt`,
  `F^{(r)} = blk (M.Fd r) (N.Fd r)`, `E^{(r)} = blk (M.Ed r) (N.Ed r)`.
* The inclusions are `inlL x = Sum.elim x 0`, `inrL y = Sum.elim 0 y`; the projections are
  `fstL z = z ∘ inl`, `sndL z = z ∘ inr`.
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {A : Type*} [CommRing A]

section blk

variable {ι ι' ι'' κ κ' κ'' : Type*}

/-- Part S: the blockwise linear map `f ⊕ g` on `ι ⊕ κ → A`:
`z ↦ Sum.elim (f (z ∘ inl)) (g (z ∘ inr))`. -/
def blk (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    (ι ⊕ κ → A) →ₗ[A] (ι' ⊕ κ' → A) where
  toFun z := Sum.elim (f (z ∘ Sum.inl)) (g (z ∘ Sum.inr))
  map_add' z w := by
    rw [show (z + w) ∘ Sum.inl = z ∘ Sum.inl + w ∘ Sum.inl from rfl,
      show (z + w) ∘ Sum.inr = z ∘ Sum.inr + w ∘ Sum.inr from rfl, map_add, map_add]
    funext p; cases p <;> rfl
  map_smul' c z := by
    rw [show (c • z) ∘ Sum.inl = c • (z ∘ Sum.inl) from rfl,
      show (c • z) ∘ Sum.inr = c • (z ∘ Sum.inr) from rfl, map_smul, map_smul]
    funext p; cases p <;> rfl

@[simp] lemma blk_inl (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (z : ι ⊕ κ → A) (i : ι') : blk f g z (Sum.inl i) = f (z ∘ Sum.inl) i := rfl

@[simp] lemma blk_inr (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (z : ι ⊕ κ → A) (k : κ') : blk f g z (Sum.inr k) = g (z ∘ Sum.inr) k := rfl

lemma blk_comp_inl (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (z : ι ⊕ κ → A) : blk f g z ∘ Sum.inl = f (z ∘ Sum.inl) := rfl

lemma blk_comp_inr (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (z : ι ⊕ κ → A) : blk f g z ∘ Sum.inr = g (z ∘ Sum.inr) := rfl

lemma blk_comp (f : (ι' → A) →ₗ[A] (ι'' → A)) (g : (κ' → A) →ₗ[A] (κ'' → A))
    (f' : (ι → A) →ₗ[A] (ι' → A)) (g' : (κ → A) →ₗ[A] (κ' → A)) :
    blk f g ∘ₗ blk f' g' = blk (f ∘ₗ f') (g ∘ₗ g') := by
  ext z p; cases p <;> rfl

lemma blk_id : blk (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) (LinearMap.id : (κ → A) →ₗ[A] _) =
    LinearMap.id := by
  ext z p; cases p <;> rfl

lemma blk_one : blk (1 : Module.End A (ι → A)) (1 : Module.End A (κ → A)) = 1 := blk_id

lemma blk_smul (c : A) (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    blk (c • f) (c • g) = c • blk f g := by
  ext z p; cases p <;> rfl

lemma blk_Hop (wt : ι → ℤ) (wt' : κ → ℤ) :
    blk (Hop (A := A) wt) (Hop wt') = Hop (Sum.elim wt wt') := by
  ext z p; cases p <;> rfl

/-- Part S: the inclusion `x ↦ Sum.elim x 0`. -/
def inlL : (ι → A) →ₗ[A] (ι ⊕ κ → A) where
  toFun x := Sum.elim x (0 : κ → A)
  map_add' x y := by funext p; cases p <;> simp
  map_smul' c x := by funext p; cases p <;> simp

/-- Part S: the inclusion `y ↦ Sum.elim 0 y`. -/
def inrL : (κ → A) →ₗ[A] (ι ⊕ κ → A) where
  toFun y := Sum.elim (0 : ι → A) y
  map_add' x y := by funext p; cases p <;> simp
  map_smul' c x := by funext p; cases p <;> simp

/-- Part S: the projection `z ↦ z ∘ inl`. -/
def fstL : (ι ⊕ κ → A) →ₗ[A] (ι → A) where
  toFun z := z ∘ Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Part S: the projection `z ↦ z ∘ inr`. -/
def sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A) where
  toFun z := z ∘ Sum.inr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma inlL_apply (x : ι → A) : (inlL (κ := κ) x : ι ⊕ κ → A) = Sum.elim x (0 : κ → A) := rfl
@[simp] lemma inrL_apply (y : κ → A) : (inrL (ι := ι) y : ι ⊕ κ → A) = Sum.elim (0 : ι → A) y := rfl
@[simp] lemma fstL_apply (z : ι ⊕ κ → A) : fstL z = z ∘ Sum.inl := rfl
@[simp] lemma sndL_apply (z : ι ⊕ κ → A) : sndL z = z ∘ Sum.inr := rfl

lemma blk_comp_inlL (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    blk f g ∘ₗ inlL = inlL ∘ₗ f := by
  ext x p; cases p
  · rfl
  · exact congrFun (map_zero g) _

lemma blk_comp_inrL (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    blk f g ∘ₗ inrL = inrL ∘ₗ g := by
  ext x p; cases p
  · exact congrFun (map_zero f) _
  · rfl

lemma fstL_comp_blk (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    fstL ∘ₗ blk f g = f ∘ₗ fstL := rfl

lemma sndL_comp_blk (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    sndL ∘ₗ blk f g = g ∘ₗ sndL := rfl

lemma single_inl [DecidableEq ι] [DecidableEq κ] (i : ι) :
    (Pi.single (Sum.inl i) (1 : A) : ι ⊕ κ → A) = inlL (Pi.single i 1) := by
  funext p; cases p <;> simp [Pi.single_apply]

lemma single_inr [DecidableEq ι] [DecidableEq κ] (k : κ) :
    (Pi.single (Sum.inr k) (1 : A) : ι ⊕ κ → A) = inrL (Pi.single k 1) := by
  funext p; cases p <;> simp [Pi.single_apply]

end blk

section dsum

variable (M N : DPLattice A)

lemma dsum_isDP : IsDP (Sum.elim M.wt N.wt) (fun r => blk (M.Fd r) (N.Fd r))
    (fun r => blk (M.Ed r) (N.Ed r)) where
  W_F p r q h := by
    rcases p with i | i <;> rcases q with j | j <;>
      simp only [single_inl, single_inr, blk_inl, blk_inr, inlL_apply, inrL_apply,
        Sum.elim_comp_inl, Sum.elim_comp_inr, map_zero, Pi.zero_apply, Sum.elim_inl,
        Sum.elim_inr] at h ⊢ <;>
      first | exact M.isDP.W_F i r j h | exact N.isDP.W_F i r j h
  W_E p r q h := by
    rcases p with i | i <;> rcases q with j | j <;>
      simp only [single_inl, single_inr, blk_inl, blk_inr, inlL_apply, inrL_apply,
        Sum.elim_comp_inl, Sum.elim_comp_inr, map_zero, Pi.zero_apply, Sum.elim_inl,
        Sum.elim_inr] at h ⊢ <;>
      first | exact M.isDP.W_E i r j h | exact N.isDP.W_E i r j h
  P0_F := by simp only [M.isDP.P0_F, N.isDP.P0_F, blk_one]
  P0_E := by simp only [M.isDP.P0_E, N.isDP.P0_E, blk_one]
  P1_F a b := by simp only [blk_comp, M.isDP.P1_F, N.isDP.P1_F, blk_smul]
  P1_E a b := by simp only [blk_comp, M.isDP.P1_E, N.isDP.P1_E, blk_smul]
  K p r s := by
    rcases p with i | i
    · rw [single_inl]
      simp only [← LinearMap.comp_apply (blk _ _) inlL, blk_comp_inlL, LinearMap.comp_apply,
        M.isDP.K i r s, map_sum, map_smul, Sum.elim_inl]
    · rw [single_inr]
      simp only [← LinearMap.comp_apply (blk _ _) inrL, blk_comp_inrL, LinearMap.comp_apply,
        N.isDP.K i r s, map_sum, map_smul, Sum.elim_inr]

/-- Part S: the direct sum `M ⊕ N` of two DP-lattices: basis `M.ι ⊕ N.ι`, weights
`Sum.elim M.wt N.wt`, `F^{(r)}`, `E^{(r)}` acting blockwise. That it is a DP-lattice is (S1). -/
def dsum : DPLattice A where
  ι := M.ι ⊕ N.ι
  wt := Sum.elim M.wt N.wt
  Fd r := blk (M.Fd r) (N.Fd r)
  Ed r := blk (M.Ed r) (N.Ed r)
  isDP := dsum_isDP M N

/-- (S1) the blockwise action of `F^{(r)}` on `M ⊕ N`. -/
theorem dsum_Fd (r : ℕ) (x : M.ι ⊕ N.ι → A) :
    (dsum M N).Fd r x ∘ Sum.inl = M.Fd r (x ∘ Sum.inl) ∧
    (dsum M N).Fd r x ∘ Sum.inr = N.Fd r (x ∘ Sum.inr) := ⟨rfl, rfl⟩

/-- (S1) the blockwise action of `E^{(r)}` on `M ⊕ N`. -/
theorem dsum_Ed (r : ℕ) (x : M.ι ⊕ N.ι → A) :
    (dsum M N).Ed r x ∘ Sum.inl = M.Ed r (x ∘ Sum.inl) ∧
    (dsum M N).Ed r x ∘ Sum.inr = N.Ed r (x ∘ Sum.inr) := ⟨rfl, rfl⟩

/-- (S1) The data of `M ⊕ N` (basis `M.ι ⊕ N.ι`, weights `Sum.elim M.wt N.wt`, blockwise
`F^{(r)}`, `E^{(r)}`) satisfy `IsDP`: (W), (P0), (P1), (K). -/
theorem S1 : IsDP (Sum.elim M.wt N.wt) (fun r => blk (M.Fd r) (N.Fd r))
    (fun r => blk (M.Ed r) (N.Ed r)) := dsum_isDP M N

lemma H_dsum : H (dsum M N) = blk (H M) (H N) := (blk_Hop M.wt N.wt).symm

/-- (S2) the inclusion `M → M ⊕ N`, `x ↦ Sum.elim x 0`. -/
def inlHom : Hom M (dsum M N) where
  toLin := inlL
  comm_F r := (blk_comp_inlL _ _).symm
  comm_E r := (blk_comp_inlL _ _).symm
  comm_H := by rw [H_dsum, blk_comp_inlL]

/-- (S2) the inclusion `N → M ⊕ N`, `y ↦ Sum.elim 0 y`. -/
def inrHom : Hom N (dsum M N) where
  toLin := inrL
  comm_F r := (blk_comp_inrL _ _).symm
  comm_E r := (blk_comp_inrL _ _).symm
  comm_H := by rw [H_dsum, blk_comp_inrL]

/-- (S2) the projection `M ⊕ N → M`, `z ↦ z ∘ inl`. -/
def fstHom : Hom (dsum M N) M where
  toLin := fstL
  comm_F r := rfl
  comm_E r := rfl
  comm_H := by rw [H_dsum]; rfl

/-- (S2) the projection `M ⊕ N → N`, `z ↦ z ∘ inr`. -/
def sndHom : Hom (dsum M N) N where
  toLin := sndL
  comm_F r := rfl
  comm_E r := rfl
  comm_H := by rw [H_dsum]; rfl

variable {M N} {M' N' M'' N'' : DPLattice A}

/-- (S2) the blockwise morphism `f ⊕ g : M ⊕ N → M' ⊕ N'`. -/
def dsumHom (f : Hom M M') (g : Hom N N') : Hom (dsum M N) (dsum M' N') where
  toLin := blk f.toLin g.toLin
  comm_F r := by
    change blk _ _ ∘ₗ blk _ _ = blk _ _ ∘ₗ blk _ _
    rw [blk_comp, blk_comp, f.comm_F, g.comm_F]
  comm_E r := by
    change blk _ _ ∘ₗ blk _ _ = blk _ _ ∘ₗ blk _ _
    rw [blk_comp, blk_comp, f.comm_E, g.comm_E]
  comm_H := by
    rw [H_dsum, H_dsum, blk_comp, blk_comp, f.comm_H, g.comm_H]

/-- (S2) `Hom.id ⊕ Hom.id = Hom.id`. -/
theorem dsumHom_id : dsumHom (Hom.id M) (Hom.id N) = Hom.id (dsum M N) :=
  Hom.ext' blk_id

/-- (S2) `(f ∘ f') ⊕ (g ∘ g') = (f ⊕ g) ∘ (f' ⊕ g')`. -/
theorem dsumHom_comp (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M') (g' : Hom N N') :
    dsumHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (dsumHom f g) (dsumHom f' g') :=
  Hom.ext' (blk_comp _ _ _ _).symm

/-- (S2) The inclusions and projections are `Hom`s (with the stated underlying maps); `f ⊕ g` is
a `Hom` acting blockwise; `⊕` preserves identities and composites. -/
theorem S2 (M N : DPLattice A) :
    (∃ i : Hom M (dsum M N), ∀ x, i.toLin x = Sum.elim x (0 : N.ι → A)) ∧
    (∃ i : Hom N (dsum M N), ∀ y, i.toLin y = Sum.elim (0 : M.ι → A) y) ∧
    (∃ p : Hom (dsum M N) M, ∀ z, p.toLin z = z ∘ Sum.inl) ∧
    (∃ p : Hom (dsum M N) N, ∀ z, p.toLin z = z ∘ Sum.inr) ∧
    (∀ {M' N' : DPLattice A} (f : Hom M M') (g : Hom N N') (z : M.ι ⊕ N.ι → A),
      (dsumHom f g).toLin z ∘ Sum.inl = f.toLin (z ∘ Sum.inl) ∧
      (dsumHom f g).toLin z ∘ Sum.inr = g.toLin (z ∘ Sum.inr)) ∧
    dsumHom (Hom.id M) (Hom.id N) = Hom.id (dsum M N) ∧
    (∀ {M' N' M'' N'' : DPLattice A} (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M')
      (g' : Hom N N'),
      dsumHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (dsumHom f g) (dsumHom f' g')) :=
  ⟨⟨inlHom M N, fun _ => rfl⟩, ⟨inrHom M N, fun _ => rfl⟩, ⟨fstHom M N, fun _ => rfl⟩,
    ⟨sndHom M N, fun _ => rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩, dsumHom_id,
    fun f g f' g' => dsumHom_comp f g f' g'⟩

end dsum

end Lemma35
