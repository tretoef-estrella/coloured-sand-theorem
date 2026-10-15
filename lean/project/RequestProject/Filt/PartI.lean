module

public import RequestProject.Filt.Sub

/-!
# `C29_filtrations_and_dance_lattices.md`: Part I — invariance under isomorphism

Encodings (namespace `Filt`):

* An isomorphism is C20's `Doubling.Iso X Y` (morphisms `e.hom`, `e.inv` with both composites
  the identities); "weight-preserving" is C25's `IsWtPres` on the underlying linear maps.
* `HasDeltaFilt`, `HasNablaFilt` are C27's inductive predicates.
* Auxiliary tools for Parts E and V: `Hom.liftInj` (a linear map `a` with `i ∘ a = h` for
  morphisms `h` and `i`, `i` injective, is a morphism), `Hom.descSurj` (a linear map `a` with
  `a ∘ q = h` for morphisms `h` and `q`, `q` surjective, is a morphism), `ShortExact.isoComp`
  (composing a short exact sequence with an isomorphism in the middle), and the facts that over
  the zero ring every DP-lattice has both filtrations.
-/

@[expose] public section

noncomputable section

namespace Filt

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

variable {A : Type*} [CommRing A]

/-! ### Auxiliary: lifting and descending morphisms -/

section aux

variable {X Y Z : DPLattice A}

/-- (auxiliary) intertwining through an injective map. -/
lemma intertwine_of_inj {a : Lin X Y} {i : Lin Y Z} {h : Lin X Z} (hi : Function.Injective i)
    (hia : i ∘ₗ a = h) {TX : Module.End A (X.ι → A)} {TY : Module.End A (Y.ι → A)}
    {TZ : Module.End A (Z.ι → A)} (hh : h ∘ₗ TX = TZ ∘ₗ h) (hi' : i ∘ₗ TY = TZ ∘ₗ i) :
    a ∘ₗ TX = TY ∘ₗ a := by
  refine LinearMap.ext fun x => hi ?_
  have e1 := LinearMap.congr_fun hh x
  have e2 := LinearMap.congr_fun hi' (a x)
  have e3 : ∀ y, i (a y) = h y := fun y => LinearMap.congr_fun hia y
  simp only [LinearMap.comp_apply] at e1 e2 ⊢
  rw [e3, e1, e2, e3]

/-- (auxiliary) a linear map `a : X → Y` with `i ∘ a = h`, where `h : Hom X Z` and `i : Hom Y Z`
with `i` injective, is a morphism. -/
def Hom.liftInj (a : Lin X Y) (i : Hom Y Z) (hi : Function.Injective i.toLin) (h : Hom X Z)
    (hia : i.toLin ∘ₗ a = h.toLin) : Hom X Y where
  toLin := a
  comm_F r := intertwine_of_inj hi hia (h.comm_F r) (i.comm_F r)
  comm_E r := intertwine_of_inj hi hia (h.comm_E r) (i.comm_E r)
  comm_H := intertwine_of_inj hi hia h.comm_H i.comm_H

/-- (auxiliary) intertwining through a surjective map. -/
lemma intertwine_of_surj {a : Lin Y Z} {q : Lin X Y} {h : Lin X Z} (hq : Function.Surjective q)
    (haq : a ∘ₗ q = h) {TX : Module.End A (X.ι → A)} {TY : Module.End A (Y.ι → A)}
    {TZ : Module.End A (Z.ι → A)} (hh : h ∘ₗ TX = TZ ∘ₗ h) (hq' : q ∘ₗ TX = TY ∘ₗ q) :
    a ∘ₗ TY = TZ ∘ₗ a := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hq y
  have e1 := LinearMap.congr_fun hh x
  have e2 := LinearMap.congr_fun hq' x
  have e3 : ∀ y, a (q y) = h y := fun y => LinearMap.congr_fun haq y
  simp only [LinearMap.comp_apply] at e1 e2 ⊢
  rw [← e2, e3, e1, e3]

/-- (auxiliary) a linear map `a : Y → Z` with `a ∘ q = h`, where `h : Hom X Z` and `q : Hom X Y`
with `q` surjective, is a morphism. -/
def Hom.descSurj (a : Lin Y Z) (q : Hom X Y) (hq : Function.Surjective q.toLin) (h : Hom X Z)
    (haq : a ∘ₗ q.toLin = h.toLin) : Hom Y Z where
  toLin := a
  comm_F r := intertwine_of_surj hq haq (h.comm_F r) (q.comm_F r)
  comm_E r := intertwine_of_surj hq haq (h.comm_E r) (q.comm_E r)
  comm_H := intertwine_of_surj hq haq h.comm_H q.comm_H

lemma Iso.inv_hom_apply (e : Iso X Y) (x : X.ι → A) : e.inv.toLin (e.hom.toLin x) = x :=
  LinearMap.congr_fun (congrArg Hom.toLin e.hom_inv) x

lemma Iso.hom_inv_apply (e : Iso X Y) (y : Y.ι → A) : e.hom.toLin (e.inv.toLin y) = y :=
  LinearMap.congr_fun (congrArg Hom.toLin e.inv_hom) y

/-- (auxiliary) composing a short exact sequence `M' → X → Q` with an isomorphism `X ≅ Y` gives a
short exact sequence `M' → Y → Q`. -/
lemma ShortExact.isoComp {M' Q : DPLattice A} {f : Hom M' X} {g : Hom X Q} (h : ShortExact f g)
    (e : Iso X Y) : ShortExact (Hom.comp e.hom f) (Hom.comp g e.inv) where
  inj x y hxy := h.inj (by
    have := congrArg e.inv.toLin hxy
    simpa only [Hom.comp, LinearMap.comp_apply, Iso.inv_hom_apply] using this)
  surj z := by
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨e.hom.toLin x, by simp only [Hom.comp, LinearMap.comp_apply, Iso.inv_hom_apply]⟩
  exact := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.mem_ker, Hom.comp, LinearMap.comp_apply]
    rw [← LinearMap.mem_ker, ← h.exact, LinearMap.mem_range]
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, by rw [Iso.inv_hom_apply]⟩
    · rintro ⟨u, hu⟩; exact ⟨u, by rw [hu, Iso.hom_inv_apply]⟩

/-- (auxiliary) the zero morphism. -/
def zeroHom (M N : DPLattice A) : Hom M N where
  toLin := 0
  comm_F _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_E _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_H := by rw [LinearMap.zero_comp, LinearMap.comp_zero]

/-- (auxiliary) over the zero ring every DP-lattice has a `Δ`-filtration. -/
lemma hasDeltaFilt_of_subsingleton [Subsingleton A] (M : DPLattice A) : HasDeltaFilt M :=
  HasDeltaFilt.step (l := 0) (zeroHom (zeroL A) M) (zeroHom M (delta A 0))
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩ isWtPres_zero isWtPres_zero (HasDeltaFilt.base inferInstance)

/-- (auxiliary) over the zero ring every DP-lattice has a `∇`-filtration. -/
lemma hasNablaFilt_of_subsingleton [Subsingleton A] (N : DPLattice A) : HasNablaFilt N :=
  HasNablaFilt.step (m := 0) (zeroHom (nabla A 0) N) (zeroHom N (zeroL A))
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩ isWtPres_zero isWtPres_zero (HasNablaFilt.base inferInstance)

/-- (auxiliary) over a nontrivial ring, a lattice isomorphic to an empty one is empty. -/
lemma isEmpty_of_iso [Nontrivial A] (e : Iso X Y) (hX : IsEmpty X.ι) : IsEmpty Y.ι := by
  refine ⟨fun i => ?_⟩
  have h1 : e.inv.toLin (Pi.single i (1 : A)) = 0 := Subsingleton.elim _ _
  have h2 := Iso.hom_inv_apply e (Pi.single i (1 : A))
  rw [h1, map_zero] at h2
  have := congrFun h2 i
  simp at this

end aux

/-! ### (I1) -/

variable {X Y : DPLattice A}

/-- (I1) If `e : Iso X Y` with `e.hom.toLin` and `e.inv.toLin` weight-preserving, then
`HasDeltaFilt X → HasDeltaFilt Y`. -/
theorem I1_delta (e : Iso X Y) (he : IsWtPres e.hom.toLin) (he' : IsWtPres e.inv.toLin)
    (hX : HasDeltaFilt X) : HasDeltaFilt Y := by
  cases hX with
  | base h =>
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact hasDeltaFilt_of_subsingleton Y
    · exact HasDeltaFilt.base (isEmpty_of_iso e h)
  | step f g hfg hf hg hM' =>
    exact HasDeltaFilt.step (Hom.comp e.hom f) (Hom.comp g e.inv) (ShortExact.isoComp hfg e)
      (isWtPres_comp he hf) (isWtPres_comp hg he') hM'

/-- (I1) If `e : Iso X Y` with `e.hom.toLin` and `e.inv.toLin` weight-preserving, then
`HasNablaFilt X → HasNablaFilt Y`. -/
theorem I1_nabla (e : Iso X Y) (he : IsWtPres e.hom.toLin) (he' : IsWtPres e.inv.toLin)
    (hX : HasNablaFilt X) : HasNablaFilt Y := by
  cases hX with
  | base h =>
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact hasNablaFilt_of_subsingleton Y
    · exact HasNablaFilt.base (isEmpty_of_iso e h)
  | step f g hfg hf hg hN' =>
    exact HasNablaFilt.step (Hom.comp e.hom f) (Hom.comp g e.inv) (ShortExact.isoComp hfg e)
      (isWtPres_comp he hf) (isWtPres_comp hg he') hN'

/-- (I1) **Invariance under isomorphism.** If `e : Iso X Y` with `e.hom.toLin` and
`e.inv.toLin` weight-preserving, then `HasDeltaFilt X → HasDeltaFilt Y` and
`HasNablaFilt X → HasNablaFilt Y`. -/
theorem I1 (e : Iso X Y) (he : IsWtPres e.hom.toLin) (he' : IsWtPres e.inv.toLin) :
    (HasDeltaFilt X → HasDeltaFilt Y) ∧ (HasNablaFilt X → HasNablaFilt Y) :=
  ⟨I1_delta e he he', I1_nabla e he he'⟩

/-! ### (I2) -/

/-- (I2, auxiliary) any linear map between two lattices all of whose weights are `0` is
weight-preserving. -/
lemma isWtPres_of_wt_zero {M N : DPLattice A} (hM : ∀ i, M.wt i = 0) (hN : ∀ j, N.wt j = 0)
    (φ : Lin M N) : IsWtPres φ := fun i j h => absurd (by rw [hM, hN]) h

lemma delta_zero_wt (i : (delta A 0).ι) : (delta A 0).wt i = 0 := by
  fin_cases i; simp [delta, weylWt]

lemma nabla_zero_wt (i : (nabla A 0).ι) : (nabla A 0).wt i = 0 := by
  fin_cases i; simp [nabla, weylWt]

/-- (I2) `HasDeltaFilt (one A)` (from `delta A 0` by `T5_delta_zero`). -/
theorem I2_delta_one : HasDeltaFilt (one A) :=
  I1_delta (Iso.ofDataEquiv _ T5_delta_zero) (isWtPres_of_wt_zero delta_zero_wt (fun _ => rfl) _)
    (isWtPres_of_wt_zero (fun _ => rfl) delta_zero_wt _) (F2_delta 0)

/-- (I2) `HasNablaFilt (one A)` (from `nabla A 0` by `T5_nabla_zero`). -/
theorem I2_nabla_one : HasNablaFilt (one A) :=
  I1_nabla (Iso.ofDataEquiv _ T5_nabla_zero) (isWtPres_of_wt_zero nabla_zero_wt (fun _ => rfl) _)
    (isWtPres_of_wt_zero (fun _ => rfl) nabla_zero_wt _) (F2_nabla 0)

/-- (I2) `HasDeltaFilt (V A)` (`delta A 1 = V A`, `T5_delta_one`). -/
theorem I2_delta_V : HasDeltaFilt (V A) := T5_delta_one (A := A) ▸ F2_delta 1

/-- (I2) `HasNablaFilt (V A)` (`nabla A 1 = V A`, `T5_nabla_one`). -/
theorem I2_nabla_V : HasNablaFilt (V A) := T5_nabla_one (A := A) ▸ F2_nabla 1

/-- (I2) `HasDeltaFilt (one A)`, `HasNablaFilt (one A)`, `HasDeltaFilt (V A)`,
`HasNablaFilt (V A)`. -/
theorem I2 : HasDeltaFilt (one A) ∧ HasNablaFilt (one A) ∧ HasDeltaFilt (V A) ∧
    HasNablaFilt (V A) :=
  ⟨I2_delta_one, I2_nabla_one, I2_delta_V, I2_nabla_V⟩

end Filt
