module

public import RequestProject.Cocycle.PartG56

/-!
# `C27_cocycles_and_filtrations.md`: Part G — (G7) every extension is glued

Encodings (namespace `Cocycle`):

* For an extension `f : Hom N X`, `g : Hom X M`, a linear section `σ` of `g` and the linear
  retraction `ρ` of `f` with `f ∘ ρ = id − σ ∘ g`, the cocycle is
  `extCocycle X ρ σ = (r ↦ ρ ∘ X.Fd r ∘ σ, r ↦ ρ ∘ X.Ed r ∘ σ)`.
* `θ : Iso X (glue M N c hc)` (C20's `Doubling.Iso`), with underlying map
  `θ.hom.toLin x = (ρ x, g x) = Sum.elim (ρ x) (g x)` (`thetaL ρ g`) and inverse
  `θ.inv.toLin (u, v) = f u + σ v` (`thetaInvL f σ`).
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

variable {M N X : DPLattice A}

/-- (G7) the cocycle of an extension: `cF r = ρ ∘ X.Fd r ∘ σ`, `cE r = ρ ∘ X.Ed r ∘ σ`. -/
def extCocycle (X : DPLattice A) (ρ : Lin X N) (σ : Lin M X) : Pair M N :=
  (fun r => ρ ∘ₗ X.Fd r ∘ₗ σ, fun r => ρ ∘ₗ X.Ed r ∘ₗ σ)

@[simp] lemma extCocycle_fst (ρ : Lin X N) (σ : Lin M X) (r : ℕ) :
    (extCocycle X ρ σ).1 r = ρ ∘ₗ X.Fd r ∘ₗ σ := rfl

@[simp] lemma extCocycle_snd (ρ : Lin X N) (σ : Lin M X) (r : ℕ) :
    (extCocycle X ρ σ).2 r = ρ ∘ₗ X.Ed r ∘ₗ σ := rfl

/-- (G7) the linear map `x ↦ (ρ x, g x)`. -/
def thetaL (ρ : Lin X N) (g : Lin X M) : (X.ι → A) →ₗ[A] (N.ι ⊕ M.ι → A) where
  toFun x := Sum.elim (ρ x) (g x)
  map_add' x y := by simp
  map_smul' t x := by simp

@[simp] lemma thetaL_apply (ρ : Lin X N) (g : Lin X M) (x : X.ι → A) :
    thetaL ρ g x = Sum.elim (ρ x) (g x) := rfl

/-- (G7) the linear map `(u, v) ↦ f u + σ v`. -/
def thetaInvL (f : Lin N X) (σ : Lin M X) : (N.ι ⊕ M.ι → A) →ₗ[A] (X.ι → A) :=
  f ∘ₗ LinearMap.funLeft A A Sum.inl + σ ∘ₗ LinearMap.funLeft A A Sum.inr

@[simp] lemma thetaInvL_elim (f : Lin N X) (σ : Lin M X) (u : N.ι → A) (v : M.ι → A) :
    thetaInvL f σ (Sum.elim u v) = f u + σ v := rfl

/-- (G7, auxiliary) under `θ`, an operator of `X` becomes the glued block operator (upper-right
block `ρ ∘ T_X ∘ σ`, lower-left block `g ∘ T_X ∘ f = 0`). -/
lemma theta_comm {f : Lin N X} {g : Lin X M} {σ : Lin M X} {ρ : Lin X N}
    (hρf : ρ ∘ₗ f = LinearMap.id) (hfρ : f ∘ₗ ρ = LinearMap.id - σ ∘ₗ g)
    (TN : Module.End A (N.ι → A)) (TX : Module.End A (X.ι → A)) (TM : Module.End A (M.ι → A))
    (hf : f ∘ₗ TN = TX ∘ₗ f) (hg : g ∘ₗ TX = TM ∘ₗ g) :
    thetaL ρ g ∘ₗ TX = blk TN (ρ ∘ₗ TX ∘ₗ σ) TM ∘ₗ thetaL ρ g := by
  refine LinearMap.ext fun x => ?_
  have hx : x = f (ρ x) + σ (g x) := by
    have := LinearMap.congr_fun hfρ x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this]; abel
  have h1 : ρ (TX (f (ρ x))) = TN (ρ x) := by
    rw [← LinearMap.comp_apply TX f, ← hf, LinearMap.comp_apply, ← LinearMap.comp_apply ρ f,
      hρf, LinearMap.id_apply]
  simp only [LinearMap.comp_apply, thetaL_apply, blk_elim]
  rw [elim_eq_iff]
  refine ⟨?_, LinearMap.congr_fun hg x⟩
  conv_lhs => rw [hx]
  rw [map_add, map_add, h1]

/-- (G7) **Every extension is glued.** Let `f : Hom N X`, `g : Hom X M` be short exact with
`f.toLin`, `g.toLin` weight-preserving. Then there are a weight-preserving linear section `σ`
of `g`, the linear retraction `ρ` of `f` with `ρ ∘ f = id` and `f ∘ ρ = id − σ ∘ g` (also
weight-preserving), the cocycle `c = extCocycle X ρ σ` (`cF r = ρ ∘ X.Fd r ∘ σ`,
`cE r = ρ ∘ X.Ed r ∘ σ`) from `M` to `N`, and an isomorphism `θ : X ≅ glue M N c` with
underlying map `x ↦ (ρ x, g x)` and inverse `(u, v) ↦ f u + σ v`, such that `θ ∘ f = incl` and
`proj ∘ θ = g`. -/
theorem G7 {f : Hom N X} {g : Hom X M} (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) :
    ∃ (σ : Lin M X) (ρ : Lin X N), IsWtPres σ ∧ IsWtPres ρ ∧ g.toLin ∘ₗ σ = LinearMap.id ∧
      ρ ∘ₗ f.toLin = LinearMap.id ∧ f.toLin ∘ₗ ρ = LinearMap.id - σ ∘ₗ g.toLin ∧
      ∃ (hc : IsCocycle (extCocycle X ρ σ)) (θ : Iso X (glue M N (extCocycle X ρ σ) hc)),
        (∀ x, θ.hom.toLin x = Sum.elim (ρ x) (g.toLin x)) ∧
        (∀ u v, θ.inv.toLin (Sum.elim u v) = f.toLin u + σ v) ∧
        Hom.comp θ.hom f = incl M N _ hc ∧ Hom.comp (proj M N _ hc) θ.hom = g := by
  obtain ⟨σ, hσw, hσ⟩ := exists_wtPres_section h.surj hg
  obtain ⟨ρ, hρf, hfρ⟩ := exists_retraction_of_section f.toLin g.toLin h.inj h.exact σ hσ
  have hρw : IsWtPres ρ := isWtPres_retraction h.inj hf hg hσw hfρ
  have hgf : ∀ u, g.toLin (f.toLin u) = 0 := fun u => by
    rw [← LinearMap.mem_ker, ← h.exact]; exact ⟨u, rfl⟩
  have hgσ : ∀ v, g.toLin (σ v) = v := fun v => LinearMap.congr_fun hσ v
  have hρf' : ∀ u, ρ (f.toLin u) = u := fun u => LinearMap.congr_fun hρf u
  have hρσ : ∀ v, ρ (σ v) = 0 := fun v => by
    apply h.inj
    have := LinearMap.congr_fun hfρ (σ v)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hgσ,
      sub_self] at this
    rw [this, map_zero]
  have hF : ∀ r, thetaL ρ g.toLin ∘ₗ X.Fd r =
      blk (N.Fd r) ((extCocycle X ρ σ).1 r) (M.Fd r) ∘ₗ thetaL ρ g.toLin := fun r =>
    theta_comm hρf hfρ _ _ _ (f.comm_F r) (g.comm_F r)
  have hE : ∀ r, thetaL ρ g.toLin ∘ₗ X.Ed r =
      blk (N.Ed r) ((extCocycle X ρ σ).2 r) (M.Ed r) ∘ₗ thetaL ρ g.toLin := fun r =>
    theta_comm hρf hfρ _ _ _ (f.comm_E r) (g.comm_E r)
  have hc : IsCocycle (extCocycle X ρ σ) := by
    refine isDP_transport X (thetaL ρ g.toLin) ?_ hF hE ?_
    · intro i k hik
      cases k with
      | inl k => exact hρw i k hik
      | inr k => exact hg i k hik
    · intro k
      cases k with
      | inl k =>
        refine ⟨f.toLin (Pi.single k 1), inWt_map hf (inWt_single N.wt k), ?_⟩
        rw [thetaL_apply, hρf', hgf, single_inl]
      | inr k =>
        refine ⟨σ (Pi.single k 1), inWt_map hσw (inWt_single M.wt k), ?_⟩
        rw [thetaL_apply, hρσ, hgσ, single_inr]
  let θh : Hom X (glue M N (extCocycle X ρ σ) hc) :=
    { toLin := thetaL ρ g.toLin
      comm_F := hF
      comm_E := hE
      comm_H := LinearMap.ext fun x => by
        change Sum.elim (ρ (Hop X.wt x)) (g.toLin (Hop X.wt x)) =
          Hop (gwt M N) (Sum.elim (ρ x) (g.toLin x))
        rw [hop_elim, elim_eq_iff]
        exact ⟨LinearMap.congr_fun (comm_H_of_isWtPres hρw) x,
          LinearMap.congr_fun g.comm_H x⟩ }
  have h1 : thetaInvL f.toLin σ ∘ₗ θh.toLin = LinearMap.id := LinearMap.ext fun x => by
    change f.toLin (ρ x) + σ (g.toLin x) = x
    have := LinearMap.congr_fun hfρ x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this]; abel
  have h2 : θh.toLin ∘ₗ thetaInvL f.toLin σ = LinearMap.id := LinearMap.ext fun z => by
    rw [← elim_comp z]
    change thetaL ρ g.toLin (thetaInvL f.toLin σ (Sum.elim _ _)) = _
    rw [thetaInvL_elim, thetaL_apply, map_add, map_add, hρf', hρσ, hgf, hgσ, add_zero,
      zero_add]
    rfl
  refine ⟨σ, ρ, hσw, hρw, hσ, hρf, hfρ, hc, Iso.ofInverse θh (thetaInvL f.toLin σ) h1 h2,
    fun x => rfl, fun u v => rfl, ?_, ?_⟩
  · refine Hom.ext' (LinearMap.ext fun u => ?_)
    change Sum.elim (ρ (f.toLin u)) (g.toLin (f.toLin u)) = Sum.elim u 0
    rw [hρf', hgf]
  · exact Hom.ext' (LinearMap.ext fun x => rfl)

/-- (G7), consequence: if every cocycle from `M` to `N` is a coboundary, every short exact
sequence `f : Hom N X`, `g : Hom X M` with weight-preserving underlying maps splits: `g` has a
section and `f` a retraction in `Hom`. -/
theorem G7_split (hall : ∀ c : Pair M N, IsCocycle c → IsCoboundary c) {f : Hom N X}
    {g : Hom X M} (h : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) :
    (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N) := by
  obtain ⟨σ, ρ, -, -, -, -, -, hc, θ, -, -, -, hproj⟩ := G7 h hf hg
  obtain ⟨s0, hs0⟩ := ((G5 _ hc).1).mp (hall _ hc)
  have hs : Hom.comp g (Hom.comp θ.inv s0) = Hom.id M := by
    apply Hom.ext'
    have e1 := congrArg Hom.toLin hproj
    have e2 := congrArg Hom.toLin θ.inv_hom
    have e3 := congrArg Hom.toLin hs0
    simp only [Hom.comp, Hom.id] at e1 e2 e3 ⊢
    rw [← e1, LinearMap.comp_assoc, ← LinearMap.comp_assoc s0.toLin θ.inv.toLin θ.hom.toLin,
      e2, LinearMap.id_comp, e3]
  exact ⟨⟨_, hs⟩, (E1 h).mp ⟨_, hs⟩⟩

end Cocycle
