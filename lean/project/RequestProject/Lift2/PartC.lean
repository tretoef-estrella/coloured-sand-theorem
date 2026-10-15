module

public import RequestProject.Lift2.PartL

/-!
# `C28_lifting_mod_2_and_corollary_34.md`: Part C (Corollary 3.4)

Encodings (namespace `Lift2`): as in `Lift2/Basic.lean`. An endomorphism of `ι → A` is
`u : Module.End A (ι → A)`; "`u` is invertible" is `IsUnit u` (in the ring `Module.End`),
equivalently `Function.Bijective u`. An isomorphism of DP-lattices is `e : Iso X Y` (C20),
with underlying maps `e.hom.toLin` and `e.inv.toLin`.
-/

@[expose] public section

noncomputable section

namespace Lift2

open DPLattice WeylFilt Doubling Twist LemmaW Cocycle Finset

variable {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}

/-- (C1), auxiliary: `det (1 + 2 • W) = 1 + 2 * c` for some `c` (reduce modulo the ideal `2A`). -/
lemma det_one_add_two_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι A) :
    ∃ c : A, (1 + (2 : A) • W).det = 1 + 2 * c := by
  let π := Ideal.Quotient.mk (Ideal.span {(2 : A)})
  have h2 : π 2 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self 2)
  have hmap : (1 + (2 : A) • W).map π = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [h2]
    · simp [hij, h2]
  have : π ((1 + (2 : A) • W).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp this)
  exact ⟨c, by rw [mul_comm, hc]; ring⟩

/-- (C1) If every `1 + 2a` (`a : A`) is a unit of `A`, then for every finite type `ι` and every
`u : Module.End A (ι → A)` of the form `u = 1 + 2 • w`, `u` is a unit, equivalently
bijective (its determinant is `1 + 2c`). Uses only the hypothesis `OneAddTwoUnit A`. -/
theorem C1 (hU : OneAddTwoUnit A) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u w : Module.End A (ι → A)) (huw : u = 1 + (2 : A) • w) :
    IsUnit u ∧ Function.Bijective u := by
  have hu : IsUnit u := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    obtain ⟨c, hc⟩ := det_one_add_two_smul (LinearMap.toMatrix' w)
    have : u = Matrix.toLin' (1 + (2 : A) • LinearMap.toMatrix' w) := by
      rw [map_add, map_smul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, huw]; rfl
    rw [this, LinearMap.det_toLin', hc]
    exact hU c
  exact ⟨hu, (Module.End.isUnit_iff u).mp hu⟩

/-- (C2) Under (H2) and the hypothesis of (C1): if `u : Module.End A (ι → A)` and
`bc φ u = 1`, then `u` is bijective. (Hypothesis (H3) of the file is not needed: only the
existence of `w` with `u − 1 = 2 • w` is used; this is a more general statement.) -/
theorem C2 (h2 : H2 φ) (hU : OneAddTwoUnit A) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Module.End A (ι → A)) (hu : bc φ u = 1) : Function.Bijective u := by
  obtain ⟨w, hw⟩ := D1_exists h2 (u - 1) (by rw [bc_sub, hu, bc_one, sub_self])
  exact (C1 hU u w (by rw [← hw, add_sub_cancel])).2

/-- (C3), auxiliary: the inverse of a bijective weight-preserving map is weight-preserving. -/
lemma isWtPres_inverse {M N : DPLattice A} {f : Lin M N} {g : Lin N M} (hf : IsWtPres f)
    (hgf : g ∘ₗ f = LinearMap.id) (hfg : f ∘ₗ g = LinearMap.id) : IsWtPres g := by
  rw [isWtPres_iff] at hf ⊢
  intro w
  calc g ∘ₗ pr N w = g ∘ₗ pr N w ∘ₗ (f ∘ₗ g) := by rw [hfg]; rfl
    _ = g ∘ₗ (f ∘ₗ pr M w) ∘ₗ g := by rw [hf w]; rfl
    _ = (g ∘ₗ f) ∘ₗ pr M w ∘ₗ g := rfl
    _ = pr M w ∘ₗ g := by rw [hgf]; rfl

/-- (C3) **Corollary 3.4.** Under (H1), (H2), (H3) and the hypothesis of (C1): let `X`, `Y`
be DP-lattices over `A` with `HasDeltaFilt X`, `HasNablaFilt X`, `HasDeltaFilt Y`,
`HasNablaFilt Y`, and `ē : Iso (baseChange φ X) (baseChange φ Y)` with `ē.hom.toLin`,
`ē.inv.toLin` weight-preserving. Then there is `e : Iso X Y` with `e.hom.toLin`, `e.inv.toLin`
weight-preserving, `bc φ e.hom.toLin = ē.hom.toLin` and `bc φ e.inv.toLin = ē.inv.toLin`.
Uses (H1), (H2), (H3) (through (L2)) and `OneAddTwoUnit A` (through (C2)). -/
theorem C3 (h1 : H1 φ) (h2 : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) {X Y : DPLattice A}
    (hXD : HasDeltaFilt X) (hXN : HasNablaFilt X) (hYD : HasDeltaFilt Y)
    (hYN : HasNablaFilt Y) (eb : Iso (baseChange φ X) (baseChange φ Y))
    (hhom : IsWtPres eb.hom.toLin) (hinv : IsWtPres eb.inv.toLin) :
    ∃ e : Iso X Y, IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
      bc φ e.hom.toLin = eb.hom.toLin ∧ bc φ e.inv.toLin = eb.inv.toLin := by
  obtain ⟨f, hfw, hf, -⟩ := L2 h1 h2 h3 hXD hYN eb.hom hhom
  obtain ⟨g, -, hg, -⟩ := L2 h1 h2 h3 hYD hXN eb.inv hinv
  have hgf_b : bc φ (g.toLin ∘ₗ f.toLin) = 1 := by
    rw [bc_comp, hf, hg]; exact congrArg Hom.toLin eb.hom_inv
  have hfg_b : bc φ (f.toLin ∘ₗ g.toLin) = 1 := by
    rw [bc_comp, hf, hg]; exact congrArg Hom.toLin eb.inv_hom
  have hgf := C2 h2 hU _ hgf_b
  have hfg := C2 h2 hU _ hfg_b
  have hfbij : Function.Bijective f.toLin :=
    ⟨fun a b hab => hgf.1 (by simp only [LinearMap.comp_apply, hab]),
     fun y => by obtain ⟨x, hx⟩ := hfg.2 y; exact ⟨g.toLin x, hx⟩⟩
  let fe := LinearEquiv.ofBijective f.toLin hfbij
  let finv : Lin Y X := fe.symm.toLinearMap
  have h_inv_f : finv ∘ₗ f.toLin = LinearMap.id :=
    LinearMap.ext fun x => fe.symm_apply_apply x
  have h_f_inv : f.toLin ∘ₗ finv = LinearMap.id :=
    LinearMap.ext fun y => fe.apply_symm_apply y
  refine ⟨Iso.ofInverse f finv h_inv_f h_f_inv, hfw, isWtPres_inverse hfw h_inv_f h_f_inv, hf, ?_⟩
  show bc φ finv = eb.inv.toLin
  have hid : bc φ f.toLin ∘ₗ eb.inv.toLin = LinearMap.id := by
    rw [hf]; exact congrArg Hom.toLin eb.inv_hom
  calc bc φ finv = bc φ finv ∘ₗ (bc φ f.toLin ∘ₗ eb.inv.toLin) := by rw [hid]; rfl
    _ = bc φ (finv ∘ₗ f.toLin) ∘ₗ eb.inv.toLin := by rw [bc_comp]; rfl
    _ = eb.inv.toLin := by rw [h_inv_f, bc_id]; rfl

end Lift2
