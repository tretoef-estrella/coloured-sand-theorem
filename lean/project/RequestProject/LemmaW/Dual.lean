module

public import RequestProject.LemmaW.Basic
public import RequestProject.Doubling.Functor

/-!
# `C25_lemma_W_and_ext.md`: Part D — the contravariant dual

Encodings (namespace `LemmaW`):

* `dual M` (D1) has basis `M.ι` (the same type), weights `M.wt`, `F^{(r)} := trM (M.Ed r)` and
  `E^{(r)} := trM (M.Fd r)`. Its condition (K) is C18's `IsDP.dual` (the transpose of a DP-lattice
  with `F` and `E` exchanged), C18's `tr` being definitionally our `trM`.
* `dualHom f : Hom (dual N) (dual M)` (D2) has underlying map `trM f.toLin`.
* Isomorphisms are C20's `Doubling.Iso` (`hom`, `inv` with both composites the identity, C19's
  `Hom.comp`, `Hom.id`); their underlying linear maps are `u.hom.toLin`, `u.inv.toLin`. In
  (D3), (D4) both underlying maps are `LinearMap.id` (the bases are the same type).
* The abstract splitting lemma `exists_retraction_of_section` (for arbitrary modules, used in
  (D5) and (E1)): if `N —f→ X —g→ Z` is exact with `f` injective and `σ` is a linear section of
  `g`, there is a linear `ρ` with `ρ ∘ f = id` and `f ∘ ρ = id − σ ∘ g`.
-/

@[expose] public section

noncomputable section

namespace LemmaW

open DPLattice WeylFilt Doubling Finset

variable {A : Type*} [CommRing A]

/-! ### Abstract splitting -/

/-- (D5), (E1), auxiliary: for an exact sequence `N —f→ X —g→ Z` of modules with `f` injective
and a linear section `σ` of `g`, there is a linear retraction `ρ` of `f` with
`f ∘ ρ = id − σ ∘ g`. -/
lemma exists_retraction_of_section {N X Z : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup X] [Module A X] [AddCommGroup Z] [Module A Z]
    (f : N →ₗ[A] X) (g : X →ₗ[A] Z) (hinj : Function.Injective f)
    (hex : LinearMap.range f = LinearMap.ker g) (σ : Z →ₗ[A] X) (hσ : g ∘ₗ σ = LinearMap.id) :
    ∃ ρ : X →ₗ[A] N, ρ ∘ₗ f = LinearMap.id ∧ f ∘ₗ ρ = LinearMap.id - σ ∘ₗ g := by
  let e := LinearEquiv.ofInjective f hinj
  let p : X →ₗ[A] X := LinearMap.id - σ ∘ₗ g
  have hmem : ∀ y, p y ∈ LinearMap.range f := by
    intro y
    rw [hex, LinearMap.mem_ker]
    have := LinearMap.congr_fun hσ (g y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [p, this]
  let q := LinearMap.codRestrict (LinearMap.range f) p hmem
  have hfe : ∀ v, f (e.symm v) = v := by
    intro v
    have := LinearEquiv.ofInjective_apply f (h := hinj) (e.symm v)
    rw [← this]; simp [e]
  have h2 : f ∘ₗ (e.symm.toLinearMap ∘ₗ q) = LinearMap.id - σ ∘ₗ g := by
    ext y : 1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hfe]
    rfl
  refine ⟨e.symm.toLinearMap ∘ₗ q, ?_, h2⟩
  ext n : 1
  apply hinj
  have := LinearMap.congr_fun h2 (f n)
  rw [LinearMap.comp_apply] at this
  rw [LinearMap.comp_apply, this]
  have hgf : g (f n) = 0 := by
    rw [← LinearMap.mem_ker, ← hex]; exact ⟨n, rfl⟩
  simp [hgf]

/-- (D5), (E1), auxiliary: a surjective linear map onto a finite free module `κ → A` has a
linear section. -/
lemma exists_section {X : Type*} [AddCommGroup X] [Module A X] {κ : Type*} [Fintype κ]
    (g : X →ₗ[A] (κ → A)) (hg : Function.Surjective g) :
    ∃ σ : (κ → A) →ₗ[A] X, g ∘ₗ σ = LinearMap.id :=
  Module.projective_lifting_property g LinearMap.id hg

/-! ### (D1) -/

/-- (D1) The contravariant dual of a DP-lattice: basis `M.ι`, weights `M.wt`,
`F^{(r)} := trM (M.Ed r)`, `E^{(r)} := trM (M.Fd r)`. Its conditions (W), (P0), (P1), (K) are
C18's `IsDP.dual`. -/
def dual (M : DPLattice A) : DPLattice A where
  ι := M.ι
  wt := M.wt
  Fd r := trM (M.Ed r)
  Ed r := trM (M.Fd r)
  isDP := M.isDP.dual

/-- (D1) `dual M` satisfies `IsDP` ((W), (P0), (P1), (K)); on basis vectors
`(dual M).Fd r (δ_i) j = M.Ed r (δ_j) i` and `(dual M).Ed r (δ_i) j = M.Fd r (δ_j) i`. -/
theorem D1 (M : DPLattice A) :
    (dual M).ι = M.ι ∧ (∀ i, (dual M).wt i = M.wt i) ∧
    (∀ r, (dual M).Fd r = trM (M.Ed r)) ∧ (∀ r, (dual M).Ed r = trM (M.Fd r)) ∧
    IsDP (dual M).wt (dual M).Fd (dual M).Ed ∧
    (∀ (r : ℕ) (i j : M.ι), (dual M).Fd r (Pi.single i 1) j = M.Ed r (Pi.single j 1) i) ∧
    (∀ (r : ℕ) (i j : M.ι), (dual M).Ed r (Pi.single i 1) j = M.Fd r (Pi.single j 1) i) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, (dual M).isDP,
    fun r i j => trM_single_apply (M.Ed r) i j, fun r i j => trM_single_apply (M.Fd r) i j⟩

/-! ### (D2) -/

/-- (D2) The dual of a morphism `f : Hom M N`: `dualHom f : Hom (dual N) (dual M)` with
underlying map `trM f.toLin`. -/
def dualHom {M N : DPLattice A} (f : Hom M N) : Hom (dual N) (dual M) where
  toLin := trM f.toLin
  comm_F r := by
    change trM f.toLin ∘ₗ trM (N.Ed r) = trM (M.Ed r) ∘ₗ trM f.toLin
    rw [← trM_comp, ← trM_comp, f.comm_E]
  comm_E r := by
    change trM f.toLin ∘ₗ trM (N.Fd r) = trM (M.Fd r) ∘ₗ trM f.toLin
    rw [← trM_comp, ← trM_comp, f.comm_F]
  comm_H := by
    change trM f.toLin ∘ₗ Hop N.wt = Hop M.wt ∘ₗ trM f.toLin
    rw [← trM_Hop N.wt, ← trM_Hop M.wt, ← trM_comp, ← trM_comp]
    exact congrArg trM f.comm_H.symm

@[simp] lemma dualHom_toLin {M N : DPLattice A} (f : Hom M N) :
    (dualHom f).toLin = trM f.toLin := rfl

/-- (D2) `dualHom (Hom.id M) = Hom.id (dual M)`. -/
theorem dualHom_id (M : DPLattice A) : dualHom (Hom.id M) = Hom.id (dual M) :=
  Hom.ext' (trM_id (A := A) (ι := M.ι))

/-- (D2) `dualHom (Hom.comp g f) = Hom.comp (dualHom f) (dualHom g)`. -/
theorem dualHom_comp {M N P : DPLattice A} (g : Hom N P) (f : Hom M N) :
    dualHom (Hom.comp g f) = Hom.comp (dualHom f) (dualHom g) :=
  Hom.ext' (trM_comp g.toLin f.toLin)

/-- (D2) If `f.toLin` is weight-preserving, so is `trM f.toLin`. -/
theorem dualHom_wtPres {M N : DPLattice A} {f : Hom M N} (hf : IsWtPres f.toLin) :
    IsWtPres (dualHom f).toLin := by
  intro j i hji
  change trM f.toLin (Pi.single j 1) i = 0
  rw [trM_single_apply]
  exact hf i j (fun h => hji h.symm)

/-- (D2) The statements of (D2) together. -/
theorem D2 :
    (∀ {M N : DPLattice A} (f : Hom M N), (dualHom f).toLin = trM f.toLin) ∧
    (∀ M : DPLattice A, dualHom (Hom.id M) = Hom.id (dual M)) ∧
    (∀ {M N P : DPLattice A} (g : Hom N P) (f : Hom M N),
      dualHom (Hom.comp g f) = Hom.comp (dualHom f) (dualHom g)) ∧
    (∀ {M N : DPLattice A} (f : Hom M N), IsWtPres f.toLin → IsWtPres (trM f.toLin)) :=
  ⟨fun _ => rfl, dualHom_id, dualHom_comp, fun _ hf => dualHom_wtPres hf⟩

/-! ### (D3) -/

/-- (D3, auxiliary) the identity map `dual (dual M) → M` as a morphism. -/
def dualDualHom (M : DPLattice A) : Hom (dual (dual M)) M where
  toLin := LinearMap.id
  comm_F r := by
    change LinearMap.id ∘ₗ trM (trM (M.Fd r)) = M.Fd r ∘ₗ LinearMap.id
    rw [trM_trM]; rfl
  comm_E r := by
    change LinearMap.id ∘ₗ trM (trM (M.Ed r)) = M.Ed r ∘ₗ LinearMap.id
    rw [trM_trM]; rfl
  comm_H := rfl

/-- (D3) `dual (dual M) ≅ M`, with both underlying linear maps the identity of `M.ι → A`. -/
def isoDualDual (M : DPLattice A) : Iso (dual (dual M)) M :=
  Iso.ofInverse (dualDualHom M) LinearMap.id rfl rfl

/-- (D3) `dual (dual M) ≅ M`: the isomorphism `isoDualDual M` has both underlying linear maps
equal to the identity of `M.ι → A`. -/
theorem D3 (M : DPLattice A) :
    (isoDualDual M).hom.toLin = (LinearMap.id : (M.ι → A) →ₗ[A] (M.ι → A)) ∧
    (isoDualDual M).inv.toLin = (LinearMap.id : (M.ι → A) →ₗ[A] (M.ι → A)) :=
  ⟨rfl, rfl⟩

/-! ### (D4) -/

/-- (D4) `dual (delta A l)` and `nabla A l` have the same basis `Fin (l + 1)`, the same weights
and the same operators. -/
theorem D4_delta (l : ℕ) :
    (dual (delta A l)).ι = Fin (l + 1) ∧ (nabla A l).ι = Fin (l + 1) ∧
    (∀ i, (dual (delta A l)).wt i = (nabla A l).wt i) ∧
    (∀ r, (dual (delta A l)).Fd r = (nabla A l).Fd r) ∧
    (∀ r, (dual (delta A l)).Ed r = (nabla A l).Ed r) := by
  refine ⟨rfl, rfl, fun _ => rfl, fun r => ?_, fun r => ?_⟩
  · change trM (deltaE l r) = nablaF l r
    rw [deltaE_eq, tr_eq_trM, trM_trM]
  · change trM (deltaF l r) = nablaE l r
    rw [deltaF_eq, tr_eq_trM, trM_trM]

/-- (D4) `dual (nabla A l)` and `delta A l` have the same basis `Fin (l + 1)`, the same weights
and the same operators. -/
theorem D4_nabla (l : ℕ) :
    (dual (nabla A l)).ι = Fin (l + 1) ∧ (delta A l).ι = Fin (l + 1) ∧
    (∀ i, (dual (nabla A l)).wt i = (delta A l).wt i) ∧
    (∀ r, (dual (nabla A l)).Fd r = (delta A l).Fd r) ∧
    (∀ r, (dual (nabla A l)).Ed r = (delta A l).Ed r) := by
  refine ⟨rfl, rfl, fun _ => rfl, fun r => ?_, fun r => ?_⟩
  · change trM (nablaE l r) = deltaF l r
    rw [deltaF_eq, tr_eq_trM]
  · change trM (nablaF l r) = deltaE l r
    rw [deltaE_eq, tr_eq_trM]

/-- (D4, auxiliary) the identity `dual (delta A l) → nabla A l` as a morphism. -/
def dualDeltaHom (l : ℕ) : Hom (dual (delta A l)) (nabla A l) where
  toLin := LinearMap.id
  comm_F r := by rw [(D4_delta l).2.2.2.1 r]; rfl
  comm_E r := by rw [(D4_delta l).2.2.2.2 r]; rfl
  comm_H := rfl

/-- (D4, auxiliary) the identity `dual (nabla A l) → delta A l` as a morphism. -/
def dualNablaHom (l : ℕ) : Hom (dual (nabla A l)) (delta A l) where
  toLin := LinearMap.id
  comm_F r := by rw [(D4_nabla l).2.2.2.1 r]; rfl
  comm_E r := by rw [(D4_nabla l).2.2.2.2 r]; rfl
  comm_H := rfl

/-- (D4) `dual (delta A l) ≅ nabla A l`, with both underlying maps the identity. -/
def isoDualDelta (l : ℕ) : Iso (dual (delta A l)) (nabla A l) :=
  Iso.ofInverse (dualDeltaHom l) LinearMap.id rfl rfl

/-- (D4) `dual (nabla A l) ≅ delta A l`, with both underlying maps the identity. -/
def isoDualNabla (l : ℕ) : Iso (dual (nabla A l)) (delta A l) :=
  Iso.ofInverse (dualNablaHom l) LinearMap.id rfl rfl

/-- (D4) The isomorphisms `dual (delta A l) ≅ nabla A l` and `dual (nabla A l) ≅ delta A l`
have both underlying linear maps equal to the identity of `Fin (l + 1) → A`. -/
theorem D4 (l : ℕ) :
    (isoDualDelta (A := A) l).hom.toLin = (LinearMap.id : (Fin (l + 1) → A) →ₗ[A] _) ∧
    (isoDualDelta (A := A) l).inv.toLin = (LinearMap.id : (Fin (l + 1) → A) →ₗ[A] _) ∧
    (isoDualNabla (A := A) l).hom.toLin = (LinearMap.id : (Fin (l + 1) → A) →ₗ[A] _) ∧
    (isoDualNabla (A := A) l).inv.toLin = (LinearMap.id : (Fin (l + 1) → A) →ₗ[A] _) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### (D5) -/

/-- (D5) Over any commutative ring: if `f : Hom N X`, `g : Hom X Z` is short exact, then
`dualHom g : Hom (dual Z) (dual X)`, `dualHom f : Hom (dual X) (dual N)` is short exact. -/
theorem D5 {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (h : ShortExact f g) :
    ShortExact (dualHom g) (dualHom f) := by
  obtain ⟨σ, hσ⟩ := exists_section g.toLin h.surj
  obtain ⟨ρ, hρf, hfρ⟩ := exists_retraction_of_section f.toLin g.toLin h.inj h.exact σ hσ
  have hgf : g.toLin ∘ₗ f.toLin = 0 := by
    refine LinearMap.ext fun n => ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, ← h.exact]
    exact ⟨n, rfl⟩
  -- transposed identities
  have t1 : trM σ ∘ₗ trM g.toLin = LinearMap.id := by
    rw [← trM_comp, hσ, trM_id]
  have t2 : trM f.toLin ∘ₗ trM ρ = LinearMap.id := by
    rw [← trM_comp, hρf, trM_id]
  have t3 : trM f.toLin ∘ₗ trM g.toLin = 0 := by
    rw [← trM_comp, hgf, trM_zero]
  have t4 : trM ρ ∘ₗ trM f.toLin + trM g.toLin ∘ₗ trM σ = LinearMap.id := by
    rw [← trM_comp, ← trM_comp, ← trM_add, hfρ, sub_add_cancel, trM_id]
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    change trM g.toLin u = trM g.toLin v at huv
    have h1 := LinearMap.congr_fun t1 u
    have h2 := LinearMap.congr_fun t1 v
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, huv]
  · intro u
    refine ⟨trM ρ u, ?_⟩
    change (trM f.toLin ∘ₗ trM ρ) u = u
    rw [t2]; rfl
  · apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      change (trM f.toLin ∘ₗ trM g.toLin) u = 0
      rw [t3]; rfl
    · intro u hu
      rw [LinearMap.mem_ker] at hu
      refine ⟨trM σ u, ?_⟩
      have := LinearMap.congr_fun t4 u
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
      change trM f.toLin u = 0 at hu
      rw [hu, map_zero, zero_add] at this
      exact this

end LemmaW
