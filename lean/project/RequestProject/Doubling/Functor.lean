module

public import RequestProject.Doubling.PartAB

/-!
# `C20_the_doubling_functor.md`: Part A (A2), (A3) — `Φ` on morphisms

Encodings:
* `phiLin f` is `1 ⊗ f` on `Φ(N) = N²`: `phiLin f (b_e n) = b_e (f n)` (`phiLin_bvec`), i.e. it
  applies `f` slot by slot.
* `phiHom f : Hom (phi N) (phi M)` is `Φ(f)` for `f : Hom N M`.
* `Iso M N` ("`M ≅ N`", used in Part D): morphisms both ways whose composites (C19's
  `Hom.comp`) are the identities (C19's `Hom.id`).
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset Polynomial WeylFilt

variable {A : Type*} [CommRing A]

/-! ### `1 ⊗ f` on slot vectors -/

section lin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- (A2) `1 ⊗ f`: apply `f` in each slot, `(1 ⊗ f)(b_e n) = b_e f(n)`. -/
def phiLin (f : (ι → A) →ₗ[A] (κ → A)) : (Fin 2 × ι → A) →ₗ[A] (Fin 2 × κ → A) :=
  bvec 0 ∘ₗ f ∘ₗ slice 0 + bvec 1 ∘ₗ f ∘ₗ slice 1

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma phiLin_bvec (f : (ι → A) →ₗ[A] (κ → A)) (e : Fin 2) (n : ι → A) :
    phiLin f (bvec e n) = bvec e (f n) := by
  rcases fin_two_cases e with rfl | rfl <;> simp [phiLin]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma slice_phiLin (f : (ι → A) →ₗ[A] (κ → A)) (e : Fin 2) (x : Fin 2 × ι → A) :
    slice e (phiLin f x) = f (slice e x) := by
  rcases fin_two_cases e with rfl | rfl <;> simp [phiLin]

lemma phiLin_id : phiLin (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) = LinearMap.id := by
  refine ext_single fun p => ?_
  obtain ⟨e, i⟩ := p
  rw [single_eq_bvec, phiLin_bvec]; rfl

omit [Fintype κ] [DecidableEq κ] in
lemma phiLin_comp {ν : Type*} [Fintype ν] [DecidableEq ν] (g : (κ → A) →ₗ[A] (ν → A))
    (f : (ι → A) →ₗ[A] (κ → A)) : phiLin (g ∘ₗ f) = phiLin g ∘ₗ phiLin f := by
  refine ext_single fun p => ?_
  obtain ⟨e, i⟩ := p
  rw [single_eq_bvec, LinearMap.comp_apply, phiLin_bvec, phiLin_bvec, phiLin_bvec]; rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma phiLin_injective {f : (ι → A) →ₗ[A] (κ → A)} (hf : Function.Injective f) :
    Function.Injective (phiLin f) := by
  intro x y hxy
  apply ext_slice
  · apply hf; rw [← slice_phiLin, hxy, slice_phiLin]
  · apply hf; rw [← slice_phiLin, hxy, slice_phiLin]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma phiLin_surjective {f : (ι → A) →ₗ[A] (κ → A)} (hf : Function.Surjective f) :
    Function.Surjective (phiLin f) := by
  intro z
  obtain ⟨x0, hx0⟩ := hf (slice 0 z)
  obtain ⟨x1, hx1⟩ := hf (slice 1 z)
  refine ⟨bvec 0 x0 + bvec 1 x1, ?_⟩
  rw [map_add, phiLin_bvec, phiLin_bvec, hx0, hx1]
  exact (eq_bvec_slice z).symm

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma phiLin_exact {ν : Type*} {f : (ι → A) →ₗ[A] (κ → A)} {g : (κ → A) →ₗ[A] (ν → A)}
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (phiLin f) = LinearMap.ker (phiLin g) := by
  have hgf : ∀ y, g (f y) = 0 := fun y => by
    have : f y ∈ LinearMap.ker g := h ▸ LinearMap.mem_range_self _ y
    simpa using this
  ext y
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    apply ext_slice <;> simp [hgf]
  · intro hy
    have h0 : slice 0 y ∈ LinearMap.range f := by
      rw [h, LinearMap.mem_ker, ← slice_phiLin, hy]; rfl
    have h1 : slice 1 y ∈ LinearMap.range f := by
      rw [h, LinearMap.mem_ker, ← slice_phiLin, hy]; rfl
    obtain ⟨x0, hx0⟩ := h0
    obtain ⟨x1, hx1⟩ := h1
    refine ⟨bvec 0 x0 + bvec 1 x1, ?_⟩
    rw [map_add, phiLin_bvec, phiLin_bvec, hx0, hx1]
    exact (eq_bvec_slice y).symm

end lin

/-! ### Morphisms preserve weights -/

lemma hom_inWt [IsDomain A] [CharZero A] {N M : DPLattice A} (f : Hom N M) {w : ℤ}
    {x : N.ι → A} (hx : InWt N.wt w x) : InWt M.wt w (f.toLin x) := by
  intro j hj
  have h := congr_fun (LinearMap.congr_fun f.comm_H x) j
  simp only [LinearMap.comp_apply] at h
  rw [Hop_of_inWt hx, map_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul, Hop_apply] at h
  have h' : (((M.wt j - w : ℤ)) : A) * f.toLin x j = 0 := by push_cast; linear_combination -h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (by exact_mod_cast h0) (sub_ne_zero.mpr hj)
  · exact h0

lemma hom_aeval {N M : DPLattice A} (f : Hom N M) (p : A[X]) (x : N.ι → A) :
    f.toLin (aeval (N.Fd 1 * N.Ed 1) p x) = aeval (M.Fd 1 * M.Ed 1) p (f.toLin x) := by
  have hT : ∀ y, f.toLin ((N.Fd 1 * N.Ed 1) y) = (M.Fd 1 * M.Ed 1) (f.toLin y) := fun y => by
    simp only [Module.End.mul_apply]
    rw [← LinearMap.comp_apply f.toLin, f.comm_F, LinearMap.comp_apply,
      ← LinearMap.comp_apply f.toLin, f.comm_E, LinearMap.comp_apply]
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    have e2 : ∀ T : Module.End A (N.ι → A), aeval T (C a * X ^ (n + 1)) =
        aeval T (C a * X ^ n) * T := fun T => by rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    have e2' : ∀ T : Module.End A (M.ι → A), aeval T (C a * X ^ (n + 1)) =
        aeval T (C a * X ^ n) * T := fun T => by rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [e2, e2', Module.End.mul_apply, ih, hT]; rfl

lemma hom_piOp {N M : DPLattice A} (f : Hom N M) (S : Finset ℕ) (c : ℕ → ℤ) (x : N.ι → A) :
    f.toLin (piOp N S c x) = piOp M S c (f.toLin x) := hom_aeval f _ x

lemma hom_F {N M : DPLattice A} (f : Hom N M) (r : ℕ) (x : N.ι → A) :
    f.toLin (N.Fd r x) = M.Fd r (f.toLin x) := LinearMap.congr_fun (f.comm_F r) x

lemma hom_E {N M : DPLattice A} (f : Hom N M) (r : ℕ) (x : N.ι → A) :
    f.toLin (N.Ed r x) = M.Ed r (f.toLin x) := LinearMap.congr_fun (f.comm_E r) x

/-! ### `Φ(f)` -/

lemma phiLin_phiFdL {N M : DPLattice A} (f : Hom N M) (r : ℕ) (e : Fin 2) (n : N.ι → A) :
    phiLin f.toLin (phiFdL N r e n) = phiFdL M r e (f.toLin n) := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [phiFdL_even, phiFdL_even, map_smul, phiLin_bvec, hom_F]
  · rcases fin_two_cases e with rfl | rfl
    · rw [phiFdL_odd0, phiFdL_odd0, map_smul, phiLin_bvec, hom_F]
    · rw [phiFdL_odd1, phiFdL_odd1, map_smul, phiLin_bvec, hom_F]

lemma phiLin_phiEdL {N M : DPLattice A} (f : Hom N M) (r : ℕ) (e : Fin 2) (w : ℤ)
    (n : N.ι → A) : phiLin f.toLin (phiEdL N r e w n) = phiEdL M r e w (f.toLin n) := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rcases fin_two_cases e with rfl | rfl
    · rw [phiEdL_even0, phiEdL_even0, map_smul, phiLin_bvec, hom_piOp, hom_E]
    · rw [phiEdL_even1, phiEdL_even1, map_smul, phiLin_bvec, hom_piOp, hom_E]
  · rcases fin_two_cases e with rfl | rfl
    · rw [phiEdL_odd0, phiEdL_odd0, map_smul, phiLin_bvec, hom_piOp, hom_E]
    · rw [phiEdL_odd1, phiEdL_odd1, map_smul, phiLin_bvec, hom_piOp, hom_E]

section functor

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (A2) `Φ(f) := 1 ⊗ f` is a morphism `Hom (phi N) (phi M)`: it commutes with every `F^{(r)}`,
every `E^{(s)}` and `H` of `Φ`. -/
def phiHom {N M : DPLattice A} (f : Hom N M) : Hom (phi N) (phi M) where
  toLin := phiLin f.toLin
  comm_F r := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    show phiLin f.toLin (phiFd N r (Pi.single (e, i) 1)) =
      phiFd M r (phiLin f.toLin (Pi.single (e, i) 1))
    rw [single_eq_bvec, phiLin_bvec, phiFd_bvec, phiFd_bvec, phiLin_phiFdL]
  comm_E r := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    show phiLin f.toLin (phiEd N r (Pi.single (e, i) 1)) =
      phiEd M r (phiLin f.toLin (Pi.single (e, i) 1))
    have hδ := inWt_single (A := A) N.wt i
    rw [single_eq_bvec, phiLin_bvec, phiEd_bvec_of_inWt N r e hδ,
      phiEd_bvec_of_inWt M r e (hom_inWt f hδ), phiLin_phiEdL]
  comm_H := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    have hδ := inWt_single (A := A) N.wt i
    show phiLin f.toLin (Hop (phiWt N) (Pi.single (e, i) 1)) =
      Hop (phiWt M) (phiLin f.toLin (Pi.single (e, i) 1))
    rw [single_eq_bvec, phiLin_bvec, Hop_of_inWt (inWt_bvec N e hδ),
      Hop_of_inWt (inWt_bvec M e (hom_inWt f hδ)), map_smul, phiLin_bvec]

@[simp] lemma phiHom_toLin {N M : DPLattice A} (f : Hom N M) :
    (phiHom f).toLin = phiLin f.toLin := rfl

/-- (A2) `Φ(f)` is a morphism, with `Φ(f)(b_e n) = b_e f(n)`; `Φ(Hom.id N) = Hom.id (phi N)`;
`Φ(g ∘ f) = Φ(g) ∘ Φ(f)`. -/
theorem A2 :
    (∀ {N M : DPLattice A} (f : Hom N M) (e : Fin 2) (n : N.ι → A),
      (phiHom f).toLin (bvec e n) = bvec e (f.toLin n)) ∧
    (∀ N : DPLattice A, phiHom (Hom.id N) = Hom.id (phi N)) ∧
    (∀ {N M P : DPLattice A} (g : Hom M P) (f : Hom N M),
      phiHom (Hom.comp g f) = Hom.comp (phiHom g) (phiHom f)) := by
  refine ⟨fun f e n => phiLin_bvec _ e n, fun N => Hom.ext' phiLin_id, fun g f => Hom.ext' ?_⟩
  exact phiLin_comp g.toLin f.toLin

/-- (A3) `Φ` is exact: if `X —f→ Y —g→ Z` is short exact, so is `Φ(X) —Φ(f)→ Φ(Y) —Φ(g)→ Φ(Z)`. -/
theorem A3 {X Y Z : DPLattice A} {f : Hom X Y} {g : Hom Y Z} (h : ShortExact f g) :
    ShortExact (phiHom f) (phiHom g) where
  inj := phiLin_injective h.inj
  surj := phiLin_surjective h.surj
  exact := phiLin_exact h.exact

end functor

/-! ### Isomorphisms -/

/-- (D1), (D2), (D3): an isomorphism `M ≅ N` of DP-lattices: morphisms both ways whose
composites are the identities. -/
structure Iso (M N : DPLattice A) where
  /-- the morphism `M → N` -/
  hom : Hom M N
  /-- the morphism `N → M` -/
  inv : Hom N M
  hom_inv : Hom.comp inv hom = Hom.id M
  inv_hom : Hom.comp hom inv = Hom.id N

/-- The inverse of a bijective morphism (given by a two-sided inverse linear map) is a morphism. -/
def Hom.ofInverse {M N : DPLattice A} (f : Hom M N) (g : (N.ι → A) →ₗ[A] (M.ι → A))
    (hgf : g ∘ₗ f.toLin = LinearMap.id) (hfg : f.toLin ∘ₗ g = LinearMap.id) : Hom N M where
  toLin := g
  comm_F r := by
    calc g ∘ₗ N.Fd r = g ∘ₗ N.Fd r ∘ₗ (f.toLin ∘ₗ g) := by rw [hfg]; rfl
      _ = g ∘ₗ (f.toLin ∘ₗ M.Fd r) ∘ₗ g := by rw [f.comm_F]; rfl
      _ = (g ∘ₗ f.toLin) ∘ₗ M.Fd r ∘ₗ g := rfl
      _ = M.Fd r ∘ₗ g := by rw [hgf]; rfl
  comm_E r := by
    calc g ∘ₗ N.Ed r = g ∘ₗ N.Ed r ∘ₗ (f.toLin ∘ₗ g) := by rw [hfg]; rfl
      _ = g ∘ₗ (f.toLin ∘ₗ M.Ed r) ∘ₗ g := by rw [f.comm_E]; rfl
      _ = (g ∘ₗ f.toLin) ∘ₗ M.Ed r ∘ₗ g := rfl
      _ = M.Ed r ∘ₗ g := by rw [hgf]; rfl
  comm_H := by
    calc g ∘ₗ H N = g ∘ₗ H N ∘ₗ (f.toLin ∘ₗ g) := by rw [hfg]; rfl
      _ = g ∘ₗ (f.toLin ∘ₗ H M) ∘ₗ g := by rw [f.comm_H]; rfl
      _ = (g ∘ₗ f.toLin) ∘ₗ H M ∘ₗ g := rfl
      _ = H M ∘ₗ g := by rw [hgf]; rfl

/-- The isomorphism given by a morphism and a two-sided inverse linear map. -/
def Iso.ofInverse {M N : DPLattice A} (f : Hom M N) (g : (N.ι → A) →ₗ[A] (M.ι → A))
    (hgf : g ∘ₗ f.toLin = LinearMap.id) (hfg : f.toLin ∘ₗ g = LinearMap.id) : Iso M N where
  hom := f
  inv := Hom.ofInverse f g hgf hfg
  hom_inv := Hom.ext' hgf
  inv_hom := Hom.ext' hfg

/-- Composition of isomorphisms. -/
def Iso.trans {M N P : DPLattice A} (u : Iso M N) (v : Iso N P) : Iso M P where
  hom := Hom.comp v.hom u.hom
  inv := Hom.comp u.inv v.inv
  hom_inv := by
    apply Hom.ext'
    have h1 := congrArg Hom.toLin u.hom_inv
    have h2 := congrArg Hom.toLin v.hom_inv
    simp only [Hom.comp, Hom.id] at h1 h2 ⊢
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc u.hom.toLin, h2, LinearMap.id_comp, h1]
  inv_hom := by
    apply Hom.ext'
    have h1 := congrArg Hom.toLin u.inv_hom
    have h2 := congrArg Hom.toLin v.inv_hom
    simp only [Hom.comp, Hom.id] at h1 h2 ⊢
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc v.inv.toLin, h1, LinearMap.id_comp, h2]

/-- `Φ` sends isomorphisms to isomorphisms (by (A2)). -/
def Iso.phi [IsDomain A] [CharZero A] [OddUnits A] {M N : DPLattice A} (u : Iso M N) :
    Iso (phi M) (phi N) where
  hom := phiHom u.hom
  inv := phiHom u.inv
  hom_inv := by rw [← A2.2.2, u.hom_inv, A2.2.1]
  inv_hom := by rw [← A2.2.2, u.inv_hom, A2.2.1]

end Doubling
