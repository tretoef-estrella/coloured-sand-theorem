module

public import RequestProject.OddTwist.PartAB

/-!
# `CSI1_the_odd_twist.md`: Part A (A2), (A3) — `Φ_p` on morphisms

Encodings:
* `twistLin p f` is `1 ⊗ f` on `Φ_p(N) = N^p`: it applies `f` slot by slot,
  `twistLin p f (b_j n) = b_j (f n)` (`twistLin_bv`).
* `twistHom p f : Hom (twist p N) (twist p M)` is `Φ_p(f)` for `f : Hom N M`.
* Isomorphisms are C20's `Doubling.Iso`; `Iso.twist` is `Φ_p` applied to an isomorphism.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Polynomial WeylFilt

open scoped Nat

/-! ### `1 ⊗ f` on slot vectors -/

section lin

variable {A : Type*} [CommRing A] (p : ℕ) {ι κ : Type*}

/-- (A2) `1 ⊗ f`: apply `f` in each slot, `(1 ⊗ f)(b_j n) = b_j f(n)`. -/
def twistLin (f : (ι → A) →ₗ[A] (κ → A)) : (Fin p × ι → A) →ₗ[A] (Fin p × κ → A) where
  toFun x y := f (sl p y.1 x) y.2
  map_add' x x' := by funext y; simp [map_add]
  map_smul' c x := by funext y; simp [map_smul]

@[simp] lemma sl_twistLin (f : (ι → A) →ₗ[A] (κ → A)) (j : Fin p) (x : Fin p × ι → A) :
    sl p j (twistLin p f x) = f (sl p j x) := rfl

@[simp] lemma twistLin_bv (f : (ι → A) →ₗ[A] (κ → A)) (k : ℕ) (n : ι → A) :
    twistLin p f (bv p k n) = bv p k (f n) := by
  funext ⟨j, i⟩
  show f (sl p j (bv p k n)) i = _
  rw [sl_bv]
  by_cases h : (j : ℕ) = k <;> simp [h]

lemma ext_sl {f g : Fin p × ι → A} (h : ∀ j, sl p j f = sl p j g) : f = g := by
  funext ⟨j, i⟩; exact congr_fun (h j) i

lemma twistLin_id [Fintype ι] [DecidableEq ι] :
    twistLin p (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) = LinearMap.id := by
  refine ext_single fun x => ?_
  obtain ⟨j, i⟩ := x
  rw [single_eq_bv, twistLin_bv]; rfl

lemma twistLin_comp [Fintype ι] [DecidableEq ι] {ν : Type*} (g : (κ → A) →ₗ[A] (ν → A))
    (f : (ι → A) →ₗ[A] (κ → A)) : twistLin p (g ∘ₗ f) = twistLin p g ∘ₗ twistLin p f := by
  refine ext_single fun x => ?_
  obtain ⟨j, i⟩ := x
  rw [single_eq_bv, LinearMap.comp_apply, twistLin_bv, twistLin_bv, twistLin_bv]; rfl

lemma twistLin_injective {f : (ι → A) →ₗ[A] (κ → A)} (hf : Function.Injective f) :
    Function.Injective (twistLin p f) := by
  intro x y hxy
  refine ext_sl p fun j => hf ?_
  rw [← sl_twistLin, hxy, sl_twistLin]

lemma twistLin_surjective [Fintype κ] {f : (ι → A) →ₗ[A] (κ → A)}
    (hf : Function.Surjective f) : Function.Surjective (twistLin p f) := by
  intro z
  choose x hx using fun j : Fin p => hf (sl p j z)
  refine ⟨∑ j : Fin p, bv p j (x j), ?_⟩
  rw [map_sum]
  simp only [twistLin_bv, hx]
  exact (eq_sum_bv p z).symm

lemma twistLin_exact [Fintype κ] {ν : Type*} {f : (ι → A) →ₗ[A] (κ → A)}
    {g : (κ → A) →ₗ[A] (ν → A)} (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (twistLin p f) = LinearMap.ker (twistLin p g) := by
  have hgf : ∀ y, g (f y) = 0 := fun y => by
    have : f y ∈ LinearMap.ker g := h ▸ LinearMap.mem_range_self _ y
    simpa using this
  ext y
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    refine ext_sl p fun j => ?_
    rw [sl_twistLin, sl_twistLin, hgf]; rfl
  · intro hy
    have hj : ∀ j : Fin p, sl p j y ∈ LinearMap.range f := fun j => by
      rw [h, LinearMap.mem_ker, ← sl_twistLin, hy]; rfl
    choose x hx using hj
    refine ⟨∑ j : Fin p, bv p j (x j), ?_⟩
    rw [map_sum]
    simp only [twistLin_bv, hx]
    exact (eq_sum_bv p y).symm

end lin

/-! ### `Φ_p(f)` -/

variable (p : ℕ) [Fact p.Prime]

lemma hom_PP {N M : DPLattice ℤ_[p]} (f : Hom N M) (w : ℤ) (S : Finset (ℕ × ℕ))
    (x : N.ι → ℤ_[p]) : f.toLin (PP p N w S x) = PP p M w S (f.toLin x) :=
  Doubling.hom_aeval f _ x

lemma twistLin_twFdL {N M : DPLattice ℤ_[p]} (f : Hom N M) (r j : ℕ) (n : N.ι → ℤ_[p]) :
    twistLin p f.toLin (twFdL p N r j n) = twFdL p M r j (f.toLin n) := by
  simp only [twFdL, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, twistLin_bv,
    Doubling.hom_F]

lemma twistLin_twEdL {N M : DPLattice ℤ_[p]} (f : Hom N M) (r j : ℕ) (w : ℤ)
    (n : N.ι → ℤ_[p]) : twistLin p f.toLin (twEdL p N r j w n) = twEdL p M r j w (f.toLin n) := by
  simp only [twEdL, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, twistLin_bv,
    Doubling.hom_E, hom_PP]

/-- (A2) `Φ_p(f) := 1 ⊗ f` is a morphism `Hom (twist p N) (twist p M)`: it commutes with every
`F^{(r)}`, every `E^{(s)}` and `H` of `Φ_p`. -/
def twistHom {N M : DPLattice ℤ_[p]} (f : Hom N M) : Hom (twist p N) (twist p M) where
  toLin := twistLin p f.toLin
  comm_F r := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    show twistLin p f.toLin (twFd p N r (Pi.single (j, i) 1)) =
      twFd p M r (twistLin p f.toLin (Pi.single (j, i) 1))
    rw [single_eq_bv, twistLin_bv, twFd_bv p N r j.isLt, twFd_bv p M r j.isLt, twistLin_twFdL]
  comm_E r := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    show twistLin p f.toLin (twEd p N r (Pi.single (j, i) 1)) =
      twEd p M r (twistLin p f.toLin (Pi.single (j, i) 1))
    have hδ := inWt_single (A := ℤ_[p]) N.wt i
    rw [single_eq_bv, twistLin_bv, twEd_bv p N r j.isLt hδ,
      twEd_bv p M r j.isLt (Doubling.hom_inWt f hδ), twistLin_twEdL]
  comm_H := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    have hδ := inWt_single (A := ℤ_[p]) N.wt i
    show twistLin p f.toLin (Hop (twWt p N) (Pi.single (j, i) 1)) =
      Hop (twWt p M) (twistLin p f.toLin (Pi.single (j, i) 1))
    rw [single_eq_bv, twistLin_bv, Doubling.Hop_of_inWt (inWt_tw p N j hδ),
      Doubling.Hop_of_inWt (inWt_tw p M j (Doubling.hom_inWt f hδ)), map_smul, twistLin_bv]

@[simp] lemma twistHom_toLin {N M : DPLattice ℤ_[p]} (f : Hom N M) :
    (twistHom p f).toLin = twistLin p f.toLin := rfl

/-- (A2) `Φ_p(f)` is a morphism, with `Φ_p(f)(b_j n) = b_j f(n)`;
`Φ_p(Hom.id N) = Hom.id (twist p N)`; `Φ_p(g ∘ f) = Φ_p(g) ∘ Φ_p(f)`. -/
theorem A2 :
    (∀ {N M : DPLattice ℤ_[p]} (f : Hom N M) (j : ℕ) (n : N.ι → ℤ_[p]),
      (twistHom p f).toLin (bv p j n) = bv p j (f.toLin n)) ∧
    (∀ N : DPLattice ℤ_[p], twistHom p (Hom.id N) = Hom.id (twist p N)) ∧
    (∀ {N M P : DPLattice ℤ_[p]} (g : Hom M P) (f : Hom N M),
      twistHom p (Hom.comp g f) = Hom.comp (twistHom p g) (twistHom p f)) := by
  refine ⟨fun f j n => twistLin_bv p _ j n, fun N => Hom.ext' (twistLin_id p),
    fun g f => Hom.ext' ?_⟩
  exact twistLin_comp p g.toLin f.toLin

/-- (A3) `Φ_p` is exact: if `X —f→ Y —g→ Z` is short exact (C19's `ShortExact`), so is
`Φ_p(X) —Φ_p(f)→ Φ_p(Y) —Φ_p(g)→ Φ_p(Z)`. -/
theorem A3 {X Y Z : DPLattice ℤ_[p]} {f : Hom X Y} {g : Hom Y Z} (h : ShortExact f g) :
    ShortExact (twistHom p f) (twistHom p g) where
  inj := twistLin_injective p h.inj
  surj := twistLin_surjective p h.surj
  exact := twistLin_exact p h.exact

/-- `Φ_p` sends isomorphisms (C20's `Doubling.Iso`) to isomorphisms (by (A2)). -/
def Iso.twist {M N : DPLattice ℤ_[p]} (u : Doubling.Iso M N) :
    Doubling.Iso (twist p M) (twist p N) where
  hom := twistHom p u.hom
  inv := twistHom p u.inv
  hom_inv := by rw [← (A2 p).2.2, u.hom_inv, (A2 p).2.1]
  inv_hom := by rw [← (A2 p).2.2, u.inv_hom, (A2 p).2.1]

end ColouredSand.OddTwist
