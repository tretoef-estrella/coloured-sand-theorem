module

public import RequestProject.OddSplitting.All
public import RequestProject.OddSplit.All
public import RequestProject.Step36.All

/-!
# `CSI6_the_dance_lattices.md`, Part A — additivity of `Φ_p = twist p` and `Ψ_r = psi p · r`

Namespace `ColouredSand.OddTwist`. Reuses C18 `DPLattice`, C19 `WeylFilt.Hom.id/comp/ext'`,
C20 `Doubling.Iso` (`Iso.ofInverse`, `Iso.trans`, `Iso.symm`), C22 `Lemma35.dsum` (with
`inlHom`, `inrHom`, `fstHom`, `sndHom`), C23 `Tensor2.dsumIso`, C24 `Iso.refl`, C27 `zeroL`,
C30 `Step36.dsumList`, `Step36.isoZeroOfIsEmpty`, CSI1 `twist`, `twistLin`, `twistHom`,
`Iso.twist`, CSI3 `psi`, `psiLin`, `psiHom`, `F2`, and CSI4 `pairHom`.

Encodings:
* «`X ≅ Y`» is `Nonempty (Doubling.Iso X Y)`; the explicit isomorphisms are `def`s.
* `psi p N r h1 h2` is CSI3's `Ψ_r(N)` (written `psi p r N` in the file), with
  `h1 : 1 ≤ r`, `h2 : r ≤ p − 1`.
* `isoDsumOfBiprod` is the recognition of a direct sum by a biproduct diagram
  `Y ⇄ X ⇄ Z` (`a ∘ c = id`, `b ∘ d = id`, `a ∘ d = 0`, `b ∘ c = 0`, `c ∘ a + d ∘ b = id`);
  (A1) applies the functors `Φ_p`, `Ψ_r` (which are additive on linear maps) to the biproduct
  diagram `N ⇄ N ⊕ N' ⇄ N'` of C22.
* For (A3), `List.map (twist p)` and `List.map (fun N => psi p N r h1 h2)` act on lists of
  lattices; `dsumList` is C30's finite direct sum.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice WeylFilt Lemma35

/-! ### Recognising a direct sum -/

section biprod

variable {A : Type*} [CommRing A] {X Y Z : DPLattice A}

/-- Part A (auxiliary): the linear map `(y, z) ↦ c y + d z` out of `Y ⊕ Z`. -/
def copairLin (c : Hom Y X) (d : Hom Z X) : (Y.ι ⊕ Z.ι → A) →ₗ[A] (X.ι → A) :=
  c.toLin ∘ₗ fstL + d.toLin ∘ₗ sndL

/-- Part A (auxiliary): a biproduct diagram `Y ⇄ X ⇄ Z` gives `X ≅ Y ⊕ Z`. -/
def isoDsumOfBiprod (a : Hom X Y) (b : Hom X Z) (c : Hom Y X) (d : Hom Z X)
    (hac : a.toLin ∘ₗ c.toLin = LinearMap.id) (hbd : b.toLin ∘ₗ d.toLin = LinearMap.id)
    (had : a.toLin ∘ₗ d.toLin = 0) (hbc : b.toLin ∘ₗ c.toLin = 0)
    (hsum : c.toLin ∘ₗ a.toLin + d.toLin ∘ₗ b.toLin = LinearMap.id) :
    Doubling.Iso X (dsum Y Z) :=
  Doubling.Iso.ofInverse (pairHom a b) (copairLin c d)
    (by
      refine LinearMap.ext fun x => ?_
      have := LinearMap.congr_fun hsum x
      simpa [copairLin] using this)
    (by
      refine LinearMap.ext fun z => funext fun s => ?_
      have h1 := fun y => LinearMap.congr_fun hac y
      have h2 := fun y => LinearMap.congr_fun hbd y
      have h3 := fun y => LinearMap.congr_fun had y
      have h4 := fun y => LinearMap.congr_fun hbc y
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2 h3 h4
      cases s with
      | inl i =>
        show a.toLin (c.toLin (z ∘ Sum.inl) + d.toLin (z ∘ Sum.inr)) i = z (Sum.inl i)
        rw [map_add, h1, h3, add_zero]; rfl
      | inr i =>
        show b.toLin (c.toLin (z ∘ Sum.inl) + d.toLin (z ∘ Sum.inr)) i = z (Sum.inr i)
        rw [map_add, h2, h4, zero_add]; rfl)

lemma fstL_comp_inlL {ι κ : Type*} :
    (fstL : (ι ⊕ κ → A) →ₗ[A] (ι → A)) ∘ₗ inlL = LinearMap.id := rfl

lemma sndL_comp_inrL {ι κ : Type*} :
    (sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A)) ∘ₗ inrL = LinearMap.id := rfl

lemma fstL_comp_inrL {ι κ : Type*} :
    (fstL : (ι ⊕ κ → A) →ₗ[A] (ι → A)) ∘ₗ inrL = 0 := rfl

lemma sndL_comp_inlL {ι κ : Type*} :
    (sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A)) ∘ₗ inlL = 0 := rfl

lemma inl_fst_add_inr_snd {ι κ : Type*} :
    (inlL : (ι → A) →ₗ[A] (ι ⊕ κ → A)) ∘ₗ fstL + inrL ∘ₗ sndL = LinearMap.id := by
  refine LinearMap.ext fun z => funext fun s => ?_
  cases s <;> simp

end biprod

/-! ### Additivity of `twistLin` and `psiLin` in the linear map -/

section lin

variable {A : Type*} [CommRing A] (p : ℕ) {ι κ : Type*}

lemma twistLin_add (f g : (ι → A) →ₗ[A] (κ → A)) :
    twistLin p (f + g) = twistLin p f + twistLin p g := rfl

lemma twistLin_zero : twistLin p (0 : (ι → A) →ₗ[A] (κ → A)) = 0 := rfl

lemma psiLin_add (f g : (ι → A) →ₗ[A] (κ → A)) :
    psiLin p (f + g) = psiLin p f + psiLin p g := rfl

lemma psiLin_zero : psiLin p (0 : (ι → A) →ₗ[A] (κ → A)) = 0 := rfl

end lin

variable (p : ℕ) [Fact p.Prime]

/-! ### (A1) -/

/-- **(A1)** (Part A of `CSI6_the_dance_lattices.md`), first half, explicit:
`Φ_p(N ⊕ N') ≅ Φ_p(N) ⊕ Φ_p(N')`, given by `(Φ_p(pr₁), Φ_p(pr₂))` with inverse
`Φ_p(in₁) + Φ_p(in₂)`. -/
def twistDsumIso (N N' : DPLattice ℤ_[p]) :
    Doubling.Iso (twist p (dsum N N')) (dsum (twist p N) (twist p N')) :=
  isoDsumOfBiprod (twistHom p (fstHom N N')) (twistHom p (sndHom N N'))
    (twistHom p (inlHom N N')) (twistHom p (inrHom N N'))
    (by
      show twistLin p fstL ∘ₗ twistLin p inlL = LinearMap.id
      rw [← twistLin_comp, fstL_comp_inlL, twistLin_id])
    (by
      show twistLin p sndL ∘ₗ twistLin p inrL = LinearMap.id
      rw [← twistLin_comp, sndL_comp_inrL, twistLin_id])
    (by
      show twistLin p fstL ∘ₗ twistLin p inrL = 0
      rw [← twistLin_comp, fstL_comp_inrL, twistLin_zero])
    (by
      show twistLin p sndL ∘ₗ twistLin p inlL = 0
      rw [← twistLin_comp, sndL_comp_inlL, twistLin_zero])
    (by
      show twistLin p inlL ∘ₗ twistLin p fstL + twistLin p inrL ∘ₗ twistLin p sndL =
        LinearMap.id
      rw [← twistLin_comp, ← twistLin_comp, ← twistLin_add, inl_fst_add_inr_snd, twistLin_id])

/-- **(A1)** (Part A of `CSI6_the_dance_lattices.md`), second half, explicit:
`Ψ_r(N ⊕ N') ≅ Ψ_r(N) ⊕ Ψ_r(N')` (`1 ≤ r ≤ p − 1`). -/
def psiDsumIso (N N' : DPLattice ℤ_[p]) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    Doubling.Iso (psi p (dsum N N') r h1 h2) (dsum (psi p N r h1 h2) (psi p N' r h1 h2)) :=
  isoDsumOfBiprod (psiHom p (fstHom N N') r h1 h2) (psiHom p (sndHom N N') r h1 h2)
    (psiHom p (inlHom N N') r h1 h2) (psiHom p (inrHom N N') r h1 h2)
    (by
      show psiLin p fstL ∘ₗ psiLin p inlL = LinearMap.id
      rw [← psiLin_comp, fstL_comp_inlL, psiLin_id])
    (by
      show psiLin p sndL ∘ₗ psiLin p inrL = LinearMap.id
      rw [← psiLin_comp, sndL_comp_inrL, psiLin_id])
    (by
      show psiLin p fstL ∘ₗ psiLin p inrL = 0
      rw [← psiLin_comp, fstL_comp_inrL, psiLin_zero])
    (by
      show psiLin p sndL ∘ₗ psiLin p inlL = 0
      rw [← psiLin_comp, sndL_comp_inlL, psiLin_zero])
    (by
      show psiLin p inlL ∘ₗ psiLin p fstL + psiLin p inrL ∘ₗ psiLin p sndL = LinearMap.id
      rw [← psiLin_comp, ← psiLin_comp, ← psiLin_add, inl_fst_add_inr_snd, psiLin_id])

/-- **(A1)** (Part A of `CSI6_the_dance_lattices.md`):
`twist p (dsum N N') ≅ dsum (twist p N) (twist p N')` and
`psi p r (dsum N N') ≅ dsum (psi p r N) (psi p r N')` for every `1 ≤ r ≤ p − 1`. -/
theorem A1_additive (N N' : DPLattice ℤ_[p]) :
    Nonempty (Doubling.Iso (twist p (dsum N N')) (dsum (twist p N) (twist p N'))) ∧
    ∀ (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1),
      Nonempty (Doubling.Iso (psi p (dsum N N') r h1 h2)
        (dsum (psi p N r h1 h2) (psi p N' r h1 h2))) :=
  ⟨⟨twistDsumIso p N N'⟩, fun r h1 h2 => ⟨psiDsumIso p N N' r h1 h2⟩⟩

/-! ### (A2) -/

/-- **(A2)** (Part A of `CSI6_the_dance_lattices.md`), for `Ψ_r`: `Ψ_r` applied to an
isomorphism (by CSI3 (F2)). -/
def Iso.psi {N N' : DPLattice ℤ_[p]} (u : Doubling.Iso N N') (r : ℕ) (h1 : 1 ≤ r)
    (h2 : r ≤ p - 1) : Doubling.Iso (psi p N r h1 h2) (psi p N' r h1 h2) where
  hom := psiHom p u.hom r h1 h2
  inv := psiHom p u.inv r h1 h2
  hom_inv := by rw [← (F2 p r h1 h2).2, u.hom_inv, (F2 p r h1 h2).1]
  inv_hom := by rw [← (F2 p r h1 h2).2, u.inv_hom, (F2 p r h1 h2).1]

/-- **(A2)** (Part A of `CSI6_the_dance_lattices.md`): `N ≅ N'` implies `twist p N ≅ twist p N'`
and `psi p r N ≅ psi p r N'` (for every `1 ≤ r ≤ p − 1`). -/
theorem A2_iso {N N' : DPLattice ℤ_[p]} (h : Nonempty (Doubling.Iso N N')) :
    Nonempty (Doubling.Iso (twist p N) (twist p N')) ∧
    ∀ (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1),
      Nonempty (Doubling.Iso (psi p N r h1 h2) (psi p N' r h1 h2)) := by
  obtain ⟨u⟩ := h
  exact ⟨⟨Iso.twist p u⟩, fun r h1 h2 => ⟨Iso.psi p u r h1 h2⟩⟩

/-! ### (A3) -/

/-- (A3), auxiliary: `Φ_p(0) ≅ 0` (empty bases). -/
def twistZeroIso : Doubling.Iso (twist p (Cocycle.zeroL ℤ_[p])) (Cocycle.zeroL ℤ_[p]) :=
  Step36.isoZeroOfIsEmpty _ (by
    show IsEmpty (Fin p × Empty)
    infer_instance)

/-- (A3), auxiliary: `Ψ_r(0) ≅ 0` (empty bases). -/
def psiZeroIso (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    Doubling.Iso (psi p (Cocycle.zeroL ℤ_[p]) r h1 h2) (Cocycle.zeroL ℤ_[p]) :=
  Step36.isoZeroOfIsEmpty _ (by
    show IsEmpty (Bool × Fin p × Empty)
    infer_instance)

/-- **(A3)** (Part A of `CSI6_the_dance_lattices.md`), explicit:
`twist p (dsumList Ls) ≅ dsumList (Ls.map (twist p))`. -/
def twistDsumListIso : (Ls : List (DPLattice ℤ_[p])) →
    Doubling.Iso (twist p (Step36.dsumList Ls)) (Step36.dsumList (Ls.map (twist p)))
  | [] => twistZeroIso p
  | X :: Ls => (twistDsumIso p X (Step36.dsumList Ls)).trans
      (Tensor2.dsumIso (Lemma35b.Iso.refl _) (twistDsumListIso Ls))

/-- **(A3)** (Part A of `CSI6_the_dance_lattices.md`), explicit:
`psi p r (dsumList Ls) ≅ dsumList (Ls.map (psi p r))`. -/
def psiDsumListIso (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : (Ls : List (DPLattice ℤ_[p])) →
    Doubling.Iso (psi p (Step36.dsumList Ls) r h1 h2)
      (Step36.dsumList (Ls.map (fun N => psi p N r h1 h2)))
  | [] => psiZeroIso p r h1 h2
  | X :: Ls => (psiDsumIso p X (Step36.dsumList Ls) r h1 h2).trans
      (Tensor2.dsumIso (Lemma35b.Iso.refl _) (psiDsumListIso r h1 h2 Ls))

/-- **(A3)** (Part A of `CSI6_the_dance_lattices.md`):
`twist p (dsumList Ls) ≅ dsumList (Ls.map (twist p))`, and similarly for `psi p r`. -/
theorem A3_dsumList (Ls : List (DPLattice ℤ_[p])) :
    Nonempty (Doubling.Iso (twist p (Step36.dsumList Ls)) (Step36.dsumList (Ls.map (twist p)))) ∧
    ∀ (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1),
      Nonempty (Doubling.Iso (psi p (Step36.dsumList Ls) r h1 h2)
        (Step36.dsumList (Ls.map (fun N => psi p N r h1 h2)))) :=
  ⟨⟨twistDsumListIso p Ls⟩, fun r h1 h2 => ⟨psiDsumListIso p r h1 h2 Ls⟩⟩

end ColouredSand.OddTwist
