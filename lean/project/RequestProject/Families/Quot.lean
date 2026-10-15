module

public import RequestProject.FamDec.Decomp
public import RequestProject.DPLattice.Corollary

/-!
# `C32_theorem_38_the_groups_of_the_families.md`: Part Q — from Theorem 3.6 to the product of
# cokernels

Encodings (namespace `Families`):

* (Q0) compares C29's `Filt.tpow` with C18's `DPLattice.tensorPow` (both `V^{⊗n}`).
* (Q1) A vector of `dsumList Ls` (C30) is `(dsumList Ls).ι → A`; the product of the summands is
  the dependent function type `(j : Fin Ls.length) → (Ls.get j).ι → A`.  "Carrying `Fd 1` and `H`
  componentwise" is exactly the form of the hypotheses `hF`, `hH` of C18 `C1`:
  `Θ (Fd 1 x) = fun j => (Ls.get j).Fd 1 (Θ x j)` and the same for `H`.  The equivalence is built
  by recursion on the list from `LinearEquiv.sumArrowLequivProdArrow` and `Fin.consLinearEquiv`;
  it is stated more generally for lists `l.map f` (`dsumMapEquiv`), which is the form used in
  Part T.
* (Q2) `isoEquiv e` is the linear equivalence underlying a C20 isomorphism `e : Doubling.Iso X Y`
  (`e.hom.toLin` with inverse `e.inv.toLin`).
-/

@[expose] public section

noncomputable section

namespace Families

open DPLattice Doubling Lemma35 Cocycle Filt Step36

universe u

variable {A : Type u} [CommRing A]

/-! ### (Q0) -/

/-- **(Q0)** of `C32_theorem_38_the_groups_of_the_families.md`: for every `n`,
`tpow A n = DPLattice.tensorPow A n`. -/
theorem Q0 (n : ℕ) : tpow A n = DPLattice.tensorPow A n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tpow_succ, ih]; rfl

/-! ### (Q1) -/

/-- **(Q1)** of `C32_theorem_38_the_groups_of_the_families.md`, general form for a list
`l.map f`: an `A`-linear equivalence
`((dsumList (l.map f)).ι → A) ≃ₗ[A] ((j : Fin l.length) → (f (l.get j)).ι → A)`
carrying `Fd 1` and `H` componentwise. -/
theorem dsumMap_exists {α : Type*} (f : α → DPLattice A) (l : List α) :
    ∃ Θ : ((dsumList (l.map f)).ι → A) ≃ₗ[A] ((j : Fin l.length) → (f (l.get j)).ι → A),
      (∀ x, Θ ((dsumList (l.map f)).Fd 1 x) = fun j => (f (l.get j)).Fd 1 (Θ x j)) ∧
      (∀ x, Θ (H (dsumList (l.map f)) x) = fun j => H (f (l.get j)) (Θ x j)) := by
  induction l with
  | nil =>
    haveI : Subsingleton ((dsumList (([] : List α).map f)).ι → A) :=
      inferInstanceAs (Subsingleton (Empty → A))
    haveI : Subsingleton ((j : Fin ([] : List α).length) → (f (([] : List α).get j)).ι → A) :=
      ⟨fun _ _ => funext fun j => j.elim0⟩
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _⟩
  | cons a l ih =>
    obtain ⟨Θ, hF, hH⟩ := ih
    let Θ' : ((dsumList ((a :: l).map f)).ι → A) ≃ₗ[A]
        ((j : Fin (a :: l).length) → (f ((a :: l).get j)).ι → A) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ A A).trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl A _) Θ).trans
          (Fin.consLinearEquiv A (fun j : Fin (l.length + 1) => (f ((a :: l).get j)).ι → A)))
    refine ⟨Θ', fun x => ?_, fun x => ?_⟩
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · exact congrFun (hF (x ∘ Sum.inr)) j
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · exact congrFun (hH (x ∘ Sum.inr)) j

/-- **(Q1)** of `C32_theorem_38_the_groups_of_the_families.md`: for every list
`Ls : List (DPLattice A)` there is an `A`-linear equivalence
`((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A)` carrying
`(dsumList Ls).Fd 1` to the `Fd 1` of `Ls.get j` and `H (dsumList Ls)` to `H (Ls.get j)`,
componentwise (in the form of the hypotheses `hF`, `hH` of C18 `C1`). -/
theorem Q1 (Ls : List (DPLattice A)) :
    ∃ Θ : ((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A),
      (∀ x, Θ ((dsumList Ls).Fd 1 x) = fun j => (Ls.get j).Fd 1 (Θ x j)) ∧
      (∀ x, Θ (H (dsumList Ls) x) = fun j => H (Ls.get j) (Θ x j)) := by
  have h := dsumMap_exists (fun X : DPLattice A => X) Ls
  rw [List.map_id'] at h
  exact h

/-! ### (Q2) -/

/-- **(Q2)** of `C32_theorem_38_the_groups_of_the_families.md` (explicit equivalence): the
`A`-linear equivalence `(X.ι → A) ≃ₗ[A] (Y.ι → A)` underlying `e : Doubling.Iso X Y`. -/
def isoEquiv {X Y : DPLattice A} (e : Doubling.Iso X Y) : (X.ι → A) ≃ₗ[A] (Y.ι → A) :=
  LinearEquiv.ofLinear e.hom.toLin e.inv.toLin (congrArg Hom.toLin e.inv_hom)
    (congrArg Hom.toLin e.hom_inv)

/-- **(Q2)** of `C32_theorem_38_the_groups_of_the_families.md`: every `e : Doubling.Iso X Y`
gives an `A`-linear equivalence `(X.ι → A) ≃ₗ[A] (Y.ι → A)` commuting with `Fd 1` and with `H`
(from the fields `comm_F`, `comm_H` of C18 `Hom`); it is `isoEquiv e`. -/
theorem Q2 {X Y : DPLattice A} (e : Doubling.Iso X Y) :
    ∃ Θ : (X.ι → A) ≃ₗ[A] (Y.ι → A),
      Θ.toLinearMap ∘ₗ X.Fd 1 = Y.Fd 1 ∘ₗ Θ.toLinearMap ∧
      Θ.toLinearMap ∘ₗ H X = H Y ∘ₗ Θ.toLinearMap :=
  ⟨isoEquiv e, e.hom.comm_F 1, e.hom.comm_H⟩

end Families
