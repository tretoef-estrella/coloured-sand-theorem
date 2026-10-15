module

public import RequestProject.Step36.All

/-!
# `C31_theorem_36_the_family_decomposition.md`: Part P — permutations and nested sums

Encodings (namespace `FamDec`): finite direct sums are C30's `Step36.dsumList`; "`X ≅ Y`" is
`Nonempty (Doubling.Iso X Y)`, and the explicit isomorphisms are given as `def`s
(`dsumListPermIso`, `dsumListFlatMapIso`). Permutations of lists are `List.Perm`. Part P holds
over any commutative ring `A`.
-/

@[expose] public section

noncomputable section

namespace FamDec

open DPLattice WeylFilt Doubling Lemma35 Tensor2 Lemma35b Cocycle Step36

variable {A : Type*} [CommRing A]

/-- (P1), explicit: the isomorphism `dsum X (dsum Y M) ≅ dsum Y (dsum X M)` (C24 `dsumAssoc`,
`dsumComm`, C23 `dsumIso`). -/
def dsumSwapIso (X Y M : DPLattice A) : Doubling.Iso (dsum X (dsum Y M)) (dsum Y (dsum X M)) :=
  ((dsumAssoc X Y M).symm.trans (dsumIso (dsumComm X Y) (Iso.refl M))).trans (dsumAssoc Y X M)

/-- **(P1)** If `L₁ ~ L₂` (`List.Perm`) then `dsumList L₁ ≅ dsumList L₂` (by induction on the
permutation, with C24 `dsumComm`, `dsumAssoc` and C23 `dsumIso`). -/
theorem P1 {L₁ L₂ : List (DPLattice A)} (h : L₁.Perm L₂) :
    Nonempty (Doubling.Iso (dsumList L₁) (dsumList L₂)) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons X _ ih =>
    obtain ⟨u⟩ := ih
    exact ⟨dsumIso (Iso.refl X) u⟩
  | swap X Y M => exact ⟨dsumSwapIso Y X (dsumList M)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨u⟩ := ih₁
    obtain ⟨v⟩ := ih₂
    exact ⟨u.trans v⟩

/-- **(P2)** For `f : ℕ → DPLattice A`, `g : ℕ → List (DPLattice A)` and `L : List ℕ`: if
`f λ ≅ dsumList (g λ)` for every `λ ∈ L`, then `dsumList (L.map f) ≅ dsumList (L.flatMap g)`
(from C30 (K4a), (K4b)). -/
theorem P2 (f : ℕ → DPLattice A) (g : ℕ → List (DPLattice A)) (L : List ℕ)
    (h : ∀ lam ∈ L, Nonempty (Doubling.Iso (f lam) (dsumList (g lam)))) :
    Nonempty (Doubling.Iso (dsumList (L.map f)) (dsumList (L.flatMap g))) := by
  induction L with
  | nil => exact ⟨Iso.refl _⟩
  | cons a L ih =>
    obtain ⟨u⟩ := h a (by simp)
    obtain ⟨v⟩ := ih (fun lam hlam => h lam (by simp [hlam]))
    rw [List.map_cons, List.flatMap_cons, dsumList_cons]
    exact ⟨(dsumIso u v).trans (dsumListAppendIso (g a) (L.flatMap g)).symm⟩

end FamDec
