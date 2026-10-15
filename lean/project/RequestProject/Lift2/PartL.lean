module

public import RequestProject.Lift2.Basic

/-!
# `C28_lifting_mod_2_and_corollary_34.md`: Part L (lifting a morphism)

Encodings (namespace `Lift2`): as in `Lift2/Basic.lean`. A morphism over `B` between the
reductions is `h̄ : Hom (baseChange φ M) (baseChange φ N)`; it is weight-preserving when
`IsWtPres h̄.toLin` (weights of `baseChange φ M` are those of `M`). "A lift" of `h̄` is
`h : Hom M N` with `bc φ h.toLin = h̄.toLin`, equivalently `bcHom φ h = h̄`.
-/

@[expose] public section

noncomputable section

namespace Lift2

open DPLattice WeylFilt Doubling Twist LemmaW Cocycle Finset

variable {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}

/-- (L0) Under (H1): for every weight-preserving `h̄ : (M.ι → B) →ₗ[B] (N.ι → B)` there is a
weight-preserving `φ0 : Lin M N` with `bc φ φ0 = h̄` (entries lifted by (H1), `0` where
`M.wt i ≠ N.wt j`). Uses only (H1). -/
theorem L0 (h1 : H1 φ) {M N : DPLattice A} (hb : (M.ι → B) →ₗ[B] (N.ι → B))
    (hhb : IsWtPres (M := baseChange φ M) (N := baseChange φ N) hb) :
    ∃ φ0 : Lin M N, IsWtPres φ0 ∧ bc φ φ0 = hb := by
  classical
  let e : M.ι → N.ι → A := fun i j =>
    if M.wt i = N.wt j then Function.surjInv h1 (hb (Pi.single i 1) j) else 0
  have he : ∀ i j, (Matrix.toLin' (Matrix.of fun j i => e i j) : Lin M N) (Pi.single i 1) j
      = e i j := fun i j => by simp [Matrix.toLin'_apply]
  refine ⟨Matrix.toLin' (Matrix.of fun j i => e i j), fun i j hij => ?_, ext_single fun i => ?_⟩
  · rw [he]; simp [e, hij]
  · funext j
    rw [bc_single_apply, he]
    by_cases hij : M.wt i = N.wt j
    · simp only [e, hij, if_true]
      exact Function.surjInv_eq h1 _
    · simp only [e, hij, if_false, map_zero]
      exact (hhb i j hij).symm

/-- (L1) A weight-preserving `h : Lin M N` with `d h = 0` is a morphism: there is
`hh : Hom M N` with `hh.toLin = h` (`H` commutes with weight-preserving maps). No ring
hypothesis is used. -/
theorem L1 {M N : DPLattice A} (h : Lin M N) (hw : IsWtPres h) (hd : d h = 0) :
    ∃ hh : Hom M N, hh.toLin = h :=
  ⟨{ toLin := h
     comm_F := fun r => sub_eq_zero.mp (by
        have := congrFun (congrArg Prod.fst hd) r; simpa using this)
     comm_E := fun r => sub_eq_zero.mp (by
        have := congrFun (congrArg Prod.snd hd) r; simpa using this)
     comm_H := comm_H_of_isWtPres hw }, rfl⟩

/-- (L2) **Lifting (end of the proof of Lemma 3.3).** Under (H1), (H2), (H3): if
`HasDeltaFilt M` and `HasNablaFilt N`, then every `h̄ : Hom (baseChange φ M) (baseChange φ N)`
with `h̄.toLin` weight-preserving has a lift `h : Hom M N` with `h.toLin` weight-preserving,
`bc φ h.toLin = h̄.toLin`, and (equivalently) `bcHom φ h = h̄`. Uses (H1), (H2), (H3). -/
theorem L2 (h1 : H1 φ) (h2 : H2 φ) (h3 : H3 A) {M N : DPLattice A} (hM : HasDeltaFilt M)
    (hN : HasNablaFilt N) (hb : Hom (baseChange φ M) (baseChange φ N))
    (hhb : IsWtPres hb.toLin) :
    ∃ h : Hom M N, IsWtPres h.toLin ∧ bc φ h.toLin = hb.toLin ∧ bcHom φ h = hb := by
  obtain ⟨φ0, hφ0w, hφ0⟩ := L0 h1 hb.toLin hhb
  obtain ⟨δ, hδ, hδc⟩ := D3 h2 h3 φ0 hφ0w (fun r => hφ0 ▸ hb.comm_F r)
    (fun r => hφ0 ▸ hb.comm_E r)
  obtain ⟨ψ, hψw, hψ⟩ := (V4 hM hN).1 δ hδc
  have hw : IsWtPres (φ0 - (2 : A) • ψ) := isWtPres_sub hφ0w (fun i j hij => by
    simp [hψw i j hij])
  have hd : d (φ0 - (2 : A) • ψ) = 0 := by rw [d_sub, d_smul, hψ, hδ, sub_self]
  obtain ⟨h, hh⟩ := L1 _ hw hd
  have h20 : φ 2 = 0 := (h2 2).mpr ⟨1, (mul_one 2).symm⟩
  have hbc : bc φ h.toLin = hb.toLin := by
    rw [hh, bc_sub, bc_smul, h20, zero_smul, sub_zero, hφ0]
  exact ⟨h, hh ▸ hw, hbc, Hom.ext' hbc⟩

end Lift2
