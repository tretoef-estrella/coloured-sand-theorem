module

public import RequestProject.Step36.PartW

@[expose] public section

noncomputable section

/-!
# `C30_the_step_of_theorem_36.md`: Part A — the step over `A`, and Part Z — the case of the paper

Encodings (namespace `Step36`), reusing C20 (`Iso`), C21 (`bc`, `baseChange`, `C3_hyp`),
C24 (`lemma35Iso`), C25 (`IsWtPres`), C27 (`HasDeltaFilt`, `HasNablaFilt`), C28 (`H1`, `H2`,
`H3`, `OneAddTwoUnit`, `C3`, `Z1`) and C29 (`T3`):

* The hypotheses (H1), (H2), (H3) and `OneAddTwoUnit` are C28's explicit propositions, passed as
  arguments; `h2 : (2 : B) = 0`.
* "`e` reduces to `lemma35Iso`" is `bc φ e.hom.toLin = (lemma35Iso φ h2 N).hom.toLin` and
  `bc φ e.inv.toLin = (lemma35Iso φ h2 N).inv.toLin` (C21's entrywise base change of linear
  maps).
* Part Z: `ℤ_[2]` is `PadicInt 2`, `B = ZMod 2`, `φ = PadicInt.toZMod`, and `h2` is the
  component `(2 : ZMod 2) = 0` of C21's `C3_hyp`.
-/

namespace Step36

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b LemmaW Cocycle Lift2

section A1

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]
  {φ : A →+* B}

/-- **(A1)** The step over `A`. Assume `H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A` and
`h2 : (2 : B) = 0`. For every DP-lattice `N` over `A` with `HasDeltaFilt N` and
`HasNablaFilt N` there is
`e : Iso (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))`
with `e.hom.toLin`, `e.inv.toLin` weight-preserving, `bc φ e.hom.toLin =
(lemma35Iso φ h2 N).hom.toLin` and `bc φ e.inv.toLin = (lemma35Iso φ h2 N).inv.toLin`.
Proof: C29 (T3) gives both filtrations of both lattices; (W1), (W2); then C28 (C3) with
`ē = lemma35Iso φ h2 N`. -/
theorem A1 (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) (h2 : (2 : B) = 0)
    {N : DPLattice A} (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    ∃ e : Doubling.Iso (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N))),
      IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
      bc φ e.hom.toLin = (lemma35Iso φ h2 N).hom.toLin ∧
      bc φ e.inv.toLin = (lemma35Iso φ h2 N).inv.toLin := by
  obtain ⟨⟨hXD, hXN⟩, ⟨hYD, hYN⟩⟩ := Filt.T3 hΔ hN
  exact Lift2.C3 h1 hk h3 hU hXD hXN hYD hYN (lemma35Iso φ h2 N) (W1 φ N h2) (W2 φ N h2)

end A1

/-! ### Part Z -/

/-- **(Z1)**, part (W1): for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` and every DP-lattice
`N` over `ℤ_[2]`, the underlying map of `lemma35Iso` is weight-preserving. -/
theorem Z1_W1 (N : DPLattice ℤ_[2]) :
    IsWtPres (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).hom.toLin :=
  W1 PadicInt.toZMod N Twist.C3_hyp.2.2.2.2.1

/-- **(Z1)**, part (W2): for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`, the inverse map
of `lemma35Iso` is weight-preserving. -/
theorem Z1_W2 (N : DPLattice ℤ_[2]) :
    IsWtPres (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).inv.toLin :=
  W2 PadicInt.toZMod N Twist.C3_hyp.2.2.2.2.1

/-- **(Z1)**, part (A1): for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` (hypotheses (H1),
(H2), (H3), `OneAddTwoUnit` by C28 (Z1), `2 = 0` by C21 `C3_hyp`) and every DP-lattice `N` over
`ℤ_[2]` with both filtrations, `V ⊗ V ⊗ Φ(N) ≅ Φ(N)^2 ⊕ Φ(V ⊗ N)` by an isomorphism with both maps
weight-preserving and reducing to `lemma35Iso`. -/
theorem Z1_A1 {N : DPLattice ℤ_[2]} (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    ∃ e : Doubling.Iso (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N))),
      IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
      bc PadicInt.toZMod e.hom.toLin =
        (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).hom.toLin ∧
      bc PadicInt.toZMod e.inv.toLin =
        (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).inv.toLin :=
  A1 Lift2.Z1.1 Lift2.Z1.2.1 Lift2.Z1.2.2.1 Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 hΔ hN

/-- **(Z1)** (W1), (W2) and (A1) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`. -/
theorem Z1 (N : DPLattice ℤ_[2]) :
    IsWtPres (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).hom.toLin ∧
    IsWtPres (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).inv.toLin ∧
    (HasDeltaFilt N → HasNablaFilt N →
      ∃ e : Doubling.Iso (tensorV (tensorV (phi N)))
          (dsum (dsum (phi N) (phi N)) (phi (tensorV N))),
        IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
        bc PadicInt.toZMod e.hom.toLin =
          (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).hom.toLin ∧
        bc PadicInt.toZMod e.inv.toLin =
          (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).inv.toLin) :=
  ⟨Z1_W1 N, Z1_W2 N, fun hΔ hN => Z1_A1 hΔ hN⟩

end Step36
