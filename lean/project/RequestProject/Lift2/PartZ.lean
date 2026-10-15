module

public import RequestProject.Lift2.PartC

/-!
# `C28_lifting_mod_2_and_corollary_34.md`: Part Z (the case of the paper)

Encodings (namespace `Lift2`): `ℤ_[2]` is Mathlib's `PadicInt 2`, `ZMod 2` is Mathlib's
`ZMod 2`, and `φ = PadicInt.toZMod : ℤ_[2] →+* ZMod 2`; everything else as in
`Lift2/Basic.lean`.
-/

@[expose] public section

noncomputable section

namespace Lift2

open DPLattice WeylFilt Doubling Twist LemmaW Cocycle Finset

/-- (Z1) `φ = PadicInt.toZMod : ℤ_[2] →+* ZMod 2` satisfies (H1), (H2), (H3), and every
`1 + 2a` with `a : ℤ_[2]` is a unit. -/
theorem Z1 : H1 (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ∧ H2 (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ∧
    H3 ℤ_[2] ∧ OneAddTwoUnit ℤ_[2] := by
  have hker : ∀ a : ℤ_[2], PadicInt.toZMod a = 0 ↔ ∃ b, a = 2 * b := fun a => by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [← hb, mul_comm]; norm_num⟩
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [hb, mul_comm]; norm_num⟩
  refine ⟨fun x => ⟨(x.val : ℤ_[2]), by simp⟩, hker, fun a ha => ?_, fun a => ?_⟩
  · rcases mul_eq_zero.mp ha with h | h
    · exact absurd h two_ne_zero
    · exact h
  · rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    intro h
    have h2 : PadicInt.toZMod (2 * a) = 0 := (hker _).mpr ⟨a, rfl⟩
    have : PadicInt.toZMod (1 + 2 * a) = 1 := by rw [map_add, h2, map_one, add_zero]
    rw [h] at this
    exact zero_ne_one this

/-- (Z2), (L2) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`: if `HasDeltaFilt M` and
`HasNablaFilt N`, every weight-preserving morphism `h̄` between the reductions modulo 2 has a
weight-preserving lift `h : Hom M N` with `bc φ h.toLin = h̄.toLin` (and `bcHom φ h = h̄`). -/
theorem Z2_L2 {M N : DPLattice ℤ_[2]} (hM : HasDeltaFilt M) (hN : HasNablaFilt N)
    (hb : Hom (baseChange PadicInt.toZMod M) (baseChange (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) N))
    (hhb : IsWtPres hb.toLin) :
    ∃ h : Hom M N, IsWtPres h.toLin ∧ bc PadicInt.toZMod h.toLin = hb.toLin ∧
      bcHom PadicInt.toZMod h = hb :=
  L2 Z1.1 Z1.2.1 Z1.2.2.1 hM hN hb hhb

/-- (Z2), (C3) **Corollary 3.4** for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`:
DP-lattices `X`, `Y` over `ℤ_[2]` with both filtrations whose reductions modulo 2 are isomorphic
by weight-preserving maps are isomorphic, by an isomorphism `e` whose two maps are
weight-preserving and reduce to the given ones. -/
theorem Z2_C3 {X Y : DPLattice ℤ_[2]} (hXD : HasDeltaFilt X) (hXN : HasNablaFilt X)
    (hYD : HasDeltaFilt Y) (hYN : HasNablaFilt Y)
    (eb : Iso (baseChange PadicInt.toZMod X) (baseChange (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) Y))
    (hhom : IsWtPres eb.hom.toLin) (hinv : IsWtPres eb.inv.toLin) :
    ∃ e : Iso X Y, IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
      bc PadicInt.toZMod e.hom.toLin = eb.hom.toLin ∧
      bc PadicInt.toZMod e.inv.toLin = eb.inv.toLin :=
  C3 Z1.1 Z1.2.1 Z1.2.2.1 Z1.2.2.2 hXD hXN hYD hYN eb hhom hinv

end Lift2
