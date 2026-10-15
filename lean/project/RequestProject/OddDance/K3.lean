module

public import RequestProject.OddDance.Tensor

/-!
# `CSI6_the_dance_lattices.md`, Part K, (K3) (optional) — the simple weights

Namespace `ColouredSand.OddTwist`. Reuses CSG3 `ColouredSand.TiltP.Ttilt`, `IsSimpleWt`,
`Ttilt_of_simple`, CSI1 (D1) `D1_iso` (`Φ_p(Δ(μ)) ≅ Δ(pμ + p − 1)`) and `Iso.twist`.

Only the part of (K3) for *simple* weights `λ` is proved here: for simple `λ` (that is,
`λ ≤ p − 1`, or `p ∣ λ + 1` and `λ ≤ p² − 1`), `danceL p λ ≅ Ttilt p λ = Δ(λ)`. The non-simple
weights (`Ttilt p λ = Tglue p r a`, CSG3's glued lattice) are not treated.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

variable (p : ℕ) [Fact p.Prime]

/-- (K3), auxiliary: `L(p b + p − 1) ≅ Δ(p b + p − 1)` whenever `L(b) ≅ Δ(b)`
(Part A (A2) and CSI1 (D1)). -/
lemma danceL_twist_iso_delta {b : ℕ} (h : Nonempty (Doubling.Iso (danceL p b) (delta ℤ_[p] b))) :
    Nonempty (Doubling.Iso (danceL p (p * b + p - 1)) (delta ℤ_[p] (p * b + p - 1))) := by
  obtain ⟨u⟩ := h
  obtain ⟨v⟩ := D1_iso p b
  rw [danceL_twist_eq]
  exact ⟨(Iso.twist p u).trans v⟩

/-- **(K3)** (Part K of `CSI6_the_dance_lattices.md`, optional), for the simple weights: if `λ`
is simple (`IsSimpleWt p λ`: `λ ≤ p − 1`, or `p ∣ λ + 1` and `λ ≤ p² − 1`), then
`danceL p λ ≅ Ttilt p λ` (both are `Δ(λ)` up to isomorphism). -/
theorem K3_simple {l : ℕ} (hs : ColouredSand.TiltP.IsSimpleWt p l) :
    Nonempty (Doubling.Iso (danceL p l) (ColouredSand.TiltP.Ttilt p l)) := by
  rw [ColouredSand.TiltP.Ttilt_of_simple p hs]
  have hp := two_le_prime p
  rcases hs with h | ⟨⟨c, hc⟩, hle⟩
  · exact danceL_iso_delta p h
  · have hc1 : 1 ≤ c := by rcases c with _ | c <;> simp_all
    have hpp : p ^ 2 = p * p := sq p
    have hcp : c ≤ p := by
      by_contra hcon
      have : p * (p + 1) ≤ p * c := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this
      omega
    have hl : l = p * (c - 1) + p - 1 := by
      have : p * (c - 1) + p = p * c := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hc1]
      omega
    rw [hl]
    exact danceL_twist_iso_delta p (danceL_iso_delta p (by omega))

end ColouredSand.OddTwist
