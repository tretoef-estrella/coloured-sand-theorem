import RequestProject.OddSplitting.All

/-!
# CheckCSI5 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI5 (`CSI5_the_splitting.md`): Part H with the short exact sequence written
out as its three components (injective, surjective, range = kernel), the two Casimir classes
`(Ω_Y − a)² = p R_Y`, `(Ω_Q − b)² = p R_Q`, `a − b` a unit; (H1) with `e ∘ e = e`, `e ∘ ι = ι`,
`π ∘ e = 0` as linear maps; (H2); the Casimir of a direct sum; Cayley–Hamilton in the form used;
units detected mod `p`; and (T0)–(T3) with sources and targets written out.
Then `#print axioms`.
-/

namespace CheckCSI5

open ColouredSand.OddTwist DPLattice

variable {p : ℕ} [Fact p.Prime]

/-- Part H, with `ShortExact` written out. -/
theorem hH {Y M Q : DPLattice ℤ_[p]} (ι : Hom Y M) (π : Hom M Q)
    (hinj : Function.Injective ι.toLin) (hsurj : Function.Surjective π.toLin)
    (hex : LinearMap.range ι.toLin = LinearMap.ker π.toLin)
    (a b : ℤ_[p]) (hab : IsUnit (a - b))
    (RY : Module.End ℤ_[p] (Y.ι → ℤ_[p]))
    (hY : (casimir Y - a • LinearMap.id) ∘ₗ (casimir Y - a • LinearMap.id) = (p : ℤ_[p]) • RY)
    (RQ : Module.End ℤ_[p] (Q.ι → ℤ_[p]))
    (hQ : (casimir Q - b • LinearMap.id) ∘ₗ (casimir Q - b • LinearMap.id) = (p : ℤ_[p]) • RQ) :
    (∃ e : Hom M M, e.toLin ∘ₗ e.toLin = e.toLin ∧ e.toLin ∘ₗ ι.toLin = ι.toLin ∧
        π.toLin ∘ₗ e.toLin = 0) ∧
    Nonempty (Doubling.Iso M (Lemma35.dsum Y Q)) := by
  have hSE : WeylFilt.ShortExact ι π := ⟨hinj, hsurj, hex⟩
  refine ⟨?_, splitting_H2 hSE hab ⟨RY, hY⟩ ⟨RQ, hQ⟩⟩
  obtain ⟨e, h1, h2, h3⟩ := splitting_H1 hSE hab ⟨RY, hY⟩ ⟨RQ, hQ⟩
  exact ⟨e, congrArg Hom.toLin h1, congrArg Hom.toLin h2, h3⟩

/-- The Casimir of a direct sum, and `Ω − c` on it. -/
theorem hDsum {A : Type*} [CommRing A] (M N : DPLattice A) (c : A) :
    casimir (Lemma35.dsum M N) = Lemma35.blk (casimir M) (casimir N) ∧
    Dcas (Lemma35.dsum M N) c = Lemma35.blk (Dcas M c) (Dcas N c) :=
  ⟨casimir_dsum M N, Dcas_dsum M N c⟩

/-- Cayley–Hamilton in the form used in step 1. -/
theorem hCH {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι] (q : A)
    (Nn R : Module.End A (ι → A)) (h : Nn * Nn = q • R) :
    ∃ (k : ℕ) (g : Polynomial A), Nn ^ (2 * k) + q • Polynomial.aeval Nn g = 0 :=
  exists_annihilating_poly q Nn R h

/-- Units are detected modulo `p`. -/
theorem hModP {ι : Type*} [Fintype ι] [DecidableEq ι] (x : Module.End ℤ_[p] (ι → ℤ_[p]))
    (h : IsUnit ((PadicInt.toZMod (p := p)).mapMatrix (LinearMap.toMatrix' x))) : IsUnit x :=
  isUnit_of_isUnit_modP x h

variable (N : DPLattice ℤ_[p])

/-- (T0). -/
theorem hT0 (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (twist p N)) (psi p N 1 h1 h2)) :=
  tensor_T0 h1 h2

/-- (T1), `2 ≤ r ≤ p − 2`. -/
theorem hT1 (r : ℕ) (h2r : 2 ≤ r) (hr : r ≤ p - 2) (a1 : 1 ≤ r) (a2 : r ≤ p - 1)
    (b1 : 1 ≤ r + 1) (b2 : r + 1 ≤ p - 1) (c1 : 1 ≤ r - 1) (c2 : r - 1 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N r a1 a2))
      (Lemma35.dsum (psi p N (r + 1) b1 b2) (psi p N (r - 1) c1 c2))) :=
  tensor_T1 r h2r hr

/-- (T2), every odd prime. -/
theorem hT2 (hp3 : 3 ≤ p) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) (b1 : 1 ≤ 2) (b2 : 2 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N 1 h1 h2))
      (Lemma35.dsum (psi p N 2 b1 b2) (Lemma35.dsum (twist p N) (twist p N)))) :=
  tensor_T2 hp3 h1 h2

/-- (T3), every odd prime, with `Psip` written out as `twist p (tensor V N)`. -/
theorem hT3 (hp3 : 3 ≤ p) (a1 : 1 ≤ p - 1) (a2 : p - 1 ≤ p - 1) (b1 : 1 ≤ p - 2)
    (b2 : p - 2 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N (p - 1) a1 a2))
      (Lemma35.dsum (twist p (Tensor2.tensor (V ℤ_[p]) N)) (psi p N (p - 2) b1 b2))) :=
  tensor_T3 hp3

end CheckCSI5

#print axioms CheckCSI5.hH
#print axioms CheckCSI5.hDsum
#print axioms CheckCSI5.hCH
#print axioms CheckCSI5.hModP
#print axioms CheckCSI5.hT0
#print axioms CheckCSI5.hT1
#print axioms CheckCSI5.hT2
#print axioms CheckCSI5.hT3
#print axioms ColouredSand.OddTwist.splitting_H1
#print axioms ColouredSand.OddTwist.splitting_H2
#print axioms ColouredSand.OddTwist.exists_retraction
#print axioms ColouredSand.OddTwist.tensor_T1
#print axioms ColouredSand.OddTwist.tensor_T3
