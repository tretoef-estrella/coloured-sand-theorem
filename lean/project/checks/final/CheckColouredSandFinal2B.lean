-- CheckColouredSandFinal2B.lean (half B: every import, pieces 19-36) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
-- Assembled by assemble_final.py (Grepy Ship, 14 Oct 2026; v2 15 Oct 2026) from the 36 certified per-piece check files, each body unchanged
-- inside its own namespace FinalCheck.<piece>. Every `#print axioms` line must read [propext, Classical.choice, Quot.sound].
import RequestProject.BlockOp.All
import RequestProject.Blocks.All
import RequestProject.Corollaries.All
import RequestProject.Exponent.All
import RequestProject.Glue.All
import RequestProject.NumberOfFactors.All
import RequestProject.OddCeiling.All
import RequestProject.OddCellFloor.All
import RequestProject.OddDance.All
import RequestProject.OddDeficit.All
import RequestProject.OddHouses.All
import RequestProject.OddLevels.All
import RequestProject.OddPayment.All
import RequestProject.OddPotential.All
import RequestProject.OddRulers.All
import RequestProject.OddSES.All
import RequestProject.OddSmith.All
import RequestProject.OddSplit.All
import RequestProject.OddSplitMove.All
import RequestProject.OddSplitting.All
import RequestProject.OddTheoremI.All
import RequestProject.OddTotal.All
import RequestProject.OddTwist.All
import RequestProject.OddTwistModP.All
import RequestProject.OddWindows.All
import RequestProject.Splitting.All
import RequestProject.Strings.All
import RequestProject.StringsAll.All
import RequestProject.TheoremB.All
import RequestProject.ThmG.All
import RequestProject.ThmGTwo.All
import RequestProject.ThmH.All
import RequestProject.TiltDec.All
import RequestProject.TiltP.All
import RequestProject.TiltRules.All
import RequestProject.TwoTheoremI.All

-- ======== piece CSI5 (from lean/proyecto_cubo/checks/CheckCSI5.lean) ========
namespace FinalCheck.CSI5

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

end FinalCheck.CSI5

-- ======== piece CSI6 (from lean/proyecto_cubo/checks/CheckCSI6.lean) ========
namespace FinalCheck.CSI6

/-!
# CheckCSI6 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI6 (`CSI6_the_dance_lattices.md`): the dance lattice `L(λ)` by its three
defining cases (`λ + 1 = d₀ + p (b + 1)` written out); the rank by the base-`p` digits; the
tensor rule `V ⊗ L(λ)` in every case with `V ⊗ X` written as `Tensor2.tensor (V ℤ_[p]) X`;
`V^{⊗m} ⊗ ℤ_p ≅ ⊕ L(λ)` for every `m`; additivity of `Φ_p`, `Ψ_r`; agreement with CSG5 in the
range `m ≤ p² + p − 1`; (K3) for simple weights. Then `#print axioms`.
-/

namespace CheckCSI6

open ColouredSand.OddTwist DPLattice

variable {p : ℕ} [Fact p.Prime]

/-- (L1): the three cases of the definition. -/
theorem hL (b d l : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1) :
    (l + 1 < p → danceL p l = delta ℤ_[p] l) ∧
    danceL p (p * (b + 1) - 1) = twist p (danceL p b) ∧
    danceL p (d + p * (b + 1) - 1) = psi p (danceL p b) d hd1 hd2 := by
  refine ⟨fun h => danceL_lt p h, ?_, danceL_psi_eq p b d hd1 hd2⟩
  have h : p * (b + 1) - 1 = p * b + p - 1 := by rw [Nat.mul_succ]
  rw [h]; exact danceL_twist_eq p b

/-- (L2): rank = leading digit × p^k × 2^(number of nonzero lower digits). -/
theorem hRank (l : ℕ) :
    Fintype.card (danceL p l).ι =
      (Nat.digits p (l + 1)).getD ((Nat.digits p (l + 1)).length - 1) 0 *
        p ^ ((Nat.digits p (l + 1)).length - 1) *
        2 ^ ((Finset.range ((Nat.digits p (l + 1)).length - 1)).filter
          (fun t => (Nat.digits p (l + 1)).getD t 0 ≠ 0)).card :=
  card_danceL_digits p l

/-- (R1): the list of weights of `V ⊗ L(λ)`, every case. -/
theorem hRule (l : ℕ) (hp3 : 3 ≤ p) :
    VdotL p 0 = [1] ∧
    (1 ≤ l → l ≤ p - 2 → VdotL p l = [l + 1, l - 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = 0 → VdotL p l = [l + 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = 1 → VdotL p l = [l + 1, l - 1, l - 1]) ∧
    (p - 1 ≤ l → 2 ≤ (l + 1) % p → (l + 1) % p ≤ p - 2 → VdotL p l = [l + 1, l - 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = p - 1 →
      VdotL p l = (l - 1) :: (VdotL p ((l + 1) / p - 1)).map (fun b' => p * b' + p - 1)) := by
  refine ⟨VdotL_zero p, fun h1 h2 => VdotL_small h1 h2, fun h1 h2 => VdotL_d0_zero (by omega) h1 h2,
    fun h1 h2 => VdotL_d0_one (by omega) h1 h2, fun h1 h2 h3 => VdotL_d0_mid h1 h2 h3,
    fun h1 h2 => VdotL_d0_top hp3 h1 h2⟩

/-- (R2): `V ⊗ L(λ) ≅ ⊕_{μ ∈ VdotL λ} L(μ)` for every `λ`, `p` odd. -/
theorem hTensor (hp2 : p ≠ 2) (l : ℕ) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (danceL p l))
      (Step36.dsumList ((VdotL p l).map (danceL p)))) :=
  tensor_danceL p hp2 l

/-- (R3): every tensor power, list form and multiplicity form. -/
theorem hTpow (hp2 : p ≠ 2) (m : ℕ) :
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m) (Step36.dsumList ((LL p m).map (danceL p)))) ∧
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m)
      (Step36.dsumList (((List.range (m + 1)).flatMap fun l =>
        List.replicate ((LL p m).count l) l).map (danceL p)))) :=
  ⟨tpow_danceL p hp2 m, tpow_danceL_mult p hp2 m⟩

/-- (R3): the lists `LL`. -/
theorem hLL (m : ℕ) : LL p 0 = [0] ∧ LL p (m + 1) = (LL p m).flatMap (VdotL p) :=
  ⟨rfl, rfl⟩

/-- (A1)–(A3): `Φ_p` and `Ψ_r` are additive and respect isomorphisms. -/
theorem hA (N N' : DPLattice ℤ_[p]) (Ls : List (DPLattice ℤ_[p]))
    (h : Nonempty (Doubling.Iso N N')) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    Nonempty (Doubling.Iso (twist p (Lemma35.dsum N N')) (Lemma35.dsum (twist p N) (twist p N'))) ∧
    Nonempty (Doubling.Iso (psi p (Lemma35.dsum N N') r h1 h2)
      (Lemma35.dsum (psi p N r h1 h2) (psi p N' r h1 h2))) ∧
    Nonempty (Doubling.Iso (twist p N) (twist p N')) ∧
    Nonempty (Doubling.Iso (psi p N r h1 h2) (psi p N' r h1 h2)) ∧
    Nonempty (Doubling.Iso (twist p (Step36.dsumList Ls)) (Step36.dsumList (Ls.map (twist p)))) :=
  ⟨(A1_additive p N N').1, (A1_additive p N N').2 r h1 h2, (A2_iso p h).1, (A2_iso p h).2 r h1 h2,
    (A3_dsumList p Ls).1⟩

/-- (K1), (K2): agreement with CSG5 for `m ≤ p² + p − 1`. -/
theorem hK (hp3 : 3 ≤ p) (m l : ℕ) (hm : m ≤ p ^ 2 + p - 1) :
    (LL p m).Perm (ColouredSand.TiltDec.LP p m) ∧ (LL p m).count l = ColouredSand.TiltDec.mP p l m :=
  ⟨K2_perm hp3 hm, K2_count hp3 hm l⟩

end CheckCSI6

#print axioms CheckCSI6.hL
#print axioms CheckCSI6.hRank
#print axioms CheckCSI6.hRule
#print axioms CheckCSI6.hTensor
#print axioms CheckCSI6.hTpow
#print axioms CheckCSI6.hLL
#print axioms CheckCSI6.hA
#print axioms CheckCSI6.hK
#print axioms ColouredSand.OddTwist.K1_perm
#print axioms ColouredSand.OddTwist.K3_simple
#print axioms ColouredSand.OddTwist.danceL
#print axioms ColouredSand.OddTwist.leading_digit_ne_zero

end FinalCheck.CSI6

-- ======== piece CSI7 (from lean/proyecto_cubo/checks/CheckCSI7.lean) ========
namespace FinalCheck.CSI7

/-!
# CheckCSI7 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI7 (`CSI7_the_twist_move.md`): the system `Gp` on a generator; the
odd twist `flT`, `NT`, `FT` on generators; `QT` written out as `−p^(p−2) • Π Q(pf + j)`;
Theorem A_p (odd `p`, and every `p ≥ 1` with the sign built in); the `c = 1` and `c = p^h`
corollaries; evenness. Then `#print axioms`.
-/

namespace CheckCSI7

open ColouredSand.OddTwist DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The system on a generator, and the twist written out. -/
theorem hSetting (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A)
    (s' : S) (i : ι) (x : N i) (q : ι × Fin p) (f : ℕ) :
    Gp p fl F Q (oslot A N S s' i x) = oslotE A N S s' (F (DirectSum.lof A ι N i x)) +
      ∑ s, ((p : A) * Q (fl i) s s') • oslot A N S s i x ∧
    flT p fl q = p * fl q.1 + q.2.val ∧
    QT p Q f = -((p : A) ^ (p - 2)) • ((List.range p).map (fun j => Q (p * f + j))).prod :=
  ⟨Gp_oslot p fl F Q s' i x, rfl, by simp [QT]⟩

/-- `FT` on generators: shift up one layer; from the top layer, `−p • b_0 (F x)`. -/
theorem hFT (p : ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p) (x : N i) :
    (∀ h : j.val + 1 < p, FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      DirectSum.lof A (ι × Fin p) (NT p N) (i, ⟨j.val + 1, h⟩) x) ∧
    (¬ j.val + 1 < p → FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      -(p : A) • embT A N p ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x))) :=
  ⟨fun h => FT_lof_lt p F i j h x, fun h => FT_lof_last p F i j h x⟩

/-- (A1) Theorem A_p for odd `p`. -/
theorem hA1 (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F (QT p Q))))) :=
  theorem_Ap p hp fl F Q c

/-- (A1) for every `p ≥ 1` with the sign `(−1)^p` built into the data. -/
theorem hA1sign (p : ℕ) (hp : 0 < p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F
          (fun f => ((-1 : A) ^ p * (p : A) ^ (p - 2)) •
            ((List.range p).map (fun j => Q (p * f + j))).prod))))) :=
  theorem_Ap_sign p hp fl F Q c

/-- (A2) powers, and the `c = 1` form. -/
theorem hA2 (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NT p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QT p Q))))) ∧
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      (Payment.Sys N S ⧸ LinearMap.range ((p : A) • Gp p fl F (QT p Q)))) :=
  ⟨corollary_Ap2 p hp fl F Q h, corollary_Ap_one p hp fl F Q⟩

/-- (A3) evenness. -/
theorem hA3 (p : ℕ) (Q : ℕ → Matrix S S A) (I : Ideal A)
    (hQ : ∀ φ s s', Q φ s s' ∈ I) (f : ℕ) (s s' : S) :
    QT p Q f s s' ∈ Ideal.span {(p : A)} ^ (p - 2) * I ^ p :=
  evenness_A3 p Q I hQ f s s'

end CheckCSI7

#print axioms CheckCSI7.hSetting
#print axioms CheckCSI7.hFT
#print axioms CheckCSI7.hA1
#print axioms CheckCSI7.hA1sign
#print axioms CheckCSI7.hA2
#print axioms CheckCSI7.hA3
#print axioms ColouredSand.OddTwist.chainCokerEquiv
#print axioms ColouredSand.OddTwist.oslot_eq_slotLof

end FinalCheck.CSI7

-- ======== piece CSI8 (from lean/proyecto_cubo/checks/CheckCSI8.lean) ========
namespace FinalCheck.CSI8

/-!
# CheckCSI8 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI8 (`CSI8_the_split_move.md`): the floors of the split; the operator `FS`
on generators (shift; `A_{p−1} x ↦ −p A_0(Fx) + p C_{p−r} x`; `C_{p−1} x ↦ −p C_0(Fx)`);
`Π(a,b)`, `QA`, `QC`, `K` written out; the blocks of `QS`; Theorem (M1) for odd `p` and,
with the sign built in, for every `p`; (M2). Then `#print axioms`.
-/

namespace CheckCSI8

open ColouredSand.OddTwist DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- Floors, products and the data, written out. -/
theorem hData (p r : ℕ) (fl : ι → ℕ) (Q : ℕ → Matrix S S A) (i : ι) (j : Fin p) (f : ℕ)
    (s s' : S) :
    flS p r fl (i, false, j) = p * fl i + j.val ∧
    flS p r fl (i, true, j) = p * fl i + r + j.val ∧
    prodQ Q (p * f + r) (p * f + p) = ((List.range (p * f + p - (p * f + r))).map
      (fun t => Q (p * f + r + t))).prod ∧
    QA p Q f = -((p : A) ^ (p - 2)) • prodQ Q (p * f) (p * f + p) ∧
    QC p r Q f = -((p : A) ^ (p - 2)) • prodQ Q (p * f + r) (p * f + r + p) ∧
    KS p r Q f = ((-1 : A) ^ (p - r + 1) * (p : A) ^ (p - r - 1)) •
      prodQ Q (p * f + r) (p * f + p) ∧
    QS p r Q f (s, false) (s', false) = QA p Q f s s' ∧
    QS p r Q f (s, true) (s', true) = QC p r Q f s s' ∧
    QS p r Q f (s, true) (s', false) = KS p r Q f s s' ∧
    QS p r Q f (s, false) (s', true) = 0 := by
  refine ⟨by simp [flS], by simp [flS], rfl, by simp [QA], by simp [QC], rfl, rfl, rfl, rfl, rfl⟩

/-- `FS` on generators. -/
theorem hFS (p r : ℕ) (hr : 0 < r) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (b : Bool)
    (j : Fin p) (x : N i) :
    (∀ h : j.val + 1 < p, FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, j) x) =
      DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, ⟨j.val + 1, h⟩) x) ∧
    (¬ j.val + 1 < p →
      FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, false, j) x) =
        -(p : A) • embS A N p false ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x)) +
          (p : A) • DirectSum.lof A (ι × Bool × Fin p) (NS p N)
            (i, true, ⟨p - r, Nat.sub_lt j.pos hr⟩) x) ∧
    (¬ j.val + 1 < p →
      FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, true, j) x) =
        -(p : A) • embS A N p true ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x))) :=
  ⟨fun h => FS_lof_lt p r hr F i b j h x, fun h => FS_lof_lastA p r hr F i j h x,
    fun h => FS_lof_lastC p r hr F i j h x⟩

/-- (M1), odd `p`. -/
theorem hM1 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸ LinearMap.range ((c * p) • Gp p fl F (QS p r Q))))) :=
  theorem_M1 p r hp hr hrp fl F Q c

/-- (M1), every `p`, with `(−1)^p` on the diagonal blocks. -/
theorem hM1sign (p r : ℕ) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((c * p) • Gp p fl F (QSsign p r Q))))) :=
  theorem_M1_sign p r hr hrp fl F Q c

/-- (M2), `c = p^h`. -/
theorem hM2 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QS p r Q))))) :=
  corollary_M2 p r hp hr hrp fl F Q h

end CheckCSI8

#print axioms CheckCSI8.hData
#print axioms CheckCSI8.hFS
#print axioms CheckCSI8.hM1
#print axioms CheckCSI8.hM1sign
#print axioms CheckCSI8.hM2
#print axioms ColouredSand.OddTwist.coupledCokerEquiv
#print axioms ColouredSand.OddTwist.QSsign_of_odd

end FinalCheck.CSI8

-- ======== piece CSI9 (from lean/proyecto_cubo/checks/CheckCSI9.lean) ========
namespace FinalCheck.CSI9

/-!
# CheckCSI9 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI9 (`CSI9_last_level_and_floors.md`): Part L, the last level
(Proposition 2.3) over `ℤ_[p]` and over any ring in which `1, …, d − 1` are units, with
`Mlast = Q 0 ⋯ Q (d−1)` written out as a list product; Part G: the floor `flL` written out,
`wt = λ − 2 flL`, parity, `F` raises the floor by one, the base case `Δ(λ)`, the recursive
description (twist and split), (G2) the dance lattice as a moved graded family, (G3) the
operator `F + p^e (D_fl + i)` as a one-slot system, with `Q₀` and `D_fl` written out.
Then `#print axioms`.
-/

namespace CheckCSI9

open ColouredSand.OddTwist DirectSum DPLattice
open scoped Pointwise

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- `Mlast` written out. -/
theorem hMlast {A : Type*} [CommRing A] (Q : ℕ → Matrix S S A) (d : ℕ) :
    prodQ Q 0 d = ((List.range d).map Q).prod := by
  simp [prodQ]

/-- (L1) over `ℤ_[p]`, with `Mlast` as a list product. -/
theorem hL1 (p : ℕ) [Fact p.Prime] (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1)
    (Q : ℕ → Matrix S S ℤ_[p]) (c : ℤ_[p]) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => ℤ_[p]) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta ℤ_[p] (d - 1))) Q)) ≃ₗ[ℤ_[p]]
      ((Fin (d - 1) → (S → ℤ_[p]) ⧸ c • (⊤ : Submodule ℤ_[p] (S → ℤ_[p]))) ×
        ((S → ℤ_[p]) ⧸ LinearMap.range
          (c • (p : ℤ_[p]) ^ d • (((List.range d).map Q).prod).mulVecLin)))) := by
  rw [← hMlast]
  exact L1 p d hd1 hd2 Q c

/-- (L1) over any commutative ring in which `1, …, d − 1` are units. -/
theorem hL1general {A : Type*} [CommRing A] (p d : ℕ) (hd : 1 ≤ d)
    (hu : ∀ k : ℕ, 1 ≤ k → k < d → IsUnit (k : A)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => A) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta A (d - 1))) Q)) ≃ₗ[A]
      ((Fin (d - 1) → (S → A) ⧸ c • (⊤ : Submodule A (S → A))) ×
        ((S → A) ⧸ LinearMap.range
          (c • (p : A) ^ d • (((List.range d).map Q).prod).mulVecLin)))) := by
  rw [← hMlast]
  exact L1_general p d hd hu Q c

variable (p : ℕ) [Fact p.Prime]

/-- (G1): the floor written out, `wt = λ − 2 flL`, parity, and `F` raises the floor by one. -/
theorem hG1 (l : ℕ) (i j : (danceL p l).ι) :
    flL p l i = (((l : ℤ) - (danceL p l).wt i) / 2).toNat ∧
    (danceL p l).wt i = (l : ℤ) - 2 * (flL p l i : ℤ) ∧
    (danceL p l).wt i ≡ (l : ℤ) [ZMOD 2] ∧
    ((danceL p l).Fd 1 (Pi.single i 1) j ≠ 0 → flL p l j = flL p l i + 1) :=
  ⟨rfl, wt_danceL p l i, G1_parity p l i, G1_Fd p l i j⟩

/-- (G1), vector form: a vector on floor `φ` is sent to floor `φ + 1`. -/
theorem hG1vec (l φ : ℕ) (v : (danceL p l).ι → ℤ_[p])
    (hv : ∀ i, flL p l i ≠ φ → v i = 0) (j : (danceL p l).ι) (hj : flL p l j ≠ φ + 1) :
    (danceL p l).Fd 1 v j = 0 :=
  G1_Fd_floor p l φ v hv j hj

/-- (G1): base case and recursive description. -/
theorem hG1rec (l : ℕ) :
    (∀ (h : l + 1 < p) (r : Fin (l + 1)), flL p l ((idxDelta p l h).symm r) = r.val) ∧
    (∀ (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) (j : Fin p)
        (i : (danceL p ((l + 1) / p - 1)).ι),
      flL p l ((idxTw p l h hd).symm (j, i)) = p * flL p ((l + 1) / p - 1) i + j) ∧
    (∀ (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) (j : Fin p)
        (i : (danceL p ((l + 1) / p - 1)).ι),
      flL p l ((idxPsi p l h hd).symm (false, j, i)) = p * flL p ((l + 1) / p - 1) i + j ∧
      flL p l ((idxPsi p l h hd).symm (true, j, i)) =
        p * flL p ((l + 1) / p - 1) i + (l + 1) % p + j) :=
  ⟨G1_delta p l, G1_twist p l, G1_psi p l⟩

/-- (G2): the dance lattice is the twist / split of the previous one as a graded family. -/
theorem hG2 (l : ℕ) (h : ¬ l + 1 < p) :
    (∀ hd : (l + 1) % p = 0,
      (∀ q, flL p l (eTw p l h hd q) = flT p (flL p ((l + 1) / p - 1)) q) ∧
      opDS (eTw p l h hd) ((danceL p l).Fd 1) = FT p (famF (danceL p ((l + 1) / p - 1)))) ∧
    (∀ hd : 1 ≤ (l + 1) % p,
      (∀ q, flL p l (ePsi p l h hd q) = flS p ((l + 1) % p) (flL p ((l + 1) / p - 1)) q) ∧
      opDS (ePsi p l h hd) ((danceL p l).Fd 1) =
        FS p ((l + 1) % p) hd (famF (danceL p ((l + 1) / p - 1)))) :=
  ⟨G2_twist p l h, G2_psi p l h⟩

/-- `Q₀` and `D_fl` written out. -/
theorem hQ0Dop (e i φ : ℕ) {ι : Type*} (fl : ι → ℕ) (x : ι → ℤ_[p]) (j : ι) :
    Q0 ℤ_[p] p e i φ () () = (p : ℤ_[p]) ^ (e - 1) * ((φ : ℤ_[p]) + i) ∧
    Dop fl x j = (fl j : ℤ_[p]) * x j :=
  ⟨rfl, rfl⟩

/-- (G3): `F + p^e (D_fl + i)` on `danceL p λ` is the one-slot system with `Q₀`. -/
theorem hG3 (l e i : ℕ) (he : 1 ≤ e) :
    (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap ∘ₗ
        Gp p (flL p l) (famF (danceL p l)) (Q0 ℤ_[p] p e i) =
      ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
          (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p])))) ∘ₗ
        (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap :=
  G3_operator p l e i he

end CheckCSI9

#print axioms CheckCSI9.hMlast
#print axioms CheckCSI9.hL1
#print axioms CheckCSI9.hL1general
#print axioms CheckCSI9.hG1
#print axioms CheckCSI9.hG1vec
#print axioms CheckCSI9.hG1rec
#print axioms CheckCSI9.hG2
#print axioms CheckCSI9.hQ0Dop
#print axioms CheckCSI9.hG3
#print axioms ColouredSand.OddTwist.Gp_Q0_eq
#print axioms ColouredSand.OddTwist.opDS_twist
#print axioms ColouredSand.OddTwist.opDS_psi

end FinalCheck.CSI9

-- ======== piece CSI10 (from lean/proyecto_cubo/checks/CheckCSI10.lean) ========
namespace FinalCheck.CSI10

/-!
# CheckCSI10 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI10 (`CSI10_theorem_Dp_and_theorem_I.md`): the digits of `λ + 1`, the
halved data and the matrix `Mp` written out, (M1), the slot count, Theorem D_p with `Y_p` written
out as the cokernel of `F + p^e (D_fl + i)` on `danceL p λ` and every `ℤ_[p] ⧸ p^a` written out,
and Theorem I (I1)–(I3) and its invariant form. Then `#print axioms`.
-/

namespace CheckCSI10

open ColouredSand.OddTwist DirectSum DPLattice
open scoped Pointwise

/-- The digits, the leading index and `I` written out. -/
theorem hDigits (p l t : ℕ) :
    digitL p l t = (Nat.digits p (l + 1)).getD t 0 ∧
    kTop p l = (Nat.digits p (l + 1)).length - 1 ∧
    Iset p l = (Finset.range (kTop p l)).filter (fun s => digitL p l s ≠ 0) :=
  ⟨rfl, rfl, rfl⟩

/-- The leading digit is nonzero. -/
theorem hTop (p l : ℕ) : digitL p l (kTop p l) ≠ 0 := digitL_top_ne_zero p l

variable (p : ℕ) [Fact p.Prime]

/-- The halved data and `Mp` written out: start at `(Unit, Q₀)`, one move per digit
(twist `QT` for a zero digit, split `QS` with slots `× Bool` otherwise), then
`Mp = p^{d_k} • Q_k 0 ⋯ Q_k (d_k − 1)`. -/
theorem hMp (l i e : ℕ) :
    Qdata p l i e (kTop p l) = iterD p (digitL p l) (kTop p l) ⟨Unit, Q0 ℤ_[p] p e i⟩ ∧
    (∀ (d : ℕ) (D : SData ℤ_[p]), stepD p d D =
      if d = 0 then ⟨D.S, QT p D.Q⟩ else ⟨D.S × Bool, QS p d D.Q⟩) ∧
    Mp p l i e = (p : ℤ_[p]) ^ digitL p l (kTop p l) •
      ((List.range (digitL p l (kTop p l))).map (Qdata p l i e (kTop p l)).Q).prod :=
  ⟨rfl, fun _ _ => rfl, by simp [Mp, prodQ]⟩

/-- Part M: `2^{|I|}` slots, and (M1). -/
theorem hM (l i e : ℕ) :
    Fintype.card (slots p l i e) = 2 ^ (Iset p l).card ∧
    ∀ s s' : slots p l i e,
      Mp p l i e s s' ∈ Ideal.span {(p : ℤ_[p]) ^ digitL p l (kTop p l)} :=
  ⟨card_slots p l i e, M1 p l i e⟩

/-- **Theorem D_p**, everything written out. -/
theorem hDp (hp : Odd p) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty ((((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
        (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p]))))) ≃ₗ[ℤ_[p]]
      (((t : Fin (kTop p l - 1)) →
          Fin ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ ((t : ℕ) + 1)}) ×
        (Fin ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ kTop p l}) ×
        ((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)))) :=
  theorem_Dp p hp l i e he

/-- **Theorem I**: (I1) `Y ≅ S × C`, (I2) `p^k S = 0`, (I3) `C` has `2^{|I|}` generators and
`C ⧸ p^{k+1} C ≅ (ℤ_[p] ⧸ p^{k+1})^{2^{|I|}}`, and the invariant form. -/
theorem hI (hp : Odd p) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty (Yp p l i e ≃ₗ[ℤ_[p]] (Sp p l × Cmod p l i e)) ∧
    (∀ x : Sp p l, (p : ℤ_[p]) ^ kTop p l • x = 0) ∧
    (∃ g : Fin (2 ^ (Iset p l).card) → Cmod p l i e, Submodule.span ℤ_[p] (Set.range g) = ⊤) ∧
    Nonempty ((Cmod p l i e ⧸ (p : ℤ_[p]) ^ (kTop p l + 1) • (⊤ : Submodule ℤ_[p] (Cmod p l i e)))
      ≃ₗ[ℤ_[p]] (Fin (2 ^ (Iset p l).card) →
        ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + 1)})) ∧
    Nonempty ((Yp p l i e ⧸ (p : ℤ_[p]) ^ (kTop p l + 1) • (⊤ : Submodule ℤ_[p] (Yp p l i e)))
      ≃ₗ[ℤ_[p]] (Sp p l × (Fin (2 ^ (Iset p l).card) →
        ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + 1)}))) :=
  theorem_I p hp l i e he

/-- `Y`, `S` and `C` are what the spec says. -/
theorem hDefs (l i e : ℕ) :
    Yp p l i e = (((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
        (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p]))))) ∧
    Sp p l = (((t : Fin (kTop p l - 1)) →
          Fin ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ ((t : ℕ) + 1)}) ×
        (Fin ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ kTop p l})) ∧
    Cmod p l i e = ((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)) :=
  ⟨rfl, rfl, rfl⟩

end CheckCSI10

#print axioms CheckCSI10.hDigits
#print axioms CheckCSI10.hTop
#print axioms CheckCSI10.hMp
#print axioms CheckCSI10.hM
#print axioms CheckCSI10.hDp
#print axioms CheckCSI10.hI
#print axioms CheckCSI10.hDefs
#print axioms ColouredSand.OddTwist.theorem_D_gen
#print axioms ColouredSand.OddTwist.theorem_I_invariant

end FinalCheck.CSI10

-- ======== piece CSI11 (from lean/proyecto_cubo/checks/CheckCSI11.lean) ========
namespace FinalCheck.CSI11

/-!
# CheckCSI11 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI11 (`CSI11_the_odd_deficit_law.md`): the powers and `I(ds)` written out,
(Q0) with `starMul` unfolded, (Q1)–(Q3), (D2), (D1) with the valuation `k − |Δ| − min Δ`
written out, its `δ`-form, its agreement with C10, and (D1) for `λ`. Then `#print axioms`.
-/

namespace CheckCSI11

open ColouredSand.OddTwist Finset

/-- Powers and `I(ds)` written out. -/
theorem hDefs (f : Finset ℕ → ℤ) (n : ℕ) (Δ : Finset ℕ) (ds : List ℕ) :
    starPow f 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    starPow f (n + 1) Δ = ∑ Δ₁ ∈ Δ.powerset, f Δ₁ * starPow f n (Δ \ Δ₁) ∧
    Iod ds = (range ds.length).filter (fun t => ds.getD t 0 ≠ 0) :=
  ⟨rfl, rfl, rfl⟩

/-- (Q0) written out: `q_0 = 1`, `q_{t+1} = q_t^p − [t < k ∧ d_t ≠ 0][t ∈ Δ] q_t^{p−d_t}`. -/
theorem hQ0 (p : ℕ) (ds : List ℕ) (t : ℕ) (Δ : Finset ℕ) :
    aP p ds 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    aP p ds (t + 1) Δ = starPow (aP p ds t) p Δ -
      (if t < ds.length ∧ ds.getD t 0 ≠ 0 then 1 else 0) * (if t ∈ Δ then 1 else 0) *
        starPow (aP p ds t) (p - ds.getD t 0) (Δ \ {t}) :=
  ⟨rfl, rfl⟩

/-- (Q1), (Q2), (Q3) for every `p` and every digit list. -/
theorem hQ (p : ℕ) (ds : List ℕ) (t N : ℕ) :
    (∀ Δ, aP p ds t Δ ≠ 0 → Δ ⊆ (Iod ds).filter (· < t)) ∧
    aP p ds t ∅ = 1 ∧ starPow (aP p ds t) N ∅ = 1 ∧
    ∀ Γ, starPow (aP p ds t) N Γ =
      ∑ P ∈ setPartitions Γ, (N.descFactorial P.card : ℤ) * ∏ B ∈ P, aP p ds t B :=
  ⟨fun Δ h => Q1_support p ds t Δ h, Q2_const p ds t, Q3_const p ds t N,
    fun Γ => Q3_partition p ds t N Γ⟩

/-- The partitions are the set partitions. -/
theorem hPart (Γ : Finset ℕ) :
    setPartitions Γ = Γ.powerset.powerset.filter (fun P =>
      (∀ B ∈ P, B.Nonempty) ∧ (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧ P.sup id = Γ) :=
  rfl

/-- (D2). -/
theorem hD2 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (t : ℕ) (Δ : Finset ℕ) (h : Δ.Nonempty) (hΔI : Δ ⊆ Iod ds) (ht : Δ.max' h < t) :
    aP p ds t Δ ≠ 0 ∧ padicValInt p (aP p ds t Δ) = t - Δ.card - Δ.min' h :=
  oddDef_D2 hp hodd hds t Δ h hΔI ht

/-- (D1), the odd deficit law (Lemma 4.2). -/
theorem hD1 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (dk : ℕ) (h1 : 1 ≤ dk) (h2 : dk ≤ p - 1) :
    starPow (aP p ds ds.length) dk ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iod ds →
        starPow (aP p ds ds.length) dk Δ ≠ 0 ∧
          padicValInt p (starPow (aP p ds ds.length) dk Δ) = ds.length - Δ.card - Δ.min' h :=
  oddDef_D1 hp hodd hds dk h1 h2

/-- (D1) with C3's `δ`, and the same valuation as C10's `a` at the prime `2`. -/
theorem hD1C10 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (dk : ℕ) (h1 : 1 ≤ dk) (h2 : dk ≤ p - 1) (hk : 1 ≤ ds.length) {Δ : Finset ℕ}
    (hΔ : Δ ⊆ Iod ds) :
    (padicValInt p (starPow (aP p ds ds.length) dk Δ) : ℤ) = Rulers.delta ds.length Δ ∧
    padicValInt p (starPow (aP p ds ds.length) dk Δ) =
      padicValInt 2 (Deficit.a (Iod ds) ds.length Δ) :=
  ⟨(D1_delta hp hodd hds dk h1 h2 hΔ).2, D1_indep hp hodd hds dk h1 h2 hk hΔ⟩

/-- (D1) for `λ`, digits of `λ + 1` from CSI10. -/
theorem hD1lam {p : ℕ} (hp : p.Prime) (hodd : Odd p) (l : ℕ) :
    dsL p l = (Nat.digits p (l + 1)).take (kTop p l) ∧ Iod (dsL p l) = Iset p l ∧
    (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iset p l →
        starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ ≠ 0 ∧
          padicValInt p (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ) =
            kTop p l - Δ.card - Δ.min' h) :=
  ⟨rfl, Iod_lambda p l, D1_lambda hp hodd l⟩

end CheckCSI11

#print axioms CheckCSI11.hDefs
#print axioms CheckCSI11.hQ0
#print axioms CheckCSI11.hQ
#print axioms CheckCSI11.hPart
#print axioms CheckCSI11.hD2
#print axioms CheckCSI11.hD1
#print axioms CheckCSI11.hD1C10
#print axioms CheckCSI11.hD1lam
#print axioms ColouredSand.OddTwist.Q3_partition

end FinalCheck.CSI11

-- ======== piece CSI12 (from lean/proyecto_cubo/checks/CheckCSI12.lean) ========
namespace FinalCheck.CSI12

/-!
# CheckCSI12 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI12 (`CSI12_the_odd_windows.md`): `o_D`, `π_0`, `b_h`, `x_h·f` and the
coefficients `c^{(h)}` (Part C) written out; the slot labels (A side keeps, C side adds `h`) and the
bijection with the subsets of `I ∩ [0, h)` with its three clauses written out; (W1) and (W2) with
the windows written out, and (W2) for any number `s ≥ 1` of factors; (C1) for digit lists and for
the digits of `λ + 1`. Then `#print axioms`.
-/

namespace CheckCSI12

open ColouredSand.OddTwist Finset

/-- The setting and Part C written out. -/
theorem hDefs (p e i d h : ℕ) (dg : ℕ → ℕ) (I D Δ : Finset ℕ) (f : Finset ℕ → ℚ) :
    oW p dg D = ∑ t ∈ D, dg t * p ^ t ∧
    piW p e i d = (p : ℚ) ^ e * ((i : ℚ) + d) ∧
    bW p dg h = (-1) ^ (p - dg h + 1) ∧
    xMul h f Δ = (if h ∈ Δ then f (Δ \ {h}) else 0) ∧
    cW p I dg 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    cW p I dg (h + 1) Δ = (-1 / (p : ℚ)) * starPow (cW p I dg h) p Δ +
      (if h ∈ I then 1 else 0) * ((-1) ^ (p - dg h + 1)) *
        (if h ∈ Δ then starPow (cW p I dg h) (p - dg h) (Δ \ {h}) else 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The labels: start at `∅`; a zero digit keeps the label; at a split, `(s, false)` (A side)
keeps the label of `s`, `(s, true)` (C side) adds `h`. -/
theorem hLab {A : Type*} [CommRing A] (p : ℕ) (dg : ℕ → ℕ) (D₀ : SData A) (h : ℕ) :
    (∀ x, slotLab p dg D₀ 0 x = ∅) ∧
    (∀ (hd : dg h = 0) (x : (iterD p dg (h + 1) D₀).S), slotLab p dg D₀ (h + 1) x =
      slotLab p dg D₀ h (cast (stepD_S_zero p _ hd (iterD p dg h D₀)) x)) ∧
    (∀ (hd : dg h ≠ 0) (x : (iterD p dg (h + 1) D₀).S), slotLab p dg D₀ (h + 1) x =
      (if (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).2 then
        insert h (slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1)
      else slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1)) :=
  ⟨fun _ => rfl, fun hd x => slotLab_succ_zero p dg D₀ h hd x,
    fun hd x => slotLab_succ_pos p dg D₀ h hd x⟩

variable (p : ℕ) [hp : Fact p.Prime]

/-- Slots as subsets, the three clauses written out. -/
theorem hSlots (l i e h : ℕ) (hh : h ≤ kTop p l) :
    labL p l i e h = slotLab p (digitL p l) ⟨Unit, Q0 ℤ_[p] p e i⟩ h ∧
    (∀ x, labL p l i e h x ⊆ (Iset p l).filter (· < h)) ∧
    Function.Injective (labL p l i e h) ∧
    (∀ E ⊆ (Iset p l).filter (· < h), ∃ x, labL p l i e h x = E) :=
  let H := slots_as_subsets p l i e h hh
  ⟨rfl, H.sub, H.inj, H.surj⟩

/-- **(W1)** written out. -/
theorem hW1 (l i e h : ℕ) (he : 1 ≤ e) (hh : h ≤ kTop p l) (f : ℕ)
    (x y : (Qdata p l i e h).S) :
    (((p : ℤ_[p]) * (Qdata p l i e h).Q f x y : ℤ_[p]) : ℚ_[p]) =
      ((if labL p l i e h y ⊆ labL p l i e h x then
          cW p (Iset p l) (digitL p l) h (labL p l i e h x \ labL p l i e h y) *
            ∏ d ∈ Icc (p ^ h * f + ∑ t ∈ labL p l i e h x, digitL p l t * p ^ t)
              (p ^ h * f + ∑ t ∈ labL p l i e h y, digitL p l t * p ^ t + p ^ h - 1),
              (p : ℚ) ^ e * ((i : ℚ) + d)
        else 0 : ℚ) : ℚ_[p]) := by
  have := W1_windows p l i e h he hh f x y
  simpa [Matrix.smul_apply, smul_eq_mul, oW, piW] using this

/-- **(W2)** written out (`K = d_k p^k`). -/
theorem hW2 (l i e : ℕ) (he : 1 ≤ e) (x y : slots p l i e) :
    (Mp p l i e x y : ℚ_[p]) =
      ((if labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x then
          starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l))
              (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y) *
            ∏ d ∈ Icc (∑ t ∈ labL p l i e (kTop p l) x, digitL p l t * p ^ t)
              (∑ t ∈ labL p l i e (kTop p l) y, digitL p l t * p ^ t +
                digitL p l (kTop p l) * p ^ kTop p l - 1), (p : ℚ) ^ e * ((i : ℚ) + d)
        else 0 : ℚ) : ℚ_[p]) :=
  W2_Mp p l i e he x y

/-- **(W2)** for any level `h ≤ k` and any number `s ≥ 1` of factors. -/
theorem hW2s (l i e h s : ℕ) (he : 1 ≤ e) (hh : h ≤ kTop p l) (hs : 1 ≤ s)
    (x y : (Qdata p l i e h).S) :
    ((((p : ℤ_[p]) ^ s • prodQ (Qdata p l i e h).Q 0 s) x y : ℤ_[p]) : ℚ_[p]) =
      ((if labL p l i e h y ⊆ labL p l i e h x then
          starPow (cW p (Iset p l) (digitL p l) h) s (labL p l i e h x \ labL p l i e h y) *
            ∏ d ∈ Icc (oW p (digitL p l) (labL p l i e h x))
              (oW p (digitL p l) (labL p l i e h y) + s * p ^ h - 1), piW p e i d
        else 0 : ℚ) : ℚ_[p]) :=
  W2_gen PadicInt.Coe.ringHom p (digitL p l) (Iset p l) e i hp.out.two_le he h
    (fun t _ => digitL_lt hp.out l t) (fun t ht => mem_Iset_iff p l t (by omega)) s hs x y

end CheckCSI12

namespace CheckCSI12

open ColouredSand.OddTwist Finset

/-- **(C1)** for digit lists (CSI11's `ds`, `I = Iod ds`). -/
theorem hC1 {p : ℕ} (hp : 2 ≤ p) (ds : List ℕ) (hds : ∀ d ∈ ds, d < p) (h : ℕ) (Δ : Finset ℕ) :
    cW p (Iod ds) (fun t => ds.getD t 0) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p ds h Δ : ℚ) *
        ∏ t ∈ Δ, (-((-1 : ℚ) ^ (p - ds.getD t 0 + 1)) *
          (-(p : ℚ)) ^ (1 + ds.getD t 0 * ((p ^ t - 1) / (p - 1)))) :=
  C1_rescaling hp ds hds h Δ

/-- **(C1)** for the digits of `λ + 1`. -/
theorem hC1lam {p : ℕ} (hp : p.Prime) (l h : ℕ) (Δ : Finset ℕ) :
    cW p (Iset p l) (digitL p l) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p (dsL p l) h Δ : ℚ) *
        ∏ t ∈ Δ, (-((-1 : ℚ) ^ (p - digitL p l t + 1)) *
          (-(p : ℚ)) ^ (1 + digitL p l t * ((p ^ t - 1) / (p - 1)))) :=
  C1_lambda hp l h Δ

end CheckCSI12

#print axioms CheckCSI12.hDefs
#print axioms CheckCSI12.hLab
#print axioms CheckCSI12.hSlots
#print axioms CheckCSI12.hW1
#print axioms CheckCSI12.hW2
#print axioms CheckCSI12.hW2s
#print axioms CheckCSI12.hC1
#print axioms CheckCSI12.hC1lam
#print axioms ColouredSand.OddTwist.W1_gen
#print axioms ColouredSand.OddTwist.W2_gen

end FinalCheck.CSI12

-- ======== piece CSI13 (from lean/proyecto_cubo/checks/CheckCSI13.lean) ========
namespace FinalCheck.CSI13

/-!
# CheckCSI13 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI13 (`CSI13_the_odd_cost_form.md`): `s_p`, `κ_p` and the two rulers
written out; Kummer; Part L (L1 Legendre and its two sums, L2, L3, L4); Part P (P1 for `i ≥ 1`
and `i = 0`; P2: support, `i ≥ 1`, the zero row and `i = 0`, each with the non-vanishing).
Then `#print axioms`.
-/

namespace CheckCSI13

open ColouredSand.OddTwist Finset

/-- The setting written out: digit sum, carries, the rulers. -/
theorem hDefs (p e k μ x a b : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) :
    sP p x = (Nat.digits p x).sum ∧
    kappaP p a b = (((sP p a : ℤ) + sP p b) - sP p (a + b)) / ((p : ℤ) - 1) ∧
    rulerP p e k I dg μ E =
      ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p μ (oW p dg E) ∧
    rulerSharpP p e k I dg E = (if E = ∅ then 0 else
      ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - ((k : ℤ) - Rulers.minOr k E)) :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {p : ℕ} [Fact p.Prime]

/-- Kummer: `κ_p(a, b) = v_p C(a+b, a)`. -/
theorem hKummer (a b : ℕ) : kappaP p a b = padicValNat p ((a + b).choose a) :=
  kappaP_eq_padicValNat_choose a b

/-- (L1) Legendre in base `p`, and its two sums. -/
theorem hL1 (n μ x y : ℕ) (hxy : x ≤ y) (hx : 1 ≤ x) :
    (padicValNat p n.factorial : ℚ) = ((n : ℚ) - sP p n) / ((p : ℚ) - 1) ∧
    ∑ d ∈ Ico x y, (padicValNat p (μ + 1 + d) : ℚ) =
      (((y : ℚ) - x) - sP p (μ + y) + sP p (μ + x)) / ((p : ℚ) - 1) ∧
    ∑ d ∈ Ico x y, (padicValNat p d : ℚ) =
      (((y : ℚ) - x) - sP p (y - 1) + sP p (x - 1)) / ((p : ℚ) - 1) :=
  ⟨L1_legendre n, L1_sum μ x y hxy, L1_sum_neg x y hx hxy⟩

/-- (L2). -/
theorem hL2 (dg : ℕ → ℕ) (E : Finset ℕ) (hd : ∀ t ∈ E, dg t < p) (x : ℕ) :
    (sP p (x + oW p dg E) : ℤ) =
      sP p x + ∑ t ∈ E, (dg t : ℤ) - ((p : ℤ) - 1) * kappaP p x (oW p dg E) :=
  L2 dg E hd x

/-- (L3). -/
theorem hL3 (k dk : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hne : E.Nonempty) (hE : E ⊆ I) :
    sP p (dk * p ^ k) = dk ∧
    kappaP p (dk * p ^ k - 1) (oW p dg E) = (k : ℤ) - E.min' hne :=
  ⟨L3_sP_K k dk hdk, L3_kappa hI hd hdk1 hdk hne hE⟩

/-- (L4) = C3's `lemma_5_1_a`. -/
theorem hL4 (k : ℕ) (I a b : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hba : b ⊆ a) (ha : a ⊆ I) :
    ((a \ b).card : ℤ) + Rulers.delta k (a \ b) =
      ∑ t ∈ a, (Rulers.h k I t : ℤ) - ∑ t ∈ b, (Rulers.h k I t : ℤ) +
        Rulers.gamma k I (a \ b) :=
  L4 hI hba ha

/-- (P1), `i ≥ 1`. -/
theorem hP1 (k dk e i : ℕ) (I a b : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hba : b ⊆ a) (ha : a ⊆ I) (hi : 1 ≤ i) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p (i + d) : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + kappaP p (i - 1) (dk * p ^ k) + rulerP p e k I dg (i - 1) a -
        rulerP p e k I dg (i - 1 + dk * p ^ k) b + Rulers.gamma k I (a \ b) :=
  oddRul_P1 hI hd hdk1 hdk hba ha e i hi

/-- (P1), `i = 0`, `a ≠ ∅`. -/
theorem hP1zero (k dk e : ℕ) (I a b : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hba : b ⊆ a) (ha : a ⊆ I) (hne : a.Nonempty) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p d : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + rulerSharpP p e k I dg a - rulerSharpP p e k I dg b +
        Rulers.gamma k I (a \ b) :=
  P1_zero hI hd hdk1 hdk hba ha hne e

/-- (P2): support, `i ≥ 1`, zero row, `i = 0`. -/
theorem hP2 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) (x y : slots p l i e)
    (x0 y0 : slots p l 0 e) :
    (¬ labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x → Mp p l i e x y = 0) ∧
    (labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x →
      Mp p l i e x y ≠ 0 ∧
      ((Mp p l i e x y).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          kappaP p (i - 1) (digitL p l (kTop p l) * p ^ kTop p l) +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (labL p l i e (kTop p l) x) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l)
            (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) (labL p l i e (kTop p l) y) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y)) ∧
    (labL p l 0 e (kTop p l) x0 = ∅ → Mp p l 0 e x0 y0 = 0) ∧
    (labL p l 0 e (kTop p l) x0 ≠ ∅ →
      labL p l 0 e (kTop p l) y0 ⊆ labL p l 0 e (kTop p l) x0 →
      Mp p l 0 e x0 y0 ≠ 0 ∧
      ((Mp p l 0 e x0 y0).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) x0) -
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) y0) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l 0 e (kTop p l) x0 \ labL p l 0 e (kTop p l) y0)) :=
  ⟨P2_support p l i e he x y, P2_pos p hodd l i e he hi x y, P2_zero_row p l e he x0 y0,
    fun hx hba => P2_zero p hodd l e he x0 y0 hx hba⟩

end CheckCSI13

#print axioms CheckCSI13.hDefs
#print axioms CheckCSI13.hKummer
#print axioms CheckCSI13.hL1
#print axioms CheckCSI13.hL2
#print axioms CheckCSI13.hL3
#print axioms CheckCSI13.hL4
#print axioms CheckCSI13.hP1
#print axioms CheckCSI13.hP1zero
#print axioms CheckCSI13.hP2

end FinalCheck.CSI13

-- ======== piece CSI14 (from lean/proyecto_cubo/checks/CheckCSI14.lean) ========
namespace FinalCheck.CSI14

/-!
# CheckCSI14 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI14 (`CSI14_the_ceiling_at_p.md`): the definitions written out (oP, ranks,
Lr/Fr at p, ĉ, x_D, U, minorValsP, ddP); Part A (A1, A2, A3, Theorem O at p); Part B (B1);
Part C (C1); Part D (D0–D3); Part Q (Q1, Q2); Part T (T1). Then `#print axioms`.
-/

namespace CheckCSI14

open ColouredSand.OddTwist Finset Matrix

theorem hDefs (p k r : ℕ) (d : ℕ → ℕ) (I D a b : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) :
    oP p d D = ∑ t ∈ D, d t * p ^ t ∧
    rankP p d I D = #(I.powerset.filter (fun D' => oP p d D' < oP p d D)) ∧
    LrP p d I r = I.powerset.filter (fun D => 2 ^ #I - r ≤ rankP p d I D) ∧
    FrP p d I r = I.powerset.filter (fun D => rankP p d I D < r) ∧
    cHatP k I R₁ R₂ a b = R₁ a - R₂ b + Rulers.gamma k I (a \ b) ∧
    xP I R₁ R₂ D = R₁ D - R₂ (I \ D) ∧
    UP I R₁ R₂ r = ∑ D ∈ GoldenMatching.Lr I r, (R₁ D - R₂ (I \ D)) ∧
    minorValsP p M r = {v | ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧
      Divisors.minor M r A B ≠ 0 ∧ padicValInt p (Divisors.minor M r A B) = v} ∧
    ddP p M r = sInf (minorValsP p M r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hA (k : ℕ) {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I)
    (r : ℕ) (hr : r ≤ 2 ^ #I) :
    (oP p d D < oP p d D' ↔ Rulers.oE D < Rulers.oE D') ∧
    rankP p d I D = GoldenMatching.rank I D ∧
    LrP p d I r = GoldenMatching.Lr I r ∧ FrP p d I r = GoldenMatching.Fr I r ∧
    oP p d (I \ D) + oP p d D = oP p d I ∧
    (∃ β : LrP p d I r ≃ FrP p d I r,
        ∀ D : LrP p d I r, GoldenMatching.IsGoldenArrow k I D (β D)) :=
  ⟨A1_same_order hp hd hD hD', A2_rank hp hd hD, A2_Lr hp hd r, A2_Fr hp hd r,
    A3_complement p d hD, (theorem_O_P k hp hI hd r hr).1⟩

theorem hB (k : ℕ) (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (r : ℕ)
    (β : GoldenMatching.Lr I r ≃ GoldenMatching.Fr I r) :
    ∑ D : GoldenMatching.Lr I r, cHatP k I R₁ R₂ D (β D) =
      UP I R₁ R₂ r + ∑ D : GoldenMatching.Lr I r, (Rulers.gamma k I ((D : Finset ℕ) \ β D) : ℤ) :=
  B1_cost k I R₁ R₂ r β

theorem hC (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (R₁ R₂ : Finset ℕ → ℤ) {p : ℕ} (hp : p.Prime) (C : ℤ) (M : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + cHatP k I R₁ R₂ a b ∧
      (p : ℤ) ^ n ∣ M a b ∧ ¬ (p : ℤ) ^ (n + 1) ∣ M a b)
    (r : ℕ) (hr : r ≤ 2 ^ #I) (e : Fin r ≃ GoldenMatching.Lr I r)
    (f : Fin r ≃ GoldenMatching.Fr I r) :
    ∃ n : ℕ, (n : ℤ) = r * C + UP I R₁ R₂ r ∧
      (p : ℤ) ^ n ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      ¬ (p : ℤ) ^ (n + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      (Matrix.of fun i j => M (e i) (f j)).det ≠ 0 :=
  C1_natural_minor k hI R₁ R₂ hp C M hS hH r hr e f

theorem hD {p : ℕ} (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (r : ℕ)
    (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) (hr : r ≤ n)
    (hD : P * M * Q = diagonal fun i => u i * (p : ℤ) ^ e i) (s : Fin n) (hr2 : r + 2 ≤ n) :
    ddP 2 M r = Divisors.dd M r ∧
    ddP p (P * M * Q) r = ddP p M r ∧
    ddP p (diagonal fun i => u i * (p : ℤ) ^ e i) r =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i ∧
    ddP p M r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i ∧
    (e s : ℤ) = (ddP p M (s + 1) : ℤ) - ddP p M s ∧
    (ddP p M (r + 1) : ℤ) - ddP p M r ≤ (ddP p M (r + 2) : ℤ) - ddP p M (r + 1) :=
  ⟨D0_two M r, D1_invariance hp M P Q hP hQ r, D2_diagonal hp e he u hu hr,
    D3_sum hp M P Q hP hQ e he u hu hD hr, D3_increment hp M P Q hP hQ e he u hu hD s,
    D3_convex hp M P Q hP hQ e he u hu hD r hr2⟩

theorem hQ1 {p : ℕ} (hp : p.Prime) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧
      ∃ ρ ≤ n, ∃ e : ℕ → ℕ, (∀ i j, i ≤ j → j < ρ → e i ≤ e j) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
          P * A * Q = diagonal (fun j : Fin n =>
            if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) :=
  Q1_smith hp n A

theorem hQ2 {p n ρ : ℕ} {e : ℕ → ℕ} {u : ℕ → ℤ} (hp : p.Prime)
    (A P Q : Matrix (Fin n) (Fin n) ℤ) (hP : ¬ (p : ℤ) ∣ P.det)
    (hQ : ¬ (p : ℤ) ∣ Q.det) (hρ : ρ ≤ n) (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ u j)
    (hD : P * A * Q = diagonal (fun j : Fin n =>
      if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0)) :
    (∀ r ≤ ρ, ddP p A r = ∑ j ∈ range r, e j) ∧
      (∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
        Divisors.minor A r B C = 0) ∧
      (A.det ≠ 0 ↔ ρ = n) :=
  Q2_smith hp A P Q hP hQ hρ he hu hD

theorem hT {p : ℕ} (hp : p.Prime) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : A.det ≠ 0) (x : ℕ → ℤ) (C : ℤ)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤ (ddP p A r : ℤ) - r * C)
    (hU : ∀ r ≤ N, (ddP p A r : ℤ) - r * C ≤ ∑ j ∈ Ico (N - r) N, x j) :
    (∀ r ≤ N, (ddP p A r : ℤ) = r * C + ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j) ∧
      ∀ (P Q : Matrix (Fin N) (Fin N) ℤ) (ρ : ℕ) (e : ℕ → ℕ) (u : ℕ → ℤ),
        ¬ (p : ℤ) ∣ P.det → ¬ (p : ℤ) ∣ Q.det → ρ ≤ N →
        (∀ i j, i ≤ j → j < ρ → e i ≤ e j) → (∀ j, ¬ (p : ℤ) ∣ u j) →
        P * A * Q = diagonal (fun j : Fin N =>
          if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) →
        ρ = N ∧ ∀ j < N, (e j : ℤ) = C + AntitonicFit.ifit N x (N - 1 - j) :=
  T1_assembly hp A hA x C hF hU

end CheckCSI14

#print axioms CheckCSI14.hDefs
#print axioms CheckCSI14.hA
#print axioms CheckCSI14.hB
#print axioms CheckCSI14.hC
#print axioms CheckCSI14.hD
#print axioms CheckCSI14.hQ1
#print axioms CheckCSI14.hQ2
#print axioms CheckCSI14.hT

end FinalCheck.CSI14

-- ======== piece CSI15 (from lean/proyecto_cubo/checks/CheckCSI15.lean) ========
namespace FinalCheck.CSI15

/-!
# CheckCSI15 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI15 (`CSI15_houses_at_p.md`): the definitions written out (digits, r_u,
R_H, J_H, x_H, ĉ_H, c_u, car_t, θ, κ, sat, type, τ, firing, d_1) and the agreement with CSI13's
ruler; Part A (A0–A3) with R_H, J_H, r_k written out; Part B (B1–B6); Part C (C1–C7).
Then `#print axioms`.
-/

namespace CheckCSI15

open ColouredSand.OddTwist Finset

theorem hDefs (p k ℓ u x t c : ℕ) (I E a b D₀ : Finset ℕ) (dg : ℕ → ℕ) (e : ℤ) :
    digP p u x = x / p ^ u % p ∧
    rP p u x = padicValNat p (x / p ^ u + 1) ∧
    RHP p k I dg ℓ e E = ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t)
        - kappaP p ℓ (∑ t ∈ E, dg t * p ^ t) ∧
    JHP p k dg ℓ E = (if p ^ k ≤ ℓ + ∑ t ∈ E, dg t * p ^ t then 1 else 0) ∧
    xHP p k I dg ℓ e E = RHP p k I dg ℓ e E - RHP p k I dg ℓ e (I \ E) ∧
    cHatHP p k I dg ℓ e a b = RHP p k I dg ℓ e a - RHP p k I dg ℓ e b
        + (Rulers.gamma k I (a \ b) : ℤ) ∧
    cinP p dg ℓ u E =
      (if p ^ u ≤ ℓ % p ^ u + (∑ t ∈ E, dg t * p ^ t) % p ^ u then 1 else 0) ∧
    carP p k I dg ℓ t E =
      ((Ico t (Rulers.next k I t)).filter (fun v => cinP p dg ℓ (v + 1) E = 1)).card ∧
    thetaP p ℓ t = p - (ℓ / p ^ t % p) ∧
    kapP p k I ℓ t = 1 + min (padicValNat p (ℓ / p ^ (t + 1) + 1)) (Rulers.h k I t - 1) ∧
    satP p k I ℓ t = (if kapP p k I ℓ t = Rulers.h k I t then 1 else 0) ∧
    typP p dg ℓ t = (if thetaP p ℓ t = 1 then .OR
      else if thetaP p ℓ t ≤ dg t then .DIG
      else if thetaP p ℓ t = dg t + 1 then .AND else .NEV) ∧
    tauP p k I dg ℓ e t = (Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t -
      (if typP p dg ℓ t = .OR ∨ typP p dg ℓ t = .DIG then (kapP p k I ℓ t : ℤ) else 0) ∧
    d1P p k I dg ℓ e c D₀ = -tauP p k I dg ℓ e c
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀
      + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHP p c dg (ℓ % p ^ c) (I.erase c \ D₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The four firing conditions of (B2), case by case. -/
theorem hFires (p ℓ t : ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) :
    (typP p dg ℓ t = .OR → (firesP p dg ℓ t E ↔ t ∈ E ∨ cinP p dg ℓ t E = 1)) ∧
    (typP p dg ℓ t = .DIG → (firesP p dg ℓ t E ↔ t ∈ E)) ∧
    (typP p dg ℓ t = .AND → (firesP p dg ℓ t E ↔ t ∈ E ∧ cinP p dg ℓ t E = 1)) ∧
    (typP p dg ℓ t = .NEV → ¬ firesP p dg ℓ t E) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [firesP, h]

theorem hRuler (p k ℓ e : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) :
    RHP p k I dg ℓ (e : ℤ) E = rulerP p e k I dg ℓ E := RHP_eq_rulerP p k I dg ℓ e E

theorem hrP {p : ℕ} [Fact p.Prime] (u x j : ℕ) :
    j ≤ rP p u x ↔ ∀ i < j, x / p ^ (u + i) % p = p - 1 := rP_spec u x j

/-- (A0)–(A3), with `R_μ`, `J_H`, `r_k` written out in (A1). -/
theorem hA {p : ℕ} [Fact p.Prime] {k : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (ℓ μ dk m : ℕ)
    (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1) {D E F a b : Finset ℕ} (hD : D ⊆ I) (hE : E ⊆ I)
    (ha : a ⊆ I) (hb : b ⊆ I) :
    xHP p k I dg ℓ e (I \ D) = -xHP p k I dg ℓ e D ∧
    (oW p dg E ≤ oW p dg F → JHP p k dg ℓ E ≤ JHP p k dg ℓ F) ∧
    (∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p μ (∑ t ∈ E, dg t * p ^ t)
      = (∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t)
          - kappaP p (μ % p ^ k) (∑ t ∈ E, dg t * p ^ t))
        - (padicValNat p (μ / p ^ k + 1) : ℤ) *
          ((if p ^ k ≤ μ % p ^ k + ∑ t ∈ E, dg t * p ^ t then 1 else 0 : ℕ) : ℤ)) ∧
    (m + dk * p ^ k) % p ^ k = m % p ^ k ∧
    (rP p k m = 0 ∨ rP p k (m + dk * p ^ k) = 0) ∧
    RHP p k I dg m e a - RHP p k I dg (m + dk * p ^ k) e b + Rulers.gamma k I (a \ b) =
      cHatHP p k I dg (m % p ^ k) e a b - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) a
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) b ∧
    RHP p k I dg m e D - RHP p k I dg (m + dk * p ^ k) e (I \ D) =
      xHP p k I dg (m % p ^ k) e D - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) D
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) (I \ D) :=
  ⟨houseP_A0_antisymm (p := p) (k := k) (dg := dg) ℓ e hD, fun h => houseP_A0_upset ℓ h,
    houseP_A1 hI hd e μ hE, houseP_A2_residue p k dk m, houseP_A2_at_most_one k dk m hdk1 hdk,
    houseP_A3_cost hI hd e dk m ha hb, houseP_A3_clock hI hd e dk m hD⟩

theorem hA2rem (k m : ℕ) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    Xor' (rP 2 k m = 0) (rP 2 k (m + 1 * 2 ^ k) = 0) ∧
    (rP p k 0 = 0 ∧ rP p k (0 + 1 * p ^ k) = 0) :=
  ⟨houseP_A2_two k m, houseP_A2_both_zero hp3 k⟩

open Classical in
/-- (B1)–(B6). -/
theorem hB {p : ℕ} [Fact p.Prime] {k ℓ : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (e : ℤ)
    {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    (∀ hne : I.Nonempty, cinP p dg ℓ (I.min' hne) E = 0) ∧
    carP p k I dg ℓ t E = (if firesP p dg ℓ t E then kapP p k I ℓ t else 0) ∧
    (firesP p dg ℓ t E ↔ thetaP p ℓ t ≤ (if t ∈ E then 1 else 0) * dg t + cinP p dg ℓ t E) ∧
    (cinP p dg ℓ (Rulers.next k I t) E = 1 ↔ 0 < carP p k I dg ℓ t E ∧ satP p k I ℓ t = 1) ∧
    kappaP p ℓ (∑ s ∈ E, dg s * p ^ s) = ∑ s ∈ I, (carP p k I dg ℓ s E : ℤ) ∧
    RHP p k I dg ℓ e E = ∑ s ∈ E, tauP p k I dg ℓ e s
      - ∑ s ∈ I, (kapP p k I ℓ s : ℤ) * (cinP p dg ℓ s E : ℤ) *
          (if (typP p dg ℓ s = .OR ∧ s ∉ E) ∨ (typP p dg ℓ s = .AND ∧ s ∈ E) then 1 else 0) ∧
    JHP p k dg ℓ E = cinP p dg ℓ k E :=
  ⟨fun hne => houseP_B1 hd hne hE, houseP_B2 hI hd hE ht, houseP_B2_fires_iff hd ht,
    houseP_B3 hI hd hE ht, houseP_B4 hI hd hℓ hE, houseP_B5 hI hd hℓ e hE, houseP_B6 hI hd hℓ hE⟩

/-- (C1)–(C7), `c = max I`, `H' = (I ∖ {c}, c, ℓ mod p^c, e, d)`. -/
theorem hC {p : ℕ} [Fact p.Prime] {k ℓ c : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (e : ℤ)
    (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ Δ : Finset ℕ} (hD : D₀ ⊆ I.erase c)
    (hΔ : Δ ⊆ I) (hcΔ : c ∉ Δ) (hΔne : Δ ≠ ∅) :
    RHP p k I dg ℓ e D₀ = RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀ ∧
    RHP p k I dg ℓ e (D₀ ∪ {c}) = tauP p k I dg ℓ e c + RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀ ∧
    JHP p k dg ℓ D₀ =
      (if typP p dg ℓ c = .OR then 1 else 0) * satP p k I ℓ c * JHP p c dg (ℓ % p ^ c) D₀ ∧
    JHP p k dg ℓ (D₀ ∪ {c}) = satP p k I ℓ c *
      ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then 1 else 0) +
        (if typP p dg ℓ c = .AND then 1 else 0) * JHP p c dg (ℓ % p ^ c) D₀) ∧
    Rulers.gamma k I Δ = Rulers.gamma c (I.erase c) Δ + (k - c) ∧
    Rulers.gamma k I (D₀ ∪ {c}) = Rulers.gamma c (I.erase c) D₀ ∧
    xHP p k I dg ℓ e D₀ = xHP p c (I.erase c) dg (ℓ % p ^ c) e D₀ + d1P p k I dg ℓ e c D₀ ∧
    xHP p k I dg ℓ e (D₀ ∪ {c}) =
      -(xHP p c (I.erase c) dg (ℓ % p ^ c) e (I.erase c \ D₀) +
        d1P p k I dg ℓ e c (I.erase c \ D₀)) :=
  ⟨houseP_C1 hI hd hℓ e hne hc hD, houseP_C2 hI hd hℓ e hne hc hD, houseP_C3 hI hd hℓ hne hc hD,
    houseP_C4 hI hd hℓ hne hc hD, houseP_C5_not_mem hI hne hc hΔ hcΔ hΔne,
    houseP_C5_mem hI hne hc hD, houseP_C6 hI hd hℓ e hne hc hD, houseP_C7 hI hd hℓ e hne hc hD⟩

end CheckCSI15

#print axioms CheckCSI15.hDefs
#print axioms CheckCSI15.hFires
#print axioms CheckCSI15.hRuler
#print axioms CheckCSI15.hrP
#print axioms CheckCSI15.hA
#print axioms CheckCSI15.hA2rem
#print axioms CheckCSI15.hB
#print axioms CheckCSI15.hC

end FinalCheck.CSI15

-- ======== piece CSI16 (from lean/proyecto_cubo/checks/CheckCSI16.lean) ========
namespace FinalCheck.CSI16

/-!
# CheckCSI16 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI16 (`CSI16_theorem_F_at_p.md`): the definitions written out (the base-p
sequences on dancers, the walk, (Λ_p), (Cut), ŷ, ĉ, the potential, X_1, v', the flat); Theorem
F1_p with x_H written out; (P4) with its two bounds; Lemma N; Theorem F_p and Corollary F′_p;
Part Δ step 1; and the three long statements (F0, Lemma P, Lemma F) by name. Then `#print axioms`.
-/

namespace CheckCSI16

open ColouredSand.OddTwist Finset AntitonicFit TheoremF

theorem hDefs (p k ℓ c q q' f : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (e cF : ℤ) (V' : ℕ → ℤ) :
    xHseqP p k I dg ℓ e q = xHP p k I dg ℓ e (dancer I q) ∧
    JHseqP p k I dg ℓ q = JHP p k dg ℓ (dancer I q) ∧
    dWalkP p k I dg ℓ e c q = d1P p k I dg ℓ e c (dancer (I.erase c) q) ∧
    yhatP p k I dg ℓ e = ifit (2 ^ #I) (xHseqP p k I dg ℓ e) ∧
    cHatSeqP p k I dg ℓ e q q' = cHatHP p k I dg ℓ e (dancer I q) (dancer I q') ∧
    X1P p k I dg ℓ e c q = yhatP p c (I.erase c) dg (ℓ % p ^ c) e q + dWalkP p k I dg ℓ e c q ∧
    vPrimeP p k I dg ℓ e c V' q = (if q < 2 ^ #(I.erase c) then
        V' q - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) q
      else tauP p k I dg ℓ e c + V' (q - 2 ^ #(I.erase c)) -
        (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) (q - 2 ^ #(I.erase c))) ∧
    flatVP p k I dg ℓ e c V' f cF q =
      (if f ≤ q ∧ q ≤ 2 ^ #I - 1 - f then cF else vPrimeP p k I dg ℓ e c V' q) ∧
    (LamPropP p k I dg ℓ e ↔
      ∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * (oW p dg I : ℤ)) ∧
    (CutPropP p k I dg ℓ e ↔ ∀ b < 2 ^ #I, JHseqP p k I dg ℓ b = 1 →
      (∀ q < b, JHseqP p k I dg ℓ q = 0) →
        IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b ∧
          IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (2 ^ #I - b)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, Iff.rfl⟩

theorem hPot (p k ℓ : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (e : ℤ) (V : ℕ → ℤ) :
    IsPotentialP p k I dg ℓ e V ↔
      (∀ q < 2 ^ #I, V q - V (2 ^ #I - 1 - q) = yhatP p k I dg ℓ e q) ∧
      (∀ q q', q ≤ q' → q' < 2 ^ #I → V q' ≤ V q) ∧
      (∀ q q', Potential.IsArrow I q q' → V q - V q' ≤
        cHatHP p k I dg ℓ e (dancer I q) (dancer I q')) :=
  ⟨fun h => ⟨h.E, h.M, h.G⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Theorem F1_p, with `x_H` written out on the dancers. -/
theorem hF1 {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, |ifit (2 ^ #I) (fun j => xHP p k I dg ℓ e (dancer I j)) q| ≤
        e * ((∑ t ∈ I, dg t * p ^ t : ℕ) : ℤ)) ∧
    (∀ b < 2 ^ #I, JHP p k dg ℓ (dancer I b) = 1 → (∀ q < b, JHP p k dg ℓ (dancer I q) = 0) →
      IsStrictCut (2 ^ #I) (fun j => (xHP p k I dg ℓ e (dancer I j) : ℝ)) b ∧
        IsStrictCut (2 ^ #I) (fun j => (xHP p k I dg ℓ e (dancer I j) : ℝ)) (2 ^ #I - b)) ∧
    (oW p dg I : ℤ) ≤ (p : ℤ) ^ k - 1 :=
  ⟨(oddF_theorem_F1 hI hd hℓ he).1, (oddF_theorem_F1 hI hd hℓ he).2,
    (oddF_F1_Lambda_pow hI hd hℓ he).1⟩

/-- (P4): the junction step and its two bounds `≤ h − e(d_c p^c − o_{I'}) ≤ h − e`. -/
theorem hP4 {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ c : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c)) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1) =
      -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ∧
    -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤
      ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ∧
    ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ≤
      ((k - c : ℕ) : ℤ) - e :=
  oddF_P4 hI hd he hne hc hV'

/-- Lemma N: no flat ⟹ `v'` is a potential. -/
theorem hN {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ c : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k)
    (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V')
    (hX : 0 < X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1)) :
    IsPotentialP p k I dg ℓ e (vPrimeP p k I dg ℓ e c V') :=
  oddF_lemma_N hI hd hℓ he hne hc hV' hX

/-- Theorem F_p and Corollary F′_p (subsets, base-p o-order). -/
theorem hT {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∃ V : ℕ → ℤ, IsPotentialP p k I dg ℓ e V) ∧
    ∃ W : Finset ℕ → ℤ,
      (∀ D, D ⊆ I → W D - W (I \ D) = yhatP p k I dg ℓ e (GoldenMatching.rank I D)) ∧
      (∀ E F, E ⊆ I → F ⊆ I → (∑ t ∈ E, dg t * p ^ t) ≤ (∑ t ∈ F, dg t * p ^ t) → W F ≤ W E) ∧
      (∀ a b, a ⊆ I → b ⊆ I → b ⊂ a → W a - W b ≤
        RHP p k I dg ℓ e a - RHP p k I dg ℓ e b + Rulers.gamma k I (a \ b)) :=
  ⟨oddF_theorem_F hI hd hℓ he, oddF_corollary_F' hI hd hℓ he⟩

/-- Part Δ step 1: `d_1 ≤ e d_c p^c` and `X_1 ≤ e·o_I`. -/
theorem hDelta {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) (q : ℕ) (hq : q < 2 ^ #(I.erase c)) :
    dWalkP p k I dg ℓ e c q ≤ e * dg c * (p : ℤ) ^ c ∧
    X1P p k I dg ℓ e c q ≤ e * (oW p dg I : ℤ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := oddF_delta_step1 hI hd he hne hc q hq
  exact ⟨by linarith, by linarith⟩

end CheckCSI16

#check @ColouredSand.OddTwist.oddF_theorem_F0
#check @ColouredSand.OddTwist.oddF_lemma_P
#check @ColouredSand.OddTwist.oddF_lemma_X
#check @ColouredSand.OddTwist.oddF_lemma_F
#print axioms CheckCSI16.hDefs
#print axioms CheckCSI16.hPot
#print axioms CheckCSI16.hF1
#print axioms CheckCSI16.hP4
#print axioms CheckCSI16.hN
#print axioms CheckCSI16.hT
#print axioms CheckCSI16.hDelta
#print axioms ColouredSand.OddTwist.oddF_theorem_F0
#print axioms ColouredSand.OddTwist.oddF_lemma_P
#print axioms ColouredSand.OddTwist.oddF_lemma_X
#print axioms ColouredSand.OddTwist.oddF_lemma_F

end FinalCheck.CSI16

-- ======== piece CSI17 (from lean/proyecto_cubo/checks/CheckCSI17.lean) ========
namespace FinalCheck.CSI17

/-!
# CheckCSI17 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI17 (`CSI17_integrality_and_cell_floor_at_p.md`): the definitions written
out (clocks z, costs, v and w, x^♯, ŷ^♯, cost^♯, the cell and sharp arrows); Lemma 7.9_p (I1),
(I2), (I3); Part B (U1)–(U3) with v, w written out and the `theorem_U` consequence; Part C with
equality on the sharp loops; the Part C consequence. Then `#print axioms`.
-/

namespace CheckCSI17

open ColouredSand.OddTwist Finset AntitonicFit TheoremF SmithBounds CellFloor

variable {p : ℕ} [Fact p.Prime] {dg : ℕ → ℕ}

theorem hDefs (k ℓ : ℕ) (I : Finset ℕ) (e : ℤ) (Pr Pc q q' a b j : ℕ) (V : ℕ → ℤ) (P : ℕ) :
    oddCellClock p k I dg ℓ e Pr Pc q = xHseqP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
      (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ) ∧
    oddCellCost p k I dg ℓ e Pr Pc q q' = cHatSeqP p k I dg ℓ e q q' -
      (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) + (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ∧
    oddCellPenal V p k I dg ℓ P q = V q - (P : ℤ) * (JHseqP p k I dg ℓ q : ℤ) ∧
    oddCellXSharp p k I dg ℓ e j = xHseqP p k I dg ℓ e (j + 1) ∧
    oddCellYhatSharp p k I dg ℓ e = ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) ∧
    oddCellCostSharp p k I dg ℓ e a b = cHatSeqP p k I dg ℓ e (a + 1) b ∧
    (IsCellArrow I q q' ↔ q < 2 ^ #I ∧ q' < 2 ^ #I ∧ dancer I q' ⊆ dancer I q) ∧
    (IsSharpArrow I a b ↔ a < 2 ^ #I - 1 ∧ b < 2 ^ #I - 1 ∧ dancer I b ⊆ dancer I (a + 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, Iff.rfl⟩

/-- (I1): the real fit of x_H is the integer ŷ_H, and ŷ_H is non-increasing. -/
theorem hI1 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q = (yhatP p k I dg ℓ e q : ℝ)) ∧
      ∀ q q', q ≤ q' → q' < 2 ^ #I → yhatP p k I dg ℓ e q' ≤ yhatP p k I dg ℓ e q := by
  refine ⟨(oddCell_lemma_7_9_I1 hI hd hℓ he).1, ?_⟩
  have h := (oddCell_lemma_7_9_I1 hI hd hℓ he).2
  intro q q' hqq' hq'
  exact h.anti hqq' hq'

/-- (I2), every P_r, P_c: the integer fit of z is ŷ_H − P_r J_H(q) + P_c J_H(N−1−q), it equals
the real fit, and it is non-increasing. -/
theorem hI2 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) :
    (∀ q < 2 ^ #I, ifit (2 ^ #I) (fun q => xHseqP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
        (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) q =
      yhatP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
        (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) ∧
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (oddCellClock p k I dg ℓ e Pr Pc)) q =
      (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q : ℝ)) ∧
    NonIncrOn (2 ^ #I) (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc)) :=
  oddCell_lemma_7_9_I2 hI hd hℓ he Pr Pc

/-- (I3), ℓ = p^k − 1, I ≠ ∅. -/
theorem hI3 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) :
    (∀ t ∈ I, typP p dg ℓ t = .OR ∧ thetaP p ℓ t = 1) ∧
    (∀ q < 2 ^ #I, JHseqP p k I dg ℓ q = if q ≠ 0 then 1 else 0) ∧
    IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) 1 ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (fun j => xHseqP p k I dg ℓ e (j + 1))) j =
      fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) j =
      yhatP p k I dg ℓ e (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (fun j => xHseqP p k I dg ℓ e (j + 1))) j =
      (yhatP p k I dg ℓ e (j + 1) : ℝ)) :=
  oddCell_lemma_7_9_I3 hI hd hℓ' he hne

/-- Part B (U1)–(U3) with v(q) = V(q) − P_r J_H(q), w(q) = V(q) − P_c J_H(q) written out. -/
theorem hB {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ)
    {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (∀ q q', q ≤ q' → q' < 2 ^ #I →
      V q' - (Pr : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ≤ V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) ∧
    (∀ q q', q ≤ q' → q' < 2 ^ #I →
      V q' - (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ≤ V q - (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) ∧
    (∀ q < 2 ^ #I, (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) -
        (V (2 ^ #I - 1 - q) - (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) =
      ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q) ∧
    (∀ q q', q < 2 ^ #I → q' < 2 ^ #I → dancer I q' ⊆ dancer I q →
      (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) - (V q' - (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ)) ≤
        cHatSeqP p k I dg ℓ e q q' - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
          (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ)) ∧
    (∀ q < 2 ^ #I, (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) -
        (V q - (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) =
      cHatSeqP p k I dg ℓ e q q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
          (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := oddCell_theorem_B hI hd hℓ he Pr Pc hV
  exact ⟨fun q q' a b => h1.anti a b, fun q q' a b => h2.anti a b, h3,
    fun q q' a b c => h4 q q' ⟨a, b, c⟩, h5⟩

/-- Part B consequence: every r-matching of the cell arrows costs at least tailSum N r (ifit z);
the potential is supplied by Theorem F_p. -/
theorem hBfloor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) {r : ℕ}
    {Rows : Finset ℕ} {β : ℕ → ℕ} (hm : IsRMatching (2 ^ #I) (IsCellArrow I) r Rows β) :
    tailSum (2 ^ #I) r (fun j => (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) j : ℝ)) ≤
      ∑ a ∈ Rows, (oddCellCost p k I dg ℓ e Pr Pc a (β a) : ℝ) :=
  oddCell_theorem_B_floor hI hd hℓ he Pr Pc hm

/-- Part C, ℓ = p^k − 1, I ≠ ∅, with v(j) = V(j+1), w(j) = V(j), and equality on the sharp loops
`b = a + 1`. -/
theorem hC {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (NonIncrOn (2 ^ #I - 1) (fun j => V (j + 1)) ∧ NonIncrOn (2 ^ #I - 1) V) ∧
    (∀ j < 2 ^ #I - 1, V (j + 1) - V (2 ^ #I - 2 - j) =
      ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) j) ∧
    (∀ a b, a < 2 ^ #I - 1 → b < 2 ^ #I - 1 → dancer I b ⊆ dancer I (a + 1) →
      V (a + 1) - V b ≤ cHatSeqP p k I dg ℓ e (a + 1) b) ∧
    (∀ a, a + 1 < 2 ^ #I - 1 → V (a + 1) - V (a + 1) = cHatSeqP p k I dg ℓ e (a + 1) (a + 1)) := by
  obtain ⟨h1, h2, h3⟩ := oddCell_theorem_C hI hd hℓ' he hne hV
  refine ⟨h1, h2, fun a b ha hb hs => h3 a b ⟨ha, hb, hs⟩, fun a _ => ?_⟩
  rw [oddCell_cHat_self]; simp

/-- Part C consequence with N − 1 positions. -/
theorem hCfloor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I - 1) (IsSharpArrow I) r Rows β) :
    tailSum (2 ^ #I - 1) r (fun j => (oddCellYhatSharp p k I dg ℓ e j : ℝ)) ≤
      ∑ a ∈ Rows, (cHatSeqP p k I dg ℓ e (a + 1) (β a) : ℝ) :=
  oddCell_theorem_C_floor hI hd hℓ' he hne hm

end CheckCSI17

#print axioms CheckCSI17.hDefs
#print axioms CheckCSI17.hI1
#print axioms CheckCSI17.hI2
#print axioms CheckCSI17.hI3
#print axioms CheckCSI17.hB
#print axioms CheckCSI17.hBfloor
#print axioms CheckCSI17.hC
#print axioms CheckCSI17.hCfloor
#print axioms ColouredSand.OddTwist.oddCell_theorem_B
#print axioms ColouredSand.OddTwist.oddCell_theorem_C

end FinalCheck.CSI17

-- ======== piece CSI18 (from lean/proyecto_cubo/checks/CheckCSI18.lean) ========
namespace FinalCheck.CSI18

/-!
# CheckCSI18 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI18 (`CSI18_theorem_4_4_smith_form_of_Mp.md`): the definitions written out
(K, the o-order matrix, C, the clocks x, ŷ, x^♯, ŷ^♯); (Z0) existence and uniqueness of the integer
matrix; (S1)–(S3) for `i ≥ 1`; (Z1)–(Z3) for `i = 0`; (Y1) and (Y2) in their three cases, with
CSI10's `Cmod`, `Yp`, `Sp`, `Zq` unfolded where they enter. Then `#print axioms`.
-/

namespace CheckCSI18

open ColouredSand.OddTwist Finset Matrix TheoremF AntitonicFit

variable (p : ℕ) [Fact p.Prime]

theorem hDefs (l i e : ℕ) :
    oddSmithK p l = digitL p l (kTop p l) * p ^ kTop p l ∧
    oddSmithMo p l i e = (Mp p l i e).submatrix (oddSmithSlot p l i e) (oddSmithSlot p l i e) ∧
    oddSmithC p l i e = (e : ℤ) * (oddSmithK p l : ℤ) + kappaP p (i - 1) (oddSmithK p l) ∧
    oddSmithX p l i e = (fun q =>
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)
        (Iset p l \ dancer (Iset p l) q)) ∧
    oddSmithYhat p l i e = ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) ∧
    oddSmithXSharp p l e = (fun q =>
      rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (dancer (Iset p l) (q + 1)) -
      rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (Iset p l \ dancer (Iset p l) (q + 1))) ∧
    oddSmithYhatSharp p l e = ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The slot of position `q` is labelled by `dancer_I q`. -/
theorem hSlot (l i e : ℕ) (q : Fin (2 ^ #(Iset p l))) :
    labL p l i e (kTop p l) (oddSmithSlot p l i e q) = dancer (Iset p l) q :=
  oddSmith_labL_slot p l i e q

/-- (Z0): the integer matrix exists and is unique. -/
theorem hZ0 (l i e : ℕ) :
    oddSmithMo p l i e = (oddSmithMZ p l i e).map (Int.cast) ∧
    ∀ MZ : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      oddSmithMo p l i e = MZ.map (Int.cast) → MZ = oddSmithMZ p l i e :=
  ⟨oddSmith_Z0 p l i e, fun MZ h => oddSmith_Z0_unique p l i e MZ h⟩

/-- (S1). -/
theorem hS1 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) (q q' : Fin (2 ^ #(Iset p l))) :
    (¬ dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' = 0) ∧
    (dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = ((e : ℤ) * (digitL p l (kTop p l) * p ^ kTop p l : ℕ) +
            kappaP p (i - 1) (digitL p l (kTop p l) * p ^ kTop p l)) +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l)
            (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) (dancer (Iset p l) q') +
          Rulers.gamma (kTop p l) (Iset p l) (dancer (Iset p l) q \ dancer (Iset p l) q') ∧
        (p : ℤ) ^ n ∣ oddSmithMZ p l i e q q' ∧ ¬ (p : ℤ) ^ (n + 1) ∣ oddSmithMZ p l i e q q') :=
  oddSmith_S1 p hodd l i e he hi q q'

/-- (S2). -/
theorem hS2 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ #(Iset p l), (ddP p (oddSmithMZ p l i e) r : ℤ) =
      r * oddSmithC p l i e +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)),
          ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) j) ∧
    (oddSmithMZ p l i e).det ≠ 0 ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) →
      ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) (j + 1) ≤
        ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) j) :=
  oddSmith_S2 p hodd l i e he hi

/-- (S3). -/
theorem hS3 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
            (E j : ℤ) = oddSmithC p l i e +
              ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) (2 ^ #(Iset p l) - 1 - j)) ∧
          P * oddSmithMZ p l i e * Q =
            diagonal (fun j : Fin (2 ^ #(Iset p l)) => u j * (p : ℤ) ^ E j) :=
  oddSmith_S3 p hodd l i e he hi

/-- (Z1): the row of `∅` (position `0`) is zero, `det = 0`, and `MZ = 0` when `I = ∅`. -/
theorem hZ1 (l e : ℕ) (he : 1 ≤ e) :
    (∀ q', oddSmithMZ p l 0 e ⟨0, Nat.two_pow_pos _⟩ q' = 0) ∧ (oddSmithMZ p l 0 e).det = 0 ∧
      (Iset p l = ∅ → oddSmithMZ p l 0 e = 0) :=
  oddSmith_Z1 p l e he

/-- (Z2). -/
theorem hZ2 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    (∀ r ≤ 2 ^ #(Iset p l) - 1, (ddP p (oddSmithMZ p l 0 e) r : ℤ) =
      r * ((e : ℤ) * (oddSmithK p l : ℤ)) +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - 1 - r) (2 ^ #(Iset p l) - 1),
          ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) j) ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) - 1 →
      ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) (j + 1) ≤
        ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) j) :=
  oddSmith_Z2 p hodd l e he hne

/-- (Z3). -/
theorem hZ3 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
            (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
              ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) (2 ^ #(Iset p l) - 2 - j)) ∧
          P * oddSmithMZ p l 0 e * Q = diagonal (fun j : Fin (2 ^ #(Iset p l)) =>
            if (j : ℕ) < 2 ^ #(Iset p l) - 1 then u j * (p : ℤ) ^ E j else 0) :=
  oddSmith_Z3 p hodd l e he hne

/-- (Y1), `i ≥ 1`, with `Cmod` and `Zq` unfolded. -/
theorem hY1pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)) ≃ₗ[ℤ_[p]]
        ((j : Fin (2 ^ #(Iset p l))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)})) :=
  oddSmith_Y1_pos p hodd l i e he hi

/-- (Y1), `i = 0`, `I ≠ ∅`. -/
theorem hY1zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (((slots p l 0 e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l 0 e).mulVecLin)) ≃ₗ[ℤ_[p]]
        (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)}))) :=
  oddSmith_Y1_zero p hodd l e he hne

/-- (Y1), `i = 0`, `I = ∅`. -/
theorem hY1empty (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (((slots p l 0 e → ℤ_[p]) ⧸
        LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l 0 e).mulVecLin)) ≃ₗ[ℤ_[p]] ℤ_[p]) :=
  oddSmith_Y1_zero_empty p l e he hI

/-- (Y2), `i ≥ 1`. -/
theorem hY2pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (Yp p l i e ≃ₗ[ℤ_[p]]
        (Sp p l × ((j : Fin (2 ^ #(Iset p l))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)}))) :=
  oddSmith_Y2_pos p hodd l i e he hi

/-- (Y2), `i = 0`, `I ≠ ∅`. -/
theorem hY2zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]]
        (Sp p l × (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)})))) :=
  oddSmith_Y2_zero p hodd l e he hne

/-- (Y2), `i = 0`, `I = ∅`. -/
theorem hY2empty (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]] (Sp p l × ℤ_[p])) :=
  oddSmith_Y2_zero_empty p hodd l e he hI

end CheckCSI18

#print axioms CheckCSI18.hDefs
#print axioms CheckCSI18.hSlot
#print axioms CheckCSI18.hZ0
#print axioms CheckCSI18.hS1
#print axioms CheckCSI18.hS2
#print axioms CheckCSI18.hS3
#print axioms CheckCSI18.hZ1
#print axioms CheckCSI18.hZ2
#print axioms CheckCSI18.hZ3
#print axioms CheckCSI18.hY1pos
#print axioms CheckCSI18.hY1zero
#print axioms CheckCSI18.hY1empty
#print axioms CheckCSI18.hY2pos
#print axioms CheckCSI18.hY2zero
#print axioms CheckCSI18.hY2empty

end FinalCheck.CSI18

-- ======== piece CSI19 (from lean/proyecto_cubo/checks/CheckCSI19.lean) ========
namespace FinalCheck.CSI19

/-!
# CheckCSI19 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI19 (`CSI19_theorem_TOTAL.md`): (U1) for `q ≠ 0`; (B1) with CSI10's `Yp`
unfolded; (T1) for every `m`; Theorem TOTAL (S1) and (S2) for every `d`, with the exponent list
written out from `S_p(λ)` and CSI18 (Y2), zero exponents removed; (S3) the agreement with CSG7's
`gTorList` for `m ≤ p² + p − 1`. Then `#print axioms`.
-/

namespace CheckCSI19

open ColouredSand ColouredSand.OddTwist ColouredSand.BlockOp ColouredSand.TheoremB ColouredSand.ThmG Finset

variable (p : ℕ) [Fact p.Prime]

/-- The exponent lists written out. -/
theorem hDefs (l i e q c m : ℕ) :
    oddTotalSpList p l =
      (List.ofFn fun t : Fin (kTop p l - 1) =>
          List.replicate ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) *
            2 ^ (Iset p l).card) ((t : ℕ) + 1)).flatten ++
        List.replicate ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) (kTop p l) ∧
    oddTotalCList p l i e =
      (if i = 0 then
        List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l +
          ((e : ℤ) * (oddSmithK p l : ℤ) + oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)).toNat
      else
        List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l +
          (oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)).toNat) ∧
    oddTotalYList p l i e = oddTotalSpList p l ++ oddTotalCList p l i e ∧
    oddTotalTotList p q c m =
      ((LL p m).flatMap fun l => oddTotalYList p l (c + (m - l) / 2) (padicValNat p q)).filter
        (fun a => a ≠ 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- (U1). -/
theorem hU1 (M : DPLattice ℤ_[p]) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (((M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m q c)) ≃ₗ[ℤ_[p]]
      ((M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m (p ^ padicValNat p q) c))) :=
  oddTotal_U1 M m c hq

/-- (B1), with `Yp` unfolded. -/
theorem hB1 (hp2 : p ≠ 2) {l m : ℕ} (hle : l ≤ m) (hpar : l % 2 = m % 2) (e c : ℕ) :
    Nonempty (cokT p (danceL p l) m (p ^ e) c ≃ₗ[ℤ_[p]]
      (((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range (sigmaOp p l e (c + (m - l) / 2)))) :=
  oddTotal_B1 hp2 hle hpar e c

/-- (T1), every `m`. -/
theorem hT1 (hp2 : p ≠ 2) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (cokT p (Filt.tpow ℤ_[p] m) m q c ≃ₗ[ℤ_[p]]
      ((t : Fin (LL p m).length) →
        Yp p ((LL p m).get t) (c + (m - (LL p m).get t) / 2) (padicValNat p q))) :=
  oddTotal_T1 hp2 m c hq

/-- (S1) Theorem TOTAL, every `d`. -/
theorem hS1 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LL p (d - σ.1)).length) →
          Yp p ((LL p (d - σ.1)).get t) (σ.1 + (d - σ.1 - (LL p (d - σ.1)).get t) / 2)
            (padicValNat p q))) :=
  oddTotal_S1 hp2 hq2

/-- (S2) Theorem TOTAL with explicit exponents, every `d`. -/
theorem hS2 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (oddTotalTotList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (oddTotalTotList p q σ.1 (d - σ.1)).get i))) :=
  oddTotal_S2 hp2 hq2 hq

/-- (S3) agreement with Theorem G. -/
theorem hS3 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) : (oddTotalTotList p q c m).Perm (gTorList p q c m) :=
  oddTotal_S3 hp2 c hq hm

end CheckCSI19

#print axioms CheckCSI19.hDefs
#print axioms CheckCSI19.hU1
#print axioms CheckCSI19.hB1
#print axioms CheckCSI19.hT1
#print axioms CheckCSI19.hS1
#print axioms CheckCSI19.hS2
#print axioms CheckCSI19.hS3
#print axioms ColouredSand.OddTwist.oddTotal_S2

end FinalCheck.CSI19

-- ======== piece CSX1 (from lean/proyecto_cubo/checks/CheckCSX1.lean) ========
namespace FinalCheck.CSX1

/-!
# CheckCSX1 (Grepy Ship, 15 Oct 2026)

Hand restatement of CSX1 (`CSX1_theorem_E_every_prime.md`): Theorem E of the Coloured Sand for
every prime `p` and every `q ≠ 0`; the case `p ∤ q` (`e = v_p(q) = 0`) written out with the
exponent `∑_{r=k}^{m−k} v_p(c + r)`; and the old theorem `theorem_E` recovered. Then `#print axioms`.
-/

namespace CheckCSX1

open ColouredSand ColouredSand.Strings Finset

/-- Theorem E, every prime, `q ≠ 0` (restated by hand). -/
theorem hE (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : q ≠ 0) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}))) :=
  strAll_theorem_E p q hq c m hm

/-- The case `p ∤ q`, exponents written out with no `v_p(q)` (restated by hand). -/
theorem hCoprime (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : ¬ (p : ℤ) ∣ q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span
            {(p : ℤ_[p]) ^ ∑ r ∈ Icc (t.1 : ℕ) (m - t.1), padicValNat p (c + r)}))) :=
  strAll_theorem_E_coprime_explicit p q hq c m hm

/-- The old statement (CS1) is a special case. -/
theorem hOld (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}))) :=
  strAll_theorem_E_eq p q hq c m hm

/-- A concrete instance of the new case: `p = 5`, `q = 7` (not divisible by 5). -/
example : ¬ ((5 : ℕ) : ℤ) ∣ (7 : ℤ) := by decide

end CheckCSX1

#print axioms CheckCSX1.hE
#print axioms CheckCSX1.hCoprime
#print axioms CheckCSX1.hOld
#print axioms ColouredSand.Strings.strAll_span_prod_eq
#print axioms ColouredSand.Strings.strAll_theorem_E
#print axioms ColouredSand.Strings.strAll_theorem_E_coprime
#print axioms ColouredSand.Strings.strAll_theorem_E_coprime_explicit
#print axioms ColouredSand.Strings.strAll_theorem_E_eq

end FinalCheck.CSX1

-- ======== piece CSX2 (from lean/proyecto_cubo/checks/CheckCSX2.lean) ========
namespace FinalCheck.CSX2

/-!
# CheckCSX2 (Grepy Ship, 15 Oct 2026)

Hand restatement of CSX2 (`CSX2_theorem_I_prime_two.md`): Theorem I of the Coloured Sand at the
prime 2. Every type is written out by hand from the certified Dancing Sand definitions
(`FamilyGroup.X`, `SC`, `Q`; `Windows.finalMatrix`; `Families.ds`; `Dance.mCount`); the cokernel
`C = coker(2^k M)` is written out instead of using `CmodTwo`. Then `#print axioms`.
-/

namespace CheckCSX2

open FamilyGroup
open scoped Pointwise

/-- (E1): for `α ≥ 1` every entry of the final matrix is even (restated by hand). -/
theorem hE1 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ Dance.mCount ds)) :
    (2 : ℤ) ∣ Windows.finalMatrix ℤ ds α i s s' :=
  ColouredSand.TwoI.twoI_E1 ds α i hα s s'

/-- (I1), `k ≥ 1`, `i ≥ 1`: exponents `E j ≥ k + 1` for the `N` large summands. -/
theorem hI1 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds, ds.length + 1 ≤ E j) ∧
      Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((j : Fin (2 ^ Dance.mCount ds)) → Q (E j))) :=
  ColouredSand.TwoI.twoI_I1_pos ds hk α i hα hi

/-- (I2): the small summands are killed by `2^k`. -/
theorem hI2 (ds : List Bool) (x : SC ds) : (2 : ℤ_[2]) ^ ds.length • x = 0 :=
  ColouredSand.TwoI.twoI_I2 ds x

/-- (I4), the invariant form, for every digit list. -/
theorem hI4 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((X ds α i ⧸ (2 : ℤ_[2]) ^ (ds.length + 1) • (⊤ : Submodule ℤ_[2] (X ds α i)))
      ≃ₗ[ℤ_[2]] (SC ds × (Fin (2 ^ Dance.mCount ds) → Q (ds.length + 1)))) :=
  ColouredSand.TwoI.twoI_I4 ds α i hα

/-- (I3), with the cokernel `coker(2^k M)` written out by hand. -/
theorem hI3 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((Fin (2 ^ Dance.mCount ds) → ℤ_[2]) ⧸
      LinearMap.range ((2 : ℤ_[2]) ^ ds.length •
        Matrix.toLin' ((Windows.finalMatrix ℤ ds α i).map (Int.castRingHom ℤ_[2]))))) :=
  ColouredSand.TwoI.twoI_I3_equiv ds α i hα

/-- (I5) on the family `λ`, invariant part, with `ds = Families.ds λ`. -/
theorem hI5 (l i α : ℕ) (hα : 1 ≤ α) :
    Nonempty ((X (Families.ds l) α i ⧸ (2 : ℤ_[2]) ^ ((Families.ds l).length + 1) •
        (⊤ : Submodule ℤ_[2] (X (Families.ds l) α i))) ≃ₗ[ℤ_[2]]
      (SC (Families.ds l) × (Fin (2 ^ Dance.mCount (Families.ds l)) →
        Q ((Families.ds l).length + 1)))) :=
  (ColouredSand.TwoI.twoI_theorem_I l i α hα).2.2.2.2

/-- (I6): `k = ⌊log₂(λ+1)⌋` and `|I| + 1` = number of binary digits 1 of `λ + 1`. -/
theorem hI6 (l : ℕ) :
    (Families.ds l).length = Nat.log 2 (l + 1) ∧
      Dance.mCount (Families.ds l) + 1 = (Nat.digits 2 (l + 1)).count 1 :=
  ColouredSand.TwoI.twoI_I6 l

/-- A concrete instance: `λ = 12`, `λ + 1 = 13 = 1101₂`, so `k = 3` and `|I| = 2`. -/
example : (Families.ds 12).length = 3 ∧ Dance.mCount (Families.ds 12) = 2 := by
  have h := hI6 12
  refine ⟨by rw [h.1]; decide, ?_⟩
  have h2 : (Nat.digits 2 (12 + 1)).count 1 = 3 := by decide
  omega

end CheckCSX2

#print axioms CheckCSX2.hE1
#print axioms CheckCSX2.hI1
#print axioms CheckCSX2.hI2
#print axioms CheckCSX2.hI3
#print axioms CheckCSX2.hI4
#print axioms CheckCSX2.hI5
#print axioms CheckCSX2.hI6
#print axioms ColouredSand.TwoI.twoI_theorem_I
#print axioms ColouredSand.TwoI.twoI_theorem_I_ds
#print axioms ColouredSand.TwoI.twoI_I1_zero
#print axioms ColouredSand.TwoI.twoI_I1_empty
#print axioms ColouredSand.TwoI.twoI_I1_nil_pos
#print axioms ColouredSand.TwoI.twoI_I1_nil_zero
#print axioms ColouredSand.TwoI.twoI_E2_pos
#print axioms ColouredSand.TwoI.twoI_E2_zero

end FinalCheck.CSX2

-- ======== piece CSX3 (from lean/proyecto_cubo/checks/CheckCSX3.lean) ========
namespace FinalCheck.CSX3

/-!
# CheckCSX3 (Grepy Ship, 15 Oct 2026)

Hand restatement of CSX3 (`CSX3_theorems_F_G_prime_two.md`): Theorems F and G of the Coloured
Sand at the prime 2 — (M2) the multiplicities, (B1) the blocks, (T1), (T2), (F1), (F2), (S1),
(S2) at `p = 2` — and the `…_allPrimes` forms, which are CSG7's statements with the hypothesis
`p ≠ 2` removed. Every type written out by hand. Then `#print axioms`.
-/

namespace CheckCSX3

open ColouredSand.Strings ColouredSand.ThmH ColouredSand.TiltP ColouredSand.TiltDec
  ColouredSand.Blocks ColouredSand.BlockOp ColouredSand.Splitting ColouredSand.Corollaries
  ColouredSand.ThmG ColouredSand.TheoremB

/-- (M2) by hand: the two weight lists agree at `p = 2` for `m ≤ 5`. -/
theorem hM2 (m : ℕ) (hm : m ≤ 5) : (LP 2 m).Perm (FamDec.L m) :=
  ColouredSand.ThmGTwo.twoM2 hm

/-- (B1) by hand: the Dancing Sand family group is the block `G_c(m, λ)` at `p = 2`. -/
theorem hB1 (lam m q c : ℕ) (hl : lam ≤ 5) (hle : lam ≤ m) (hpar : lam % 2 = m % 2)
    (hq : 1 ≤ padicValNat 2 q) :
    Nonempty (FamilyGroup.X (Families.ds lam) (padicValNat 2 q) (c + (m - lam) / 2) ≃+
      GBlk 2 q c ((m - lam) / 2) lam) :=
  ColouredSand.ThmGTwo.twoB1 c hl hle hpar hq

/-- (T1) Theorem G at `p = 2`, by hand. -/
theorem hT1 (q m c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 5) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2) ≃+
      ((j : Fin (LP 2 m).length) →
        GBlk 2 q c ((m - (LP 2 m).get j) / 2) ((LP 2 m).get j))) :=
  ColouredSand.ThmGTwo.twoT1 c hq hm

/-- (T2) the torsion form at `p = 2`, the exponent list written as a `flatMap`. -/
theorem hT2 (q m c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 5) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
      ((i : Fin ((LP 2 m).flatMap (fun l => blkList 2 q c ((m - l) / 2) l)).length) →
        ZMod (2 ^ ((LP 2 m).flatMap (fun l => blkList 2 q c ((m - l) / 2) l)).get i))) :=
  ColouredSand.ThmGTwo.twoT2 c hq hm

/-- (F1) by hand. -/
theorem hF1 (q m c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 2) :
    (gTorList 2 q c m).Perm (FList 2 q c m) :=
  ColouredSand.ThmGTwo.twoF1 c hq hm

/-- (F2) the Glue Theorem at `p = 2`, by hand. -/
theorem hF2 (q m c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
      ((i : Fin (FList 2 q c m).length) → ZMod (2 ^ (FList 2 q c m).get i))) :=
  ColouredSand.ThmGTwo.twoF2 c hq hm

/-- (S1) the sandpile at `p = 2`, `d ≤ 5`, by hand. -/
theorem hS1 (d q : ℕ) (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat 2 q) (hd : d ≤ 5) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent (sandpile d q) 2) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LP 2 (d - σ.1)).length) →
          GBlk 2 q σ.1 ((d - σ.1 - (LP 2 (d - σ.1)).get t) / 2) ((LP 2 (d - σ.1)).get t))) :=
  ColouredSand.ThmGTwo.twoS1 hq2 hq hd

/-- (S2) by hand. -/
theorem hS2 (d q : ℕ) (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat 2 q) (hd : d ≤ 5) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) 2 ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList 2 q σ.1 (d - σ.1)).length) →
          ZMod (2 ^ (gTorList 2 q σ.1 (d - σ.1)).get i))) :=
  ColouredSand.ThmGTwo.twoS2 hq2 hq hd

/-- (T1) for every prime, with no `p ≠ 2`, by hand. -/
theorem hT1all (p : ℕ) [Fact p.Prime] (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      ((j : Fin (LP p m).length) →
        GBlk p q c ((m - (LP p m).get j) / 2) ((LP p m).get j))) :=
  ColouredSand.ThmGTwo.twoT1_allPrimes c hq hm

/-- (F2) for every prime, with no `p ≠ 2`, by hand. -/
theorem hF2all (p : ℕ) [Fact p.Prime] (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ 2 * p - 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (FList p q c m).length) → ZMod (p ^ (FList p q c m).get i))) :=
  ColouredSand.ThmGTwo.twoF2_allPrimes c hq hm

/-- (S2) for every prime, with no `p ≠ 2`, by hand. -/
theorem hS2all (p : ℕ) [Fact p.Prime] (d q : ℕ) (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (gTorList p q σ.1 (d - σ.1)).get i))) :=
  ColouredSand.ThmGTwo.twoS2_allPrimes hq2 hq hd

/-- The multiset `VdotP 2 4` by hand (the case where `τ` matters). -/
example : ColouredSand.TiltDec.VdotP 2 4 = [5, 3, 3] := ColouredSand.ThmGTwo.twoVdotP_four

end CheckCSX3

#print axioms CheckCSX3.hM2
#print axioms CheckCSX3.hB1
#print axioms CheckCSX3.hT1
#print axioms CheckCSX3.hT2
#print axioms CheckCSX3.hF1
#print axioms CheckCSX3.hF2
#print axioms CheckCSX3.hS1
#print axioms CheckCSX3.hS2
#print axioms CheckCSX3.hT1all
#print axioms CheckCSX3.hF2all
#print axioms CheckCSX3.hS2all
#print axioms ColouredSand.ThmGTwo.twoThmG
#print axioms ColouredSand.ThmGTwo.twoT2_allPrimes
#print axioms ColouredSand.ThmGTwo.twoF1_allPrimes
#print axioms ColouredSand.ThmGTwo.twoS1_allPrimes

end FinalCheck.CSX3
