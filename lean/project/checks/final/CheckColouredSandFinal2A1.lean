-- CheckColouredSandFinal2A1.lean (part A1 of half A: every import, pieces 1-4) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
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

-- ======== piece CS1 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS1.lean) ========
namespace FinalCheck.CS1

/-! CheckCS1 — Grepy Connor, 13 Oct 2026. The headline statements of piece CS1
(strings of the Boolean lattice and Theorem E of «The Coloured Sand Theorem»),
restated by hand and closed by the certified theorems; then their axioms. -/

open Finset ColouredSand.Strings

-- §0: the definitions, read on basis vectors (faithfulness).
#check @H_single
#check @U_single
#check @D_single

-- (S1) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] :
    D m R ∘ₗ U m R - U m R ∘ₗ D m R = (m : R) • LinearMap.id - (2 : R) • H m R :=
  commutator_DU_UD

-- (S2) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] {k : ℕ} {v : B m R} (hv : v ∈ level m R k)
    (hD : D m R v = 0) {i : ℕ} (hi : 1 ≤ i) :
    D m R ((U m R ^ i) v) = ((i : ℤ) * ((m : ℤ) - 2 * k - i + 1)) • (U m R ^ (i - 1)) v :=
  string_relation hv hD hi

-- (S3)(c) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R))
    {k : ℕ} (hk : k ≤ m / 2) : (Lam m R k).map (U m R ^ (m - 2 * k + 1)) = ⊥ :=
  strings_c hR hk

-- (S4) restated by hand.
example {R : Type} [CommRing R] (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) R)
    (d : Fin n → R) (hdiag : ∀ i, M i i = d i)
    (hsub : ∀ i j : Fin n, (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin n, i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (Matrix.mulVecLin M)) ≃ₗ[R]
      (R ⧸ Ideal.span {∏ i, d i})) :=
  bidiagonal_coker n hn M d hdiag hsub hzero

-- (S5) Theorem E restated by hand, with the exponent written out.
example (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)},
            Fin (m.choose k - if (k : ℕ) = 0 then 0 else m.choose ((k : ℕ) - 1))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^
            (∑ r ∈ Icc (t.1 : ℕ) (m - t.1), (padicValInt p q + padicValNat p (c + r)))}))) :=
  theorem_E p q hq c m hm

#print axioms commutator_DU_UD
#print axioms string_relation
#print axioms Lam_zero
#print axioms strings_a
#print axioms strings_b
#print axioms stringEquiv
#print axioms strings_c
#print axioms Lam_free_finrank
#print axioms Lam_free_finrank_of_isLocalRing
#print axioms bidiagonal_coker
#print axioms coker_opM_equiv
#print axioms theorem_E

end FinalCheck.CS1

-- ======== piece CS2 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS2.lean) ========
namespace FinalCheck.CS2

/-! CheckCS2 — Grepy Connor, 13 Oct 2026. Theorem A (Jacobson–Niedermaier–Reiner splitting) of
«The Coloured Sand Theorem», restated by hand, plus the definitions read on their face. -/

open Finset ColouredSand.Strings ColouredSand.Splitting

-- the objects, on their face
#print ColouredSand.Splitting.hammingGraph
#print ColouredSand.Splitting.laplacian
#check @laplacian_apply
#check @Mq_apply
#check @hammingGraph_degree
#check @completeGraph_lapMatrix

-- (A2) restated by hand: the cokernel of the Laplacian of H(d,q), written with Mathlib's lapMatrix,
-- against the product of the pieces q(c+H)+U.
example (d q : ℕ) (hq : 2 ≤ q) :
    Nonempty ((((Fin d → Fin q) → ℤ) ⧸
        LinearMap.range ((((hammingGraph d q).lapMatrix ℤ)).mulVecLin)) ≃ₗ[ℤ]
      ∀ σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))),
        (B (d - σ.1) ℤ ⧸ LinearMap.range
          ((q : ℤ) • (((σ.1 : ℕ) : ℤ) • LinearMap.id + H (d - σ.1) ℤ) + U (d - σ.1) ℤ))) :=
  theorem_A d q hq

-- adjacency is "differ in exactly one coordinate"
example (d q : ℕ) (x y : Fin d → Fin q) : (hammingGraph d q).Adj x y ↔ hammingDist x y = 1 := Iff.rfl

-- (A4) restated by hand
example (p : ℕ) [Fact p.Prime] (m : ℕ) (q c q' c' : ℤ)
    (hzero : ∀ s ≤ m, (q * (c + s) = 0 ↔ q' * (c' + s) = 0))
    (hval : ∀ s ≤ m, padicValInt p (q * (c + s)) = padicValInt p (q' * (c' + s))) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      (B m ℤ_[p] ⧸ LinearMap.range ((q' : ℤ_[p]) • ((c' : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p]))) :=
  opM_coker_depends_only_on_valuations m q c q' c' hzero hval

#print axioms theorem_A
#print axioms basisVec_isBasis
#print axioms K_ev_zero
#print axioms K_sigma
#print axioms K_fv
#print axioms completeGraph_lapMatrix
#print axioms hammingGraph_degree
#print axioms rescaling
#print axioms rescaling_coker
#print axioms rescaling_padic
#print axioms rescaling_padic_coker
#print axioms opM_coker_equiv_valuations
#print axioms opM_coker_depends_only_on_valuations

end FinalCheck.CS2

-- ======== piece CS3 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS3.lean) ========
namespace FinalCheck.CS3

/-! CheckCS3 — Grepy Altair, 13 Oct 2026. Theorem B of «The Coloured Sand Theorem» (the Sylow
p-subgroup of the sandpile group of H(d,q) for p > d, ballot numbers), restated by hand, plus the
definitions read on their face. -/

open scoped TensorProduct
open Finset ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB

-- the objects, on their face
#print ColouredSand.TheoremB.cokerL
#print ColouredSand.TheoremB.sandpile
#print ColouredSand.TheoremB.nCount
#print ColouredSand.TheoremB.ballot
#check @ColouredSand.Splitting.laplacian_apply

-- (B3) Theorem B restated by hand: the sandpile group written out as the torsion of the cokernel of
-- the Laplacian, Syl_p as Mathlib's primary component, n_v written as the explicit double sum.
example (d q p : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hpd : d < p) (hpq : p ∣ q) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) p ≃+
      ((s : Σ v : Fin d, Fin (∑ j ∈ range (d + 1), ∑ k ∈ range (d + 1),
          if j + 2 * k = d + 1 - ((v : ℕ) + 1) ∧ (j, k) ≠ (0, 0) then
            d.choose j * (q - 2) ^ j *
              (((v : ℕ) + 1 + 2 * k - 1).choose k -
                if k = 0 then 0 else ((v : ℕ) + 1 + 2 * k - 1).choose (k - 1))
          else 0)) → ZMod (p ^ (padicValNat p q * ((s.1 : ℕ) + 1))))) :=
  theorem_B d q p hd hpd hpq hq

-- (B2) restated by hand
example (v k : ℕ) (hv : 1 ≤ v) :
    ((v + 2 * k - 1).choose k : ℚ) - (if k = 0 then 0 else ((v + 2 * k - 1).choose (k - 1) : ℚ)) =
      (v : ℚ) / (v + 2 * k) * (v + 2 * k).choose k :=
  ballot_identity v k hv

-- (B1) restated by hand
example (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Finite G] :
    Nonempty (AddCommGroup.primaryComponent G p ≃+ ℤ_[p] ⊗[ℤ] G) :=
  sylow_tensor_padic p G

-- (B4), d = 2, with u = q − 2
example (q : ℕ) : nCount 2 q 1 = (q - 2) ^ 2 + 1 ∧ nCount 2 q 2 = 2 * (q - 2) := nCount_two q

-- §0: coker L ≅ ℤ × K, K finite
example (d q : ℕ) (hq : 1 ≤ q) :
    Nonempty (cokerL d q ≃ₗ[ℤ] ℤ × sandpile d q) ∧ Finite (sandpile d q) :=
  cokerL_equiv_int_prod_sandpile d q hq

#print axioms theorem_B
#print axioms ballot_identity
#print axioms ballot_cast
#print axioms sylow_tensor_padic
#print axioms coker_tensor_padic
#print axioms coker_tensor_padic_matrix
#print axioms torsion_tensor_equiv_syl
#print axioms nCount_two
#print axioms nCount_three
#print axioms nCount_four
#print axioms theorem_B_two
#print axioms theorem_B_three
#print axioms theorem_B_four
#print axioms hammingGraph_connected
#print axioms cokerL_equiv_int_prod_sandpile

end FinalCheck.CS3

-- ======== piece CS4 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS4.lean) ========
namespace FinalCheck.CS4

/-! CheckCS4 — Grepy Altair, 13 Oct 2026. Theorem C of «The Coloured Sand Theorem» (the exponent of
the Sylow p-subgroup of the sandpile group of H(d,q), every prime p, q ≥ 3), Lemma 4 (the inverse),
the exponent criterion and Lemma 5 (carries), restated by hand. -/

open scoped Nat
open Finset ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Exponent

#print ColouredSand.Exponent.expE
#print ColouredSand.Exponent.carryPairs
#check @ColouredSand.Exponent.mem_carryPairs

-- (C4) Theorem C restated by hand: the sandpile group as the torsion of the cokernel of the
-- Laplacian, Syl_p as Mathlib's primary component, the exponent as Mathlib's AddMonoid.exponent.
example (d q p : ℕ) [Fact p.Prime] (hq : 3 ≤ q) :
    AddMonoid.exponent (AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) p) =
      p ^ (if 1 ≤ padicValNat p q then (Icc 1 d).sup (fun s => padicValNat p q * s + padicValNat p s)
        else Nat.log p d) :=
  theorem_C d q p hq

-- (C1) Lemma 4 restated by hand
example (m q c : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c) (S T : Finset (Fin m)) (hST : S ⊆ T) (s k : ℕ)
    (hs : S.card = s) (hk : T.card = s + k) :
    (LinearMap.toMatrix' ((q : ℚ) • ((c : ℚ) • LinearMap.id + H m ℚ) + U m ℚ : (Finset (Fin m) → ℚ) →ₗ[ℚ] _))⁻¹ T S =
      (-1) ^ k * (k ! : ℚ) * ∏ i ∈ range (k + 1), 1 / ((q : ℚ) * (c + s + i)) :=
  (lemma4 m q c hq hc).2 S T |>.1 hST s k hs hk

-- (C3) Lemma 5 restated by hand
example (p : ℕ) [Fact p.Prime] (d e : ℕ) :
    (carryPairs d).sup (fun x => e * x.1 + padicValNat p x.1 + padicValNat p (x.2.choose x.1)) =
      (Icc 1 d).sup (fun s => e * s + padicValNat p s) := lemma5 p d e

-- (C5) the checks
example : AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile 10 3) 3) = 3 ^ 11 :=
  exponent_three_three_ten
example (d q p : ℕ) [Fact p.Prime] (hq : 3 ≤ q) (hpd : d < p) :
    AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile d q) p) = p ^ (padicValNat p q * d) :=
  exponent_of_lt d q p hq hpd

#print axioms theorem_C
#print axioms lemma4
#print axioms exponent_criterion
#print axioms exponent_criterion_padic
#print axioms kills_coker_iff_integral
#print axioms lemma5
#print axioms lemma5_zero
#print axioms exponent_three_three_ten
#print axioms expE_of_lt
#print axioms exponent_of_lt

end FinalCheck.CS4
