import RequestProject.Exponent.All

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
