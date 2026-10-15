import RequestProject.ThmGTwo.All

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
