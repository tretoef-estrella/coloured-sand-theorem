import RequestProject.ThmG.All

/-!
# CheckCSG7 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG7 (`CSG7_theorem_G.md`): Theorem G as printed (T1), its torsion form (T2)
with the list of exponents written out as a `flatMap`, the Glue Theorem (F1), (F2), the Sylow
`p`-subgroup of `K(H(d,q))` (S1), (S2), and the Example (X1), checked against the certified
theorems of `ColouredSand.ThmG`. The first case of (L0) is checked by hand: for `λ ≤ p − 1` and
`c + k ≥ 1` the list is the single exponent `Σ_{t ≤ λ} (v_p(q) + v_p(c + k + t))`.
Then `#print axioms`.
-/

namespace CheckCSG7

open ColouredSand.Strings ColouredSand.ThmH ColouredSand.TiltP ColouredSand.TiltDec
  ColouredSand.Blocks ColouredSand.BlockOp ColouredSand.Splitting ColouredSand.Corollaries
  ColouredSand.ThmG ColouredSand.TheoremB

/-- (L0), first case, by hand. -/
theorem hL0a (p : ℕ) [Fact p.Prime] (q c k l : ℕ) (hl : l ≤ p - 1) (hck : c + k ≠ 0) :
    blkList p q c k l =
      [∑ t ∈ Finset.range (l + 1), (padicValNat p q + padicValNat p (c + k + t))] := by
  simp only [blkList, if_pos hl, if_neg hck]; rfl

/-- (L0), first case, `c = k = 0`, by hand: no finite factor. -/
theorem hL0b (p : ℕ) [Fact p.Prime] (q l : ℕ) (hl : l ≤ p - 1) :
    blkList p q 0 0 l = [] := by
  simp only [blkList, if_pos hl, if_true]

/-- (L1) by hand. -/
theorem hL1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q c l m : ℕ) (hq : 1 ≤ padicValNat p q)
    (hl : l ≤ p ^ 2 + p - 1) (hle : l ≤ m) (hpar : l % 2 = m % 2) :
    Nonempty ((((Ttilt p l).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p l) m q c)) ≃+
      ((Fin (if c = 0 ∧ (m - l) / 2 = 0 then 1 else 0) → ℤ_[p]) ×
        ((i : Fin (blkList p q c ((m - l) / 2) l).length) →
          ZMod (p ^ (blkList p q c ((m - l) / 2) l).get i)))) :=
  L1 hp2 hq hl hle hpar

/-- (T1) Theorem G, as printed, by hand. -/
theorem hT1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      ((j : Fin (LP p m).length) →
        (Fin (if c = 0 ∧ (m - (LP p m).get j) / 2 = 0 then 1 else 0) → ℤ_[p]) ×
          ((i : Fin (blkList p q c ((m - (LP p m).get j) / 2) ((LP p m).get j)).length) →
            ZMod (p ^ (blkList p q c ((m - (LP p m).get j) / 2) ((LP p m).get j)).get i)))) :=
  T1 hp2 c hq hm

/-- (T2) the torsion form, by hand: the exponent list is the `flatMap` over `LP p m`. -/
theorem hT2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin ((LP p m).flatMap (fun l => blkList p q c ((m - l) / 2) l)).length) →
        ZMod (p ^ ((LP p m).flatMap (fun l => blkList p q c ((m - l) / 2) l)).get i))) :=
  T2 hp2 c hq hm

/-- (F1) by hand. -/
theorem hF1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ 2 * p - 2) :
    ((LP p m).flatMap (fun l => blkList p q c ((m - l) / 2) l)).Perm (FList p q c m) :=
  F1 hp2 c hq hm

/-- (F2) Theorem F, as printed, by hand. -/
theorem hF2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q m c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ 2 * p - 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (FList p q c m).length) → ZMod (p ^ (FList p q c m).get i))) :=
  F2 hp2 c hq hm

/-- (S2) `Syl_p K(H(d,q))`, by hand. -/
theorem hS2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d q : ℕ) (hq2 : 2 ≤ q)
    (hq : 1 ≤ padicValNat p q) (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin ((LP p (d - σ.1)).flatMap
            (fun l => blkList p q σ.1 ((d - σ.1 - l) / 2) l)).length) →
          ZMod (p ^ ((LP p (d - σ.1)).flatMap
            (fun l => blkList p q σ.1 ((d - σ.1 - l) / 2) l)).get i))) :=
  S2 hp2 hq2 hq hd

/-- (S1) by hand. -/
theorem hS1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d q : ℕ) (hq2 : 2 ≤ q)
    (hq : 1 ≤ padicValNat p q) (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LP p (d - σ.1)).length) →
          GBlk p q σ.1 ((d - σ.1 - (LP p (d - σ.1)).get t) / 2) ((LP p (d - σ.1)).get t))) :=
  S1 hp2 hq2 hq hd

/-- (X1) the Example, by hand: `Syl_3 K(H(4,3)) ≅ (ℤ/3)² ⊕ (ℤ/9)⁷ ⊕ (ℤ/27)⁸ ⊕ (ℤ/81)¹⁷`. -/
theorem hX1 :
    Nonempty (AddCommGroup.primaryComponent (sandpile 4 3) 3 ≃+
      (Fin 2 → ZMod 3) × (Fin 7 → ZMod 9) × (Fin 8 → ZMod 27) × (Fin 17 → ZMod 81)) :=
  X1

end CheckCSG7

#print axioms CheckCSG7.hL0a
#print axioms CheckCSG7.hL0b
#print axioms CheckCSG7.hL1
#print axioms CheckCSG7.hT1
#print axioms CheckCSG7.hT2
#print axioms CheckCSG7.hF1
#print axioms CheckCSG7.hF2
#print axioms CheckCSG7.hS1
#print axioms CheckCSG7.hS2
#print axioms CheckCSG7.hX1
#print axioms ColouredSand.ThmG.L1
#print axioms ColouredSand.ThmG.L2_val
#print axioms ColouredSand.ThmG.T1
#print axioms ColouredSand.ThmG.T2
#print axioms ColouredSand.ThmG.F1
#print axioms ColouredSand.ThmG.F2
#print axioms ColouredSand.ThmG.S1
#print axioms ColouredSand.ThmG.S2
#print axioms ColouredSand.ThmG.X1
