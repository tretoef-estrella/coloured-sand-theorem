-- CheckColouredSandFinal2A4.lean (part A4 of half A: every import, pieces 13-15) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
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

-- ======== piece CSG6 (from lean/proyecto_cubo/checks/CheckCSG6.lean) ========
namespace FinalCheck.CSG6

/-!
# CheckCSG6 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG6 (`CSG6_operator_on_the_blocks.md`): the operator written out by hand
(`F^{(1)} + q (c + (m − h)/2)` with `2 · half = 1`), the dictionary (K2), the decomposition of the
cokernel (K4), the matrices (E1), (E2), and the groups of the blocks (G1) with `k = (m − λ)/2`
written by hand, checked against the certified theorems of `ColouredSand.BlockOp`.
Then `#print axioms`.
-/

namespace CheckCSG6

open ColouredSand.Strings ColouredSand.ThmH ColouredSand.TiltP ColouredSand.TiltDec
  ColouredSand.Blocks ColouredSand.BlockOp DPLattice

/-- The operator by hand: `opT M m q c v = F^{(1)} v + q (c v + half (m v − H v))`. -/
theorem hOp (p : ℕ) [Fact p.Prime] (M : DPLattice ℤ_[p]) (m q c : ℕ) (v : M.ι → ℤ_[p]) :
    opT p M m q c v = M.Fd 1 v + (q : ℤ_[p]) • ((c : ℤ_[p]) • v +
      half p • ((m : ℤ_[p]) • v - DPLattice.H M v)) := rfl

/-- `half` by hand: `2 * half = 1` for `p ≠ 2`. -/
theorem hHalf (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ℤ_[p]) * half p = 1 :=
  two_mul_half hp2

/-- (K2) by hand. -/
theorem hK2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m q c : ℕ) (f : B m ℤ_[p]) :
    Psi ℤ_[p] m (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]) f) =
      opT p (Filt.tpow ℤ_[p] m) m q c (Psi ℤ_[p] m f) :=
  LinearMap.congr_fun (K2 hp2 m q c) f

/-- (K4) by hand: for `m ≤ p² + p − 1`. -/
theorem hK4 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) (hm : m ≤ p ^ 2 + p - 1) (q c : ℕ) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((j : Fin (LP p m).length) → ((Ttilt p ((LP p m).get j)).ι → ℤ_[p]) ⧸
        LinearMap.range (opT p (Ttilt p ((LP p m).get j)) m q c))) :=
  K4 hp2 hm q c

/-- (E1) by hand, at `m = λ + 2k`. -/
theorem hE1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (l k q c : ℕ) :
    opT p (delta ℤ_[p] l) (l + 2 * k) q c = Matrix.mulVecLin (Mch p q c k l) :=
  E1 hp2 l k q c

/-- (E2) by hand, `λ = p − 1 + r + p a`. -/
theorem hE2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (r a : ℕ) (h : GlueHyp p r a) (k q c : ℕ) :
    opT p (Tglue p r a) (p - 1 + r + p * a + 2 * k) q c = Matrix.mulVecLin (Mblk p q c k r a) :=
  E2 hp2 h k q c

/-- (G1)(a) by hand: `λ ≤ p − 1`, `c + (m − λ)/2 ≥ 1`. -/
theorem hG1a (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q c l m : ℕ) (hq : 1 ≤ padicValNat p q)
    (hl : l ≤ p - 1) (hle : l ≤ m) (hpar : l % 2 = m % 2) (hck : 1 ≤ c + (m - l) / 2) :
    Nonempty ((((Ttilt p l).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p l) m q c)) ≃+
      ZMod (p ^ (∑ t ∈ Finset.range (l + 1),
        (padicValNat p q + padicValNat p (c + (m - l) / 2 + t))))) :=
  (G1a hp2 hq hl hle hpar).1 hck

/-- (G1)(c) by hand: two Weyl factors, `c + (m − λ)/2 ≥ 1`. -/
theorem hG1c (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (q c l m : ℕ) (hq : 1 ≤ padicValNat p q)
    (hl : l ≤ p ^ 2 + p - 1) (hns : ¬ (l ≤ p - 1 ∨ (p ∣ l + 1 ∧ l ≤ p ^ 2 - 1)))
    (hle : l ≤ m) (hpar : l % 2 = m % 2) (hck : 1 ≤ c + (m - l) / 2) :
    Nonempty ((((Ttilt p l).ι → ℤ_[p]) ⧸ LinearMap.range (opT p (Ttilt p l) m q c)) ≃+
      (Fin (2 * ((l - p) / p)) → ZMod p) ×
        ZMod (p ^ blkX p q c ((m - l) / 2) ((l - p) % p + 1) ((l - p) / p)) ×
        ZMod (p ^ blkY p q c ((m - l) / 2) ((l - p) % p + 1) ((l - p) / p))) :=
  (G1c hp2 hq hl hns hle hpar).1 hck

/-- (G2) by hand: every summand is in the range of (G1). -/
theorem hG2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) (hm : m ≤ p ^ 2 + p - 1) (q c : ℕ)
    (j : Fin (LP p m).length) :
    (LP p m).get j ≤ m ∧ (LP p m).get j % 2 = m % 2 ∧ (LP p m).get j ≤ p ^ 2 + p - 1 :=
  (G2 hp2 hm q c).2 j

end CheckCSG6

#print axioms CheckCSG6.hOp
#print axioms CheckCSG6.hHalf
#print axioms CheckCSG6.hK2
#print axioms CheckCSG6.hK4
#print axioms CheckCSG6.hE1
#print axioms CheckCSG6.hE2
#print axioms CheckCSG6.hG1a
#print axioms CheckCSG6.hG1c
#print axioms CheckCSG6.hG2
#print axioms ColouredSand.BlockOp.K3a
#print axioms ColouredSand.BlockOp.K3b
#print axioms ColouredSand.BlockOp.E3a
#print axioms ColouredSand.BlockOp.E3b
#print axioms ColouredSand.BlockOp.G1b
#print axioms ColouredSand.BlockOp.E1_false_at_two

end FinalCheck.CSG6

-- ======== piece CSG7 (from lean/proyecto_cubo/checks/CheckCSG7.lean) ========
namespace FinalCheck.CSG7

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

end FinalCheck.CSG7

-- ======== piece CSI1 (from lean/proyecto_cubo/checks/CheckCSI1.lean) ========
namespace FinalCheck.CSI1

/-!
# CheckCSI1 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSI1 (`CSI1_the_odd_twist.md`): the coefficient `q(c, r)` (A0), the weights
of `Φ_p(N)` written by hand, the single operators (B1) with `g_j = p²X + j(pw + p − j)` written out,
the closed formulas (B3) with `c = ⌊(j+r)/p⌋`, `c = ⌊(r+p−1−j)/p⌋` and the factor of `P_{j,r}`
written out, (B2), the functor (A2), exactness (A3), and the isomorphisms (D1), (D2), (D3),
checked against the certified theorems of `ColouredSand.OddTwist`. Then `#print axioms`.
-/

namespace CheckCSI1

open ColouredSand.OddTwist DPLattice Doubling WeylFilt Polynomial

open scoped Nat

/-- (A0) by hand: `r! · q(c, r) = p^c · c!` and `q(c, r) = p^c c!/r!` in `ℚ_[p]`, for `r/p ≤ c`. -/
theorem hA0 (p : ℕ) [Fact p.Prime] (c r : ℕ) (h : r / p ≤ c) :
    ((r ! : ℕ) : ℤ_[p]) * qc p c r = (p : ℤ_[p]) ^ c * ((c ! : ℕ) : ℤ_[p]) ∧
    ((qc p c r : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ c * ((c ! : ℕ) : ℚ_[p]) / ((r ! : ℕ) : ℚ_[p]) :=
  ⟨(A0 p h).2.2, (A0 p h).2.1⟩

/-- The weights of `Φ_p(N)` by hand. -/
theorem hWt (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p]) (j : Fin p) (i : N.ι) :
    (twist p N).wt (j, i) = (p : ℤ) * N.wt i + p - 1 - 2 * (j : ℤ) := rfl

/-- The factor of `P_{j,r}` by hand: `p²X + (k − pa)(p(w+1+a) − k)`. -/
theorem hFactor (p : ℕ) [Fact p.Prime] (w : ℤ) (a k : ℕ) :
    pFactor p w (a, k) = C ((p : ℤ_[p]) ^ 2) * X +
      C ((((k : ℤ) - p * a) * (p * (w + 1 + a) - k) : ℤ) : ℤ_[p]) := rfl

/-- `S(j, r)` by hand. -/
theorem hS (p : ℕ) [Fact p.Prime] (j r a k : ℕ) :
    (a, k) ∈ Sset p j r ↔ 1 ≤ k ∧ k ≤ p - 1 ∧ (a = 0 → k ≤ j) ∧ j + p * a < r + k :=
  mem_Sset p (Fact.out : p.Prime).one_lt.le j r (a, k)

/-- (B1) by hand: the single operators. -/
theorem hB1 (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p]) :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), j + 1 < p → (twist p N).Fd 1 (bv p j n) = bv p (j + 1) n) ∧
    (∀ n : N.ι → ℤ_[p], (twist p N).Fd 1 (bv p (p - 1) n) = (-(p : ℤ_[p])) • bv p 0 (N.Fd 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), 1 ≤ j → j < p → InWt N.wt w n →
      (twist p N).Ed 1 (bv p j n) = bv p (j - 1)
        ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) + (((j : ℤ) * (p * w + p - j) : ℤ) : ℤ_[p]) • n)) ∧
    (∀ n : N.ι → ℤ_[p], (twist p N).Ed 1 (bv p 0 n) = (-(p : ℤ_[p])) • bv p (p - 1) (N.Ed 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n →
      H (twist p N) (bv p j n) = ((p * w + p - 1 - 2 * j : ℤ) : ℤ_[p]) • bv p j n) :=
  B1 p N

/-- (B2) by hand: `r! F^{(r)} = F^r`, `r! E^{(r)} = E^r`. -/
theorem hB2 (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p]) (r : ℕ) :
    ((r ! : ℕ) : ℤ_[p]) • (twist p N).Fd r = (twist p N).Fd 1 ^ r ∧
    ((r ! : ℕ) : ℤ_[p]) • (twist p N).Ed r = (twist p N).Ed 1 ^ r :=
  B2 p N r

/-- (B3) by hand: the closed formulas, with `P_{j,r}` written as the product of the factors
evaluated at `X = F E`. -/
theorem hB3 (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p]) (r j : ℕ) (hj : j < p) :
    (∀ n : N.ι → ℤ_[p], (twist p N).Fd r (bv p j n) =
      ((-1 : ℤ_[p]) ^ ((j + r) / p) * qc p ((j + r) / p) r) •
        bv p (j + r - p * ((j + r) / p)) (N.Fd ((j + r) / p) n)) ∧
    (∀ (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n → (twist p N).Ed r (bv p j n) =
      ((-1 : ℤ_[p]) ^ ((r + p - 1 - j) / p) * qc p ((r + p - 1 - j) / p) r) •
        bv p (j + p * ((r + p - 1 - j) / p) - r)
          (N.Ed ((r + p - 1 - j) / p)
            (aeval (N.Fd 1 * N.Ed 1) (∏ ak ∈ Sset p j r, pFactor p w ak) n))) :=
  B3 p N r j hj

/-- (A2) by hand: `Φ_p(f)(b_j n) = b_j f(n)`, identity, composition. -/
theorem hA2 (p : ℕ) [Fact p.Prime] :
    (∀ {N M : DPLattice ℤ_[p]} (f : Hom N M) (j : ℕ) (n : N.ι → ℤ_[p]),
      (twistHom p f).toLin (bv p j n) = bv p j (f.toLin n)) ∧
    (∀ N : DPLattice ℤ_[p], twistHom p (Hom.id N) = Hom.id (twist p N)) ∧
    (∀ {N M P : DPLattice ℤ_[p]} (g : Hom M P) (f : Hom N M),
      twistHom p (Hom.comp g f) = Hom.comp (twistHom p g) (twistHom p f)) :=
  A2 p

/-- (A3) by hand. -/
theorem hA3 (p : ℕ) [Fact p.Prime] {X Y Z : DPLattice ℤ_[p]} {f : Hom X Y} {g : Hom Y Z}
    (h : ShortExact f g) : ShortExact (twistHom p f) (twistHom p g) :=
  A3 p h

/-- (D1) by hand: `Φ_p(Δ(μ)) ≅ Δ(pμ + p − 1)`, the map `e'_R ↦ c_R b_{R mod p} e_{R/p}`. -/
theorem hD1 (p : ℕ) [Fact p.Prime] (μ : ℕ) :
    (∀ R : Fin (p * μ + p - 1 + 1), deltaMap p μ (eD (p * μ + p - 1) R) =
      cD p (R : ℕ) • bv p ((R : ℕ) % p) (eD μ ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩)) ∧
    Nonempty (Iso (twist p (delta ℤ_[p] μ)) (delta ℤ_[p] (p * μ + p - 1))) :=
  ⟨(D1 p μ).1, D1_iso p μ⟩

/-- (D1) the coefficients `c_R` by hand. -/
theorem hcD (p : ℕ) [Fact p.Prime] :
    cD p 0 = 1 ∧
    (∀ R : ℕ, R % p ≤ p - 2 → (((R + 1 : ℕ)) : ℤ_[p]) * cD p (R + 1) = cD p R) ∧
    (∀ R : ℕ, R % p = p - 1 → cD p (R + 1) = -cD p R) ∧ (∀ R : ℕ, IsUnit (cD p R)) :=
  ⟨(D1 p 0).2.1, fun R h => ((D1 p 0).2.2.1 R h).2, (D1 p 0).2.2.2.1, (D1 p 0).2.2.2.2.1⟩

/-- (D2) by hand. -/
theorem hD2 (p : ℕ) [Fact p.Prime] (μ : ℕ) :
    Nonempty (Iso (twist p (nabla ℤ_[p] μ)) (nabla ℤ_[p] (p * μ + p - 1))) ∧
    (∀ R : ℕ, R % p = p - 1 → dN p μ (R + 1) = -dN p μ R) :=
  ⟨D2_iso p μ, (D2 p μ).2.2.2.1⟩

/-- (D3) by hand. -/
theorem hD3 (p : ℕ) [Fact p.Prime] :
    Nonempty (Iso (twist p (one ℤ_[p])) (delta ℤ_[p] (p - 1))) := D3 p

end CheckCSI1

#print axioms CheckCSI1.hA0
#print axioms CheckCSI1.hWt
#print axioms CheckCSI1.hFactor
#print axioms CheckCSI1.hS
#print axioms CheckCSI1.hB1
#print axioms CheckCSI1.hB2
#print axioms CheckCSI1.hB3
#print axioms CheckCSI1.hA2
#print axioms CheckCSI1.hA3
#print axioms CheckCSI1.hD1
#print axioms CheckCSI1.hcD
#print axioms CheckCSI1.hD2
#print axioms CheckCSI1.hD3
#print axioms ColouredSand.OddTwist.A1
#print axioms ColouredSand.OddTwist.D1
#print axioms ColouredSand.OddTwist.D2

end FinalCheck.CSI1
