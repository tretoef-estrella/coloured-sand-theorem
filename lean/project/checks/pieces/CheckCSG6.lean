import RequestProject.BlockOp.All

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
