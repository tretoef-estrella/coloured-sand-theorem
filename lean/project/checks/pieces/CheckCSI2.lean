import RequestProject.OddTwistModP.All

/-!
# CheckCSI2 (Grepy Sand, 14 Oct 2026)

Hand restatement of CSI2 (`CSI2_reduction_mod_p.md`): Lucas at `p` (T0), the Frobenius twist
`frobP` written out (weights `p·wt`, `F^{(r)} = F^{(r/p)}` if `p ∣ r`, else `0`), the Steinberg
lattice `St = baseChange g0 Δ(p−1)`, Wilson (C0), the formulas mod `p` (C1), the diagonal map
`D(b_j e_i) = j!·(e_j ⊗ e_i)` with the isomorphism (C2), and the case of the paper (C3) with
`ZMod p`, `PadicInt.toZMod` and `delta ℤ_[p] (p − 1)` written out. Then `#print axioms`.
-/

namespace CheckCSI2

open ColouredSand.OddTwist DPLattice

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime]

/-- (T0) by hand. -/
theorem hT0 (hp : (p : B) = 0) (x : ℤ) (j : ℕ) :
    ((Ring.choose ((p : ℤ) * x) (p * j) : ℤ) : B) = ((Ring.choose x j : ℤ) : B) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ p - 1 → ((Ring.choose ((p : ℤ) * x) (p * j + t) : ℤ) : B) = 0 :=
  T0 hp x j

/-- The Frobenius twist written out. -/
theorem hFrob (hp : (p : B) = 0) (M : DPLattice B) :
    (frobP hp M).ι = M.ι ∧ (∀ i, (frobP hp M).wt i = (p : ℤ) * M.wt i) ∧
    (∀ r, (frobP hp M).Fd r = if p ∣ r then M.Fd (r / p) else 0) ∧
    (∀ r, (frobP hp M).Ed r = if p ∣ r then M.Ed (r / p) else 0) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `St` is the base change of `Δ(p − 1)`. -/
theorem hSt (g0 : ℤ_[p] →+* B) : St g0 = Twist.baseChange g0 (delta ℤ_[p] (p - 1)) := rfl

/-- (C0) Wilson, by hand. -/
theorem hC0 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (c t : ℕ) (ht : t ≤ p - 1) :
    g0 (qc p c (p * c + t)) * ((Nat.factorial t : ℕ) : B) = (-1) ^ c ∧
    ∀ c' : ℕ, c + 1 ≤ c' → g0 (qc p c' (p * c + t)) = 0 :=
  C0 hp g0 c t ht

/-- (C1) by hand. -/
theorem hC1 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (N : DPLattice ℤ_[p]) (c t : ℕ) (ht : t ≤ p - 1)
    (j : ℕ) (hj : j < p) (n : N.ι → B) :
    (j + t ≤ p - 1 → ((Nat.factorial t : ℕ) : B) • (Twist.baseChange g0 (twist p N)).Fd (p * c + t) (bv p j n) =
      bv p (j + t) ((Twist.baseChange g0 N).Fd c n)) ∧
    (p - 1 < j + t → (Twist.baseChange g0 (twist p N)).Fd (p * c + t) (bv p j n) = 0) ∧
    (t ≤ j → ((Nat.factorial (j - t) : ℕ) : B) • (Twist.baseChange g0 (twist p N)).Ed (p * c + t) (bv p j n) =
      (((Nat.factorial j : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        bv p (j - t) ((Twist.baseChange g0 N).Ed c n)) ∧
    (j < t → (Twist.baseChange g0 (twist p N)).Ed (p * c + t) (bv p j n) = 0) :=
  oddModP_C1 hp g0 N c t ht j hj n

/-- (C2) by hand: `D(b_j e_i) = j!·(e_j ⊗ e_i)` and the isomorphism with `St ⊗ N̄^{[1]}`. -/
theorem hC2 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (N : DPLattice ℤ_[p]) :
    (∀ (j : ℕ) (hj : j < p - 1 + 1) (i : N.ι),
      Dmap B p N.ι (bv p j (Pi.single i 1)) =
        ((Nat.factorial j : ℕ) : B) • Tensor2.tprod (Pi.single (⟨j, hj⟩ : Fin (p - 1 + 1)) 1)
          (Pi.single i 1)) ∧
    ∃ u : Doubling.Iso (Twist.baseChange g0 (twist p N))
        (Tensor2.tensor (Twist.baseChange g0 (delta ℤ_[p] (p - 1)))
          (frobP hp (Twist.baseChange g0 N))),
      u.hom.toLin = Dmap B p N.ι ∧ u.inv.toLin = Dinv B p N.ι :=
  oddModP_C2 hp g0 N

/-- (C3) the case of the paper, by hand. -/
theorem hC3 (N : DPLattice ℤ_[p]) :
    Nonempty (Doubling.Iso (Twist.baseChange PadicInt.toZMod (twist p N))
      (Tensor2.tensor (Twist.baseChange PadicInt.toZMod (delta ℤ_[p] (p - 1)))
        (frobP (ZMod.natCast_self p) (Twist.baseChange PadicInt.toZMod N)))) :=
  oddModP_C3 N

end CheckCSI2

#print axioms CheckCSI2.hT0
#print axioms CheckCSI2.hFrob
#print axioms CheckCSI2.hSt
#print axioms CheckCSI2.hC0
#print axioms CheckCSI2.hC1
#print axioms CheckCSI2.hC2
#print axioms CheckCSI2.hC3
#print axioms ColouredSand.OddTwist.T1
#print axioms ColouredSand.OddTwist.T2
#print axioms ColouredSand.OddTwist.oddModP_S1
#print axioms ColouredSand.OddTwist.C3_hyp
#print axioms ColouredSand.OddTwist.prop12Iso
