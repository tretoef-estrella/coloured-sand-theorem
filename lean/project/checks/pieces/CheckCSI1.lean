import RequestProject.OddTwist.All

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
