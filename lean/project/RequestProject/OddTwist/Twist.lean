module

public import RequestProject.OddTwist.Basic

/-!
# `CSI1_the_odd_twist.md`: Setting — the lattice `Φ_p(N)` and its closed formulas

Encodings (`N : DPLattice ℤ_[p]`, `w_i = N.wt i`, `e_i = Pi.single i 1`, `F = N.Fd 1`,
`E = N.Ed 1`, `X = F ∘ E`):

* `Φ_p(N)` has basis `Fin p × N.ι`; the vector with `n` in slot `j` is `b_j n = bv p j n`, and the
  basis vector `b_j e_i` is `Pi.single (j, i) 1 = bv p j (Pi.single i 1)` (`single_eq_bv`).
* `twWt p N (j, i) = p·w_i + p − 1 − 2j`.
* `Sset p j r` is the finite set `S(j, r)` of pairs `(a, k)` with `1 ≤ k ≤ p − 1`, `a ≥ 0`,
  `(a = 0 → k ≤ j)` and `j − k + a·p < r`; the last condition is written without subtraction as
  `j + p·a < r + k` (natural numbers), see `mem_Sset`.
* `pFactor p w (a, k)` is the polynomial `p²·X + (k − p·a)·(p·(w + 1 + a) − k)` (integer
  coefficients, in `ℤ_[p][X]`) and `PP p N w S = ∏_{(a,k) ∈ S} (p²·X + (k − p·a)(p(w+1+a) − k))`
  is the product of these polynomials evaluated at the operator `X = F ∘ E` of `N` (so the
  factors commute and the empty product is the identity). `P_{j,r}` of the file (for `e_i`) is
  `PP p N w_i (Sset p j r)`.
* `cFr p j r = (j + r) / p` and `cEr p j r = (r + p − 1 − j) / p` are the integers `c` of the two
  closed formulas.
* `twFdL p N r j` and `twEdL p N r j w` are the closed formulas for `F^{(r)}(b_j ·)` and
  `E^{(r)}(b_j ·)` (on vectors of weight `w` for `E`) as linear maps of the slot vector:
  `F^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{(j+r) mod p} F^{(c)} n`, `c = (j+r)/p`, and
  `E^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{j + pc − r} E^{(c)} P_{j,r}(n)`, `c = (r+p−1−j)/p`.
  (Here `(j+r) mod p = j + r − pc` and `j + pc − r = j − r + pc`, see `twFd_single`,
  `twEd_single`.)
* `twFd p N r`, `twEd p N r` are the `ℤ_[p]`-linear extensions of the closed formulas on the
  basis vectors `b_j e_i` (`Basis.constr`). The DP-lattice `twist p N` is built in
  `PartAB.lean`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Polynomial

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- Setting: the weights of `Φ_p(N)`, `wt(j, i) = p·w_i + p − 1 − 2j`. -/
def twWt (x : Fin p × N.ι) : ℤ := p * N.wt x.2 + p - 1 - 2 * ((x.1 : ℕ) : ℤ)

/-- Setting: the set `S(j, r) = {(a, k) : 1 ≤ k ≤ p − 1, a ≥ 0, (a = 0 → k ≤ j),
j − k + a·p < r}` (the last condition written as `j + p·a < r + k`; the bound `a ≤ r` used to make
the set finite is automatic, see `mem_Sset`). -/
def Sset (j r : ℕ) : Finset (ℕ × ℕ) :=
  ((range (r + 1)) ×ˢ (Icc 1 (p - 1))).filter
    (fun ak => (ak.1 = 0 → ak.2 ≤ j) ∧ j + p * ak.1 < r + ak.2)

omit [Fact p.Prime] in
lemma mem_Sset (hp : 1 ≤ p) (j r : ℕ) (ak : ℕ × ℕ) :
    ak ∈ Sset p j r ↔ 1 ≤ ak.2 ∧ ak.2 ≤ p - 1 ∧ (ak.1 = 0 → ak.2 ≤ j) ∧ j + p * ak.1 < r + ak.2 := by
  obtain ⟨a, k⟩ := ak
  simp only [Sset, mem_filter, mem_product, mem_range, mem_Icc]
  constructor
  · rintro ⟨⟨-, h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, h1, h2⟩, h3, h4⟩
    by_contra ha
    have : p * (r + 1) ≤ p * a := Nat.mul_le_mul_left _ (by omega)
    have : p * (r + 1) = p * r + p := by ring
    have : r ≤ p * r := Nat.le_mul_of_pos_left r hp
    omega

/-- Setting: the factor `p²·X + (k − p·a)·(p·(w + 1 + a) − k)` of `P_{j,r}` (a polynomial with
integer coefficients). -/
def pFactor (w : ℤ) (ak : ℕ × ℕ) : ℤ_[p][X] :=
  C ((p : ℤ_[p]) ^ 2) * X +
    C (((((ak.2 : ℕ) : ℤ) - p * (ak.1 : ℕ)) * (p * (w + 1 + (ak.1 : ℕ)) - (ak.2 : ℕ)) : ℤ) : ℤ_[p])

/-- Setting: `∏_{(a,k) ∈ S} (p²·X + (k − p·a)(p(w+1+a) − k))` evaluated at `X = F ∘ E` of `N`. -/
def PP (w : ℤ) (S : Finset (ℕ × ℕ)) : Module.End ℤ_[p] (N.ι → ℤ_[p]) :=
  aeval (N.Fd 1 * N.Ed 1) (∏ ak ∈ S, pFactor p w ak)

/-- Setting: `c = (j + r) / p` in the formula for `F^{(r)}(b_j ·)`. -/
def cFr (j r : ℕ) : ℕ := (j + r) / p

/-- Setting: `c = (r + p − 1 − j) / p` in the formula for `E^{(r)}(b_j ·)`. -/
def cEr (j r : ℕ) : ℕ := (r + p - 1 - j) / p

/-- Setting: the closed formula `F^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{(j+r) mod p} F^{(c)} n`,
`c = (j + r)/p`, as a linear map of `n`. -/
def twFdL (r j : ℕ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × N.ι → ℤ_[p]) :=
  ((-1 : ℤ_[p]) ^ cFr p j r * qc p (cFr p j r) r) • (bv p ((j + r) % p) ∘ₗ N.Fd (cFr p j r))

/-- Setting: the closed formula `E^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{j+pc−r} E^{(c)} P_{j,r}(n)`,
`c = (r + p − 1 − j)/p`, as a linear map of `n` (for `n` of weight `w`). -/
def twEdL (r j : ℕ) (w : ℤ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × N.ι → ℤ_[p]) :=
  ((-1 : ℤ_[p]) ^ cEr p j r * qc p (cEr p j r) r) •
    (bv p (j + p * cEr p j r - r) ∘ₗ N.Ed (cEr p j r) ∘ₗ PP p N w (Sset p j r))

/-- Setting: the closed formula for `F^{(r)}(b_j e_i)`. -/
def twFdB (r : ℕ) (x : Fin p × N.ι) : Fin p × N.ι → ℤ_[p] := twFdL p N r x.1 (Pi.single x.2 1)

/-- Setting: the closed formula for `E^{(r)}(b_j e_i)` (with `w = w_i`). -/
def twEdB (r : ℕ) (x : Fin p × N.ι) : Fin p × N.ι → ℤ_[p] :=
  twEdL p N r x.1 (N.wt x.2) (Pi.single x.2 1)

/-- Setting: `F^{(r)}` on `Φ_p(N)`, the `ℤ_[p]`-linear extension of the closed formulas. -/
def twFd (r : ℕ) : Module.End ℤ_[p] (Fin p × N.ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin p × N.ι)).constr ℤ_[p] (twFdB p N r)

/-- Setting: `E^{(r)}` on `Φ_p(N)`, the `ℤ_[p]`-linear extension of the closed formulas. -/
def twEd (r : ℕ) : Module.End ℤ_[p] (Fin p × N.ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin p × N.ι)).constr ℤ_[p] (twEdB p N r)

lemma twFd_pi_single (r : ℕ) (x : Fin p × N.ι) : twFd p N r (Pi.single x 1) = twFdB p N r x := by
  rw [twFd, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma twEd_pi_single (r : ℕ) (x : Fin p × N.ι) : twEd p N r (Pi.single x 1) = twEdB p N r x := by
  rw [twEd, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

/-- Setting: the closed formula for `F^{(r)}` on basis vectors:
`F^{(r)}(b_j e_i) = (−1)^c · q(c, r) · b_{j+r−pc} F^{(c)} e_i`, `c = (j + r)/p`. -/
theorem twFd_single (r : ℕ) (j : Fin p) (i : N.ι) :
    twFd p N r (bv p j (Pi.single i 1)) =
      ((-1 : ℤ_[p]) ^ ((j + r) / p) * qc p ((j + r) / p) r) •
        bv p (j + r - p * ((j + r) / p)) (N.Fd ((j + r) / p) (Pi.single i 1)) := by
  rw [← single_eq_bv, twFd_pi_single, twFdB, twFdL, ← Nat.mod_eq_sub_mul_div]
  rfl

/-- Setting: the closed formula for `E^{(r)}` on basis vectors:
`E^{(r)}(b_j e_i) = (−1)^c · q(c, r) · b_{j−r+pc} E^{(c)} P_{j,r}(e_i)`, `c = (r + p − 1 − j)/p`,
`P_{j,r} = ∏_{(a,k) ∈ S(j,r)} (p²X + (k − pa)(p(w_i + 1 + a) − k))`. -/
theorem twEd_single (r : ℕ) (j : Fin p) (i : N.ι) :
    twEd p N r (bv p j (Pi.single i 1)) =
      ((-1 : ℤ_[p]) ^ ((r + p - 1 - j) / p) * qc p ((r + p - 1 - j) / p) r) •
        bv p (j + p * ((r + p - 1 - j) / p) - r)
          (N.Ed ((r + p - 1 - j) / p) (PP p N (N.wt i) (Sset p j r) (Pi.single i 1))) := by
  rw [← single_eq_bv, twEd_pi_single, twEdB, twEdL]
  rfl

end ColouredSand.OddTwist
