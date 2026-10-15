module

public import RequestProject.Doubling.SL2

/-!
# `C20_the_doubling_functor.md`: the lattice `Φ(N)` (Setting) and its closed formulas

Encodings:
* `Φ(N)` has basis `Fin 2 × N.ι`; the vector "with `n` in slot `e`" is `b_e n = bvec e n` (C18).
  The basis vector `b_e e_i` is `Pi.single (e, i) 1 = bvec e (Pi.single i 1)`.
* `phiWt N (e, i) = 2 w_i + wtV e`, i.e. `wt(0, i) = 2w_i + 1`, `wt(1, i) = 2w_i − 1`.
* `phiFdB N r (e, i)` and `phiEdB N r (e, i)` are the closed formulas of the file for
  `F^{(r)}(b_e e_i)` and `E^{(r)}(b_e e_i)` (with `s = r / 2` and the parity of `r` deciding between
  `r = 2s` and `r = 2s + 1`); `phiFd N r` and `phiEd N r` are their `A`-linear extensions
  (`Basis.constr` on the standard basis). The closed formulas are restated in the form of the file
  as `phiFd_even`, `phiFd_odd_b0`, `phiFd_odd_b1`, `phiEd_even_b1`, `phiEd_odd_b1`,
  `phiEd_even_b0`, `phiEd_odd_b0`.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset Polynomial

variable {A : Type*} [CommRing A] (N : DPLattice A)

/-- Setting: the weights of `Φ(N)`: `wt(0, i) = 2w_i + 1`, `wt(1, i) = 2w_i − 1`. -/
def phiWt (p : Fin 2 × N.ι) : ℤ := 2 * N.wt p.2 + wtV p.1

/-- Setting: the closed formula for `F^{(r)}(b_e ·)` as a linear map of the slot vector
(`s = r/2`): `F^{(2s)}(b_e n) = ⅟(2s−1)!! · b_e F^{(s)} n`,
`F^{(2s+1)}(b_0 n) = ⅟(2s+1)!! · b_1 F^{(s)} n`,
`F^{(2s+1)}(b_1 n) = (2s+2)·⅟(2s+1)!! · b_0 F^{(s+1)} n`. -/
def phiFdL (r : ℕ) (e : Fin 2) : (N.ι → A) →ₗ[A] (Fin 2 × N.ι → A) :=
  if r % 2 = 0 then dfi (A := A) (r / 2) • (bvec e ∘ₗ N.Fd (r / 2))
  else if e = 0 then dfi (A := A) (r / 2 + 1) • (bvec 1 ∘ₗ N.Fd (r / 2))
  else (((2 * (r / 2) + 2 : ℕ) : A) * dfi (r / 2 + 1)) • (bvec 0 ∘ₗ N.Fd (r / 2 + 1))

/-- Setting: the closed formula for `F^{(r)}(b_e e_i)` (`phiFdL` applied to `e_i`). -/
def phiFdB (r : ℕ) (p : Fin 2 × N.ι) : Fin 2 × N.ι → A := phiFdL N r p.1 (Pi.single p.2 1)

/-- Setting: the closed formula for `E^{(r)}(b_e ·)` on vectors of weight `w`, as a linear map
of the slot vector (`s = r/2`):
`E^{(2s)}(b_1 n) = ⅟(2s−1)!! · b_1 Π_{c}(E^{(s)} n)`, `c_j = (w+2s+1)² − (w+2j)²`, `0 ≤ j < s`;
`E^{(2s+1)}(b_1 n) = ⅟(2s+1)!! · b_0 Π_{c}(E^{(s)} n)`, same `c_j`, `0 ≤ j ≤ s`;
`E^{(2s)}(b_0 n) = ⅟(2s−1)!! · b_0 Π_{c}(E^{(s)} n)`, same `c_j`, `1 ≤ j ≤ s`;
`E^{(2s+1)}(b_0 n) = 2(s+1)·⅟(2s+1)!! · b_1 Π_{c}(E^{(s+1)} n)`,
`c_j = (w+2s+3)² − (w+2j)²`, `1 ≤ j ≤ s`. -/
def phiEdL (r : ℕ) (e : Fin 2) (w : ℤ) : (N.ι → A) →ₗ[A] (Fin 2 × N.ι → A) :=
  if r % 2 = 0 then
    if e = 1 then
      dfi (A := A) (r / 2) • (bvec 1 ∘ₗ piOp N (range (r / 2)) (cE w (r / 2)) ∘ₗ N.Ed (r / 2))
    else
      dfi (A := A) (r / 2) • (bvec 0 ∘ₗ piOp N (Icc 1 (r / 2)) (cE w (r / 2)) ∘ₗ N.Ed (r / 2))
  else
    if e = 1 then
      dfi (A := A) (r / 2 + 1) •
        (bvec 0 ∘ₗ piOp N (range (r / 2 + 1)) (cE w (r / 2)) ∘ₗ N.Ed (r / 2))
    else
      (((2 * (r / 2 + 1) : ℕ) : A) * dfi (r / 2 + 1)) •
        (bvec 1 ∘ₗ piOp N (Icc 1 (r / 2)) (cE w (r / 2 + 1)) ∘ₗ N.Ed (r / 2 + 1))

/-- Setting: the closed formula for `E^{(r)}(b_e e_i)` (`phiEdL` with `w = w_i`, applied to
`e_i`). -/
def phiEdB (r : ℕ) (p : Fin 2 × N.ι) : Fin 2 × N.ι → A :=
  phiEdL N r p.1 (N.wt p.2) (Pi.single p.2 1)

/-- Setting: `F^{(r)}` on `Φ(N)`, the `A`-linear extension of the closed formulas. -/
def phiFd (r : ℕ) : Module.End A (Fin 2 × N.ι → A) :=
  (Pi.basisFun A (Fin 2 × N.ι)).constr A (phiFdB N r)

/-- Setting: `E^{(r)}` on `Φ(N)`, the `A`-linear extension of the closed formulas. -/
def phiEd (r : ℕ) : Module.End A (Fin 2 × N.ι → A) :=
  (Pi.basisFun A (Fin 2 × N.ι)).constr A (phiEdB N r)

lemma phiFd_single (r : ℕ) (p : Fin 2 × N.ι) : phiFd N r (Pi.single p 1) = phiFdB N r p := by
  rw [phiFd, ← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma phiEd_single (r : ℕ) (p : Fin 2 × N.ι) : phiEd N r (Pi.single p 1) = phiEdB N r p := by
  rw [phiEd, ← Pi.basisFun_apply A, Module.Basis.constr_basis]

lemma two_mul_mod (s : ℕ) : 2 * s % 2 = 0 := by omega
lemma two_mul_div (s : ℕ) : 2 * s / 2 = s := by omega
lemma two_mul_add_one_mod (s : ℕ) : (2 * s + 1) % 2 = 1 := by omega
lemma two_mul_add_one_div (s : ℕ) : (2 * s + 1) / 2 = s := by omega

/-! ### The closed formulas on basis vectors (Setting) -/

/-- Setting: `F^{(2s)}(b_e e_i) = ⅟(2s−1)!! · b_e F^{(s)} e_i`. -/
theorem phiFd_even (s : ℕ) (e : Fin 2) (i : N.ι) :
    phiFd N (2 * s) (bvec e (Pi.single i 1)) = dfi (A := A) s • bvec e (N.Fd s (Pi.single i 1)) := by
  rw [← single_eq_bvec, phiFd_single, phiFdB, phiFdL, if_pos (two_mul_mod s), two_mul_div]
  rfl

/-- Setting: `F^{(2s+1)}(b_0 e_i) = ⅟(2s+1)!! · b_1 F^{(s)} e_i`. -/
theorem phiFd_odd_b0 (s : ℕ) (i : N.ι) :
    phiFd N (2 * s + 1) (bvec 0 (Pi.single i 1)) =
      dfi (A := A) (s + 1) • bvec 1 (N.Fd s (Pi.single i 1)) := by
  rw [← single_eq_bvec, phiFd_single, phiFdB, phiFdL, two_mul_add_one_mod, two_mul_add_one_div]
  simp

/-- Setting: `F^{(2s+1)}(b_1 e_i) = (2s+2)·⅟(2s+1)!! · b_0 F^{(s+1)} e_i`. -/
theorem phiFd_odd_b1 (s : ℕ) (i : N.ι) :
    phiFd N (2 * s + 1) (bvec 1 (Pi.single i 1)) =
      (((2 * s + 2 : ℕ) : A) * dfi (s + 1)) • bvec 0 (N.Fd (s + 1) (Pi.single i 1)) := by
  rw [← single_eq_bvec, phiFd_single, phiFdB, phiFdL, two_mul_add_one_mod, two_mul_add_one_div]
  simp

/-- Setting: `E^{(2s)}(b_1 e_i) = ⅟(2s−1)!! · b_1 Π_{c}(E^{(s)} e_i)`,
`c_j = (w_i+2s+1)² − (w_i+2j)²`, `0 ≤ j < s`. -/
theorem phiEd_even_b1 (s : ℕ) (i : N.ι) :
    phiEd N (2 * s) (bvec 1 (Pi.single i 1)) =
      dfi (A := A) s • bvec 1 (piOp N (range s) (fun j => (N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2)
        (N.Ed s (Pi.single i 1))) := by
  rw [← single_eq_bvec, phiEd_single, phiEdB, phiEdL, if_pos (two_mul_mod s), two_mul_div]
  rw [if_pos rfl]; rfl

/-- Setting: `E^{(2s+1)}(b_1 e_i) = ⅟(2s+1)!! · b_0 Π_{c}(E^{(s)} e_i)`,
`c_j = (w_i+2s+1)² − (w_i+2j)²`, `0 ≤ j ≤ s`. -/
theorem phiEd_odd_b1 (s : ℕ) (i : N.ι) :
    phiEd N (2 * s + 1) (bvec 1 (Pi.single i 1)) =
      dfi (A := A) (s + 1) • bvec 0 (piOp N (range (s + 1))
        (fun j => (N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2) (N.Ed s (Pi.single i 1))) := by
  rw [← single_eq_bvec, phiEd_single, phiEdB, phiEdL, two_mul_add_one_mod, two_mul_add_one_div]
  rw [if_neg one_ne_zero, if_pos rfl]; rfl

/-- Setting: `E^{(2s)}(b_0 e_i) = ⅟(2s−1)!! · b_0 Π_{c}(E^{(s)} e_i)`,
`c_j = (w_i+2s+1)² − (w_i+2j)²`, `1 ≤ j ≤ s`. -/
theorem phiEd_even_b0 (s : ℕ) (i : N.ι) :
    phiEd N (2 * s) (bvec 0 (Pi.single i 1)) =
      dfi (A := A) s • bvec 0 (piOp N (Icc 1 s) (fun j => (N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2)
        (N.Ed s (Pi.single i 1))) := by
  rw [← single_eq_bvec, phiEd_single, phiEdB, phiEdL, if_pos (two_mul_mod s), two_mul_div]
  rw [if_neg (show ((0 : Fin 2) ≠ 1) by decide)]; rfl

/-- Setting: `E^{(2s+1)}(b_0 e_i) = 2(s+1)·⅟(2s+1)!! · b_1 Π_{c}(E^{(s+1)} e_i)`,
`c_j = (w_i+2s+3)² − (w_i+2j)²`, `1 ≤ j ≤ s`. -/
theorem phiEd_odd_b0 (s : ℕ) (i : N.ι) :
    phiEd N (2 * s + 1) (bvec 0 (Pi.single i 1)) =
      (((2 * (s + 1) : ℕ) : A) * dfi (s + 1)) • bvec 1 (piOp N (Icc 1 s)
        (fun j => (N.wt i + 2 * s + 3) ^ 2 - (N.wt i + 2 * j) ^ 2)
        (N.Ed (s + 1) (Pi.single i 1))) := by
  rw [← single_eq_bvec, phiEd_single, phiEdB, phiEdL, two_mul_add_one_mod, two_mul_add_one_div]
  have hc : cE (N.wt i) (s + 1) = fun j : ℕ => (N.wt i + 2 * s + 3) ^ 2 - (N.wt i + 2 * j) ^ 2 := by
    funext j; simp only [cE]; push_cast; ring
  simp [hc]

end Doubling
