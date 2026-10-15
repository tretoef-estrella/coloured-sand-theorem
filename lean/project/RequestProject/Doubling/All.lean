module

public import RequestProject.Doubling.Basic
public import RequestProject.Doubling.SL2
public import RequestProject.Doubling.Phi
public import RequestProject.Doubling.PhiOps
public import RequestProject.Doubling.PartAB
public import RequestProject.Doubling.Functor
public import RequestProject.Doubling.WeylBasis
public import RequestProject.Doubling.PartD
public import RequestProject.Doubling.PartD1
public import RequestProject.Doubling.PartD2
public import RequestProject.Doubling.PartD3

/-!
# `C20_the_doubling_functor.md`: index (namespace `Doubling`)

Reused without redefinition: from C18 (namespace `DPLattice`) `DPLattice`, `IsDP`, `H`, `Hom`,
`one`, `V`, `bvec`, `delta`, `nabla`, `T5_delta_zero`, `T5_delta_one`; from C19 (namespace
`WeylFilt`) `Hom.id`, `Hom.comp`, `ShortExact`.

## Encodings

* **Ring** (Setting): `[CommRing A] [IsDomain A] [CharZero A] [OddUnits A]`, where the class
  `OddUnits A` is exactly `hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)`
  (`Basic.lean`); instance check for `ℤ_[2]`: `padicInt_two_hodd` and `instance : OddUnits ℤ_[2]`.
* **Double factorials** (Setting): `k!!` is `Nat.doubleFactorial k`; `⅟(2s−1)!!` is
  `dfi s = Ring.inverse ((2s−1)!! : A)` (so `⅟(−1)!! = dfi 0 = 1` and `⅟(2s+1)!! = dfi (s+1)`).
* **`Π_{c}`** (Setting): `piOp N S c = ∏_{j ∈ S} (4FE + c_j)`, the polynomial
  `∏_{j∈S} (4X + c_j)` evaluated at `F ∘ E` (`F = N.Fd 1`, `E = N.Ed 1`); `S = range s` is
  `0 ≤ j < s`, `S = range (s+1)` is `0 ≤ j ≤ s`, `S = Icc 1 s` is `1 ≤ j ≤ s`.
* **`Φ(N)`** (Setting, `Phi.lean`, `PartAB.lean`): basis `Fin 2 × N.ι`, `b_e n = bvec e n`
  (C18), weights `phiWt N (e,i) = 2 w_i + wtV e` (`2w_i + 1`, `2w_i − 1`). `F^{(r)}`, `E^{(r)}` are
  `phiFd N r`, `phiEd N r`: the closed formulas of the file on the basis vectors `b_e e_i`
  (`phiFdB`, `phiEdB`), extended `A`-linearly (`Basis.constr`); the seven formulas are restated as
  `phiFd_even`, `phiFd_odd_b0`, `phiFd_odd_b1`, `phiEd_even_b1`, `phiEd_odd_b1`, `phiEd_even_b0`,
  `phiEd_odd_b0`. The DP-lattice is `phi N : DPLattice A`.
* **Weight vectors**: "`n` of weight `w`" is C18's `InWt N.wt w n`.
* **`Φ` on morphisms** (`Functor.lean`): `phiLin f` is `1 ⊗ f` (`b_e n ↦ b_e f(n)`) and
  `phiHom f : Hom (phi N) (phi M)` is `Φ(f)`.
* **Isomorphism** (Part D): `Iso M N` — `hom : Hom M N`, `inv : Hom N M` with
  `Hom.comp inv hom = Hom.id M`, `Hom.comp hom inv = Hom.id N`.
* **Part D** (`PartD.lean`, `PartD1.lean`, `PartD2.lean`): `e'_R = eD (2μ+1) R`, `w'_R = eN (2μ+1) R`;
  `x_R` is `xD μ R` (in `Φ(Δ_A(μ))`) or `xN μ R` (in `Φ(∇_A(μ))`), `= b_0 e_s` for `R = 2s` and
  `b_1 e_s` for `R = 2s+1`; `c_R = cD R`, `c_R^{-1} = cDinv R`, `d_R = dN μ R`,
  `d_R^{-1} = dNinv μ R`; `δ_μ = deltaMap μ`, its inverse `deltaInv μ`; `ν_μ = nablaMap μ`, its
  inverse `nablaInv μ`.

## Results

* (A1) `A1`, `phi`, `phi_data`; (A2) `A2`, `phiHom`; (A3) `A3`.
* (B1) `B1`; (B2) `B2`; (B3) `B3`.
* (D1) `D1`, `D1_iso`; (D2) `D2`, `D2_iso`, with the recursion `dN_rec`; (D3) `D3`, `D3'`.
-/
