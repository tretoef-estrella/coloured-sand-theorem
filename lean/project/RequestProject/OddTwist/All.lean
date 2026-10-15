module

public import RequestProject.OddTwist.Basic
public import RequestProject.OddTwist.Twist
public import RequestProject.OddTwist.Ops
public import RequestProject.OddTwist.PartAB
public import RequestProject.OddTwist.Functor
public import RequestProject.OddTwist.PartD
public import RequestProject.OddTwist.PartD1
public import RequestProject.OddTwist.PartD2
public import RequestProject.OddTwist.PartD3

/-!
# `CSI1_the_odd_twist.md`: index (namespace `ColouredSand.OddTwist`)

The odd twist functor `Φ_p` (Definition 1.1, Proposition 1.2 (a), (b), (d)), following C20
(`RequestProject/Doubling/`) with `2` replaced by a prime `p`.

Reused without redefinition: from C18 (namespace `DPLattice`) `DPLattice`, `IsDP`, `H`, `Hom`,
`InWt`, `one`, `delta`, `nabla` (with `deltaF`, `deltaE`, `nablaF`, `nablaE`, `weylWt` inside),
`T5_delta_zero`; from C19 (namespace `WeylFilt`) `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`;
from C20 (namespace `Doubling`) `RecData`, `isDP_of_rec`, `homOfOne`, `comm_of_rec` (inside
`homOfOne`), `factorial_smul_of_rec`, `dp_rec_F`, `dp_rec_E`, `dp_lie`, `Ed_FE`, `hom_aeval`,
`hom_inWt`, `Hop_of_inWt`, `eq_on_inWt`, `Iso`, `Iso.ofInverse`, `Iso.ofDataEquiv`, `Iso.symm`,
`Iso.trans`, and the basis vectors `eD`, `eN` of `Δ`, `∇` with their single-operator formulas.

## Encodings

* **Setting**: `p : ℕ` with `[Fact p.Prime]`, ring `ℤ_[p]`. The hypothesis `p ≠ 2` of the file is
  never needed: all results hold for every prime `p` (more general).
* **`q(c, r)`** (`Basic.lean`): `qc p c r : ℤ_[p]`, defined as `p^{c+v_p(c!)−v_p(r!)} · c!' · (r!')⁻¹`
  (`n! = p^{v_p(n!)} n!'`); (A0) is `A0` (norm bound, image `p^c c!/r!` in `ℚ_[p]`, and
  `r! · q(c, r) = p^c · c!`), for `r / p ≤ c`.
* **Slots**: `bv p k n = b_k n` (slot `k : ℕ`, zero if `k ≥ p`), `sl p j` the slot `j`.
* **`Φ_p(N)`** (`Twist.lean`, `PartAB.lean`): basis `Fin p × N.ι`, weights
  `twWt p N (j, i) = p w_i + p − 1 − 2j`, `F^{(r)} = twFd p N r`, `E^{(r)} = twEd p N r` (the closed
  formulas `twFdL`, `twEdL` on basis vectors, extended linearly; restated as `twFd_single`,
  `twEd_single`). `S(j, r) = Sset p j r` (with `j − k + ap < r` written `j + pa < r + k`),
  `P_{j,r} = PP p N w_i (Sset p j r)`, the product of the polynomials `pFactor p w (a, k)` evaluated
  at `X = F ∘ E`. The DP-lattice is `twist p N`.
* **Weight vectors**: "`n` of weight `w`" is C18's `InWt N.wt w n`.
* **`Φ_p` on morphisms** (`Functor.lean`): `twistLin p f = 1 ⊗ f`, `twistHom p f = Φ_p(f)`.
* **Part D** (`PartD*.lean`): `λ = lam p μ = pμ + p − 1`; `x_R = xD p μ R` (in `Φ_p(Δ(μ))`),
  `xN p μ R` (in `Φ_p(∇(μ))`), `= b_{R mod p} e_{R/p}`; `c_R = cD p R`, `c_R^{-1} = cDinv p R`,
  `d_R = dN p μ R`, `d_R^{-1} = dNinv p μ R`; `δ = deltaMap p μ` (inverse `deltaInv p μ`),
  `ν = nablaMap p μ` (inverse `nablaInv p μ`). Divisions `c_R/(R+1)`, `d_R/(λ−R)` are stated
  multiplicatively together with the unit property of the divisor.

## Main results

* (A0) `A0` (with `qc_spec`, `qc_coe`).
* (A1) `A1`, `twist`, `twist_data`; (A2) `A2`, `twistHom`; (A3) `A3`.
* (B1) `B1`; (B2) `B2`; (B3) `B3`; closed formulas on basis vectors `twFd_single`, `twEd_single`.
* (D1) `D1`, `D1_iso`; (D2) `D2`, `D2_iso`; (D3) `D3`, `D3'`.
-/
