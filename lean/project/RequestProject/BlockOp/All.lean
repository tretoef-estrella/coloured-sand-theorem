module

public import RequestProject.BlockOp.Operator
public import RequestProject.BlockOp.Matrices
public import RequestProject.BlockOp.Groups

/-!
# `CSG6_operator_on_the_blocks.md` — the operator `q(c+H)+U` on `B_m ⊗ ℤ_p`, block by block
# (namespace `ColouredSand.BlockOp`)

The odd-`p` analogue of `RequestProject/ThmH/TheoremH.lean` (`T1equiv`, `opT_eq_sigL`).

Reused, not redefined: `ColouredSand.Strings.B`, `H`, `U`, `opM`; `ColouredSand.ThmH.Psi`,
`ThmH.D2` (the dictionary `B_m(A) = V^{⊗m}`); `Filt.tpow`, `Step36.dsumList`, `Doubling.Iso`,
`DPLattice.H`, `DPLattice.delta`; `Families.dsumMap_exists`, `Families.isoEquiv`;
`cokerEquivOfConj`, `range_pi_comp_proj`, `Submodule.quotientPi`; `TiltP.Ttilt`,
`Ttilt_of_simple`, `Ttilt_of_not_simple`, `IsSimpleWt`, `rT`, `aT`, `T3`, `Tglue`, `Tglue_wt_inl`,
`Tglue_wt_inr`, `T1_Fd`, `GlueHyp`; `Glue.glueBasis`, `xzero`, `Oop`, `Hop_ell`, `Hop_stilde`,
`Orestr`, `G5b_matrix`; `Blocks.Mblk`, `Mch`, `Nt`, `lam`, `mu`, `chA`, `blkX`, `blkY`, `E12`,
`E22`, `B1`, `B2`, `S1`, `S2`; `TiltDec.LP`, `M3`, `D2`.

## Encodings

* `ℤ_[p]` is Mathlib's `PadicInt p` (`[Fact p.Prime]`), `hp2 : p ≠ 2`.
* `half p = Ring.inverse 2`; `opT p M m q c = F^{(1)} + q • (c • id + half p • (m • id − H))`.
* `coker f = N ⧸ LinearMap.range f`; `cokT p M m q c` is the cokernel of `opT p M m q c`.
* The summands of `V^{⊗m}` are indexed by `j : Fin (LP p m).length`, `λ_j = (LP p m).get j`.
* Matrices act by `Matrix.mulVecLin` (column `y` = image of the basis vector `y`).

## Contents

* `Operator.lean`, Part K: **(K0)** `half`, `two_mul_half`; **(K1)** `opT`; **(K2)** `K2`;
  **(K3)** `K3a`, `K3b` (with `dsumTheta`); **(K4)** `K4equiv` (the `def`) and `K4`.
* `Matrices.lean`, Part E: **(E1)** `E1` (and the remark `E1_false_at_two`: with this `opT`,
  (E1) fails at `p = 2`, so Part E assumes `p ≠ 2`); **(E2)** `E2`; **(E3)** `E3a`, `E3b`
  (with the explicit equivalences `E3a_equiv`, `E3b_equiv` at `m = λ + 2k`).
* `Groups.lean`, Part G: **(G1)** `G1a`, `G1b`, `G1c`; **(G2)** `G2`.
-/
