module

public import RequestProject.OddTheoremI.Basic
public import RequestProject.OddTheoremI.Reindex
public import RequestProject.OddTheoremI.Digits
public import RequestProject.OddTheoremI.TheoremD
public import RequestProject.OddTheoremI.TheoremI

/-!
# `CSI10_theorem_Dp_and_theorem_I.md` — Theorem D_p and Theorem I (every odd prime)

Namespace `ColouredSand.OddTwist`. Reuses, without modification, CSI6 (`danceL`, `card_danceL_digits`),
CSI7 (`Gp`, `QT`, `NT`, `flT`, `FT`, `corollary_Ap2`), CSI8 (`QS`, `prodQ`, `NS`, `flS`, `FS`,
`corollary_M2`), CSI9 (`famF`, `opDS`, `dsE`, `sysUnitE`, `Dop`, `Q0`, `flL`, `idxDelta`, `eTw`,
`ePsi`, `G1_delta`, `G2_twist`, `G2_psi`, `G3_operator`, `L1`) and C11 (`Payment.Sys`,
`Payment.quotProdEquiv`).

Files:
* `Basic.lean` — Setting and **Part M**: the digits (`digitL`, `kTop`, `Iset`), slot types with
  data (`SData`, `stepD`, `iterD`), the halved data `Qdata`, the matrix `Mp` on `slots`,
  `card_slots` (`|slots| = 2^{|I|}`) and **(M1)** `M1`.
* `Reindex.lean` — reindexing a system along an equivalence of index types (`sysRe`,
  `sysRe_comp_Gp`) and the counting of the torsion factors.
* `Digits.lean` — the digits of `λ + 1` along the recursion of `danceL`.
* `TheoremD.lean` — **Part D**: `Yp`, `sigmaOp`, `Zq`; the general form `theorem_D_gen` (any
  starting slot type and data, any starting scalar `p^h`); **(D1)** `theorem_Dp`.
* `TheoremI.lean` — **Part I**: `Sp`, `Cmod`; **(I1)** `I1`, **(I2)** `I2`, **(I3)**
  `I3_generators` and `I3_quot`; the invariant form `theorem_I_invariant`; the assembly
  `theorem_I`.

(I4) (`p = 2` from the cube's Theorem D) is not formalized: the cube's Theorem D
(`Windows.theorem_D`) is stated for the cube's own lattices `SysT ℤ ds` and operator
`Windows.sigma` over `ℤ`, not for `danceL 2 λ` over `ℤ_[2]`, so it does not connect directly.

## Main results (exact Lean names, namespace `ColouredSand.OddTwist`)

* (M1) `M1`; `card_slots`.
* (D1) `theorem_Dp`; general form `theorem_D_gen`.
* (I1) `I1`; (I2) `I2`; (I3) `I3_generators`, `I3_quot`; invariant form `theorem_I_invariant`;
  Theorem I assembled: `theorem_I`.
-/
