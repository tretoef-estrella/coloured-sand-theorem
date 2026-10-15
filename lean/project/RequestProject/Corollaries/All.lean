module

public import RequestProject.Corollaries.Valuation
public import RequestProject.Corollaries.JordanType
public import RequestProject.Corollaries.CorollarySix
public import RequestProject.Corollaries.Checks

/-!
# `CS6_corollaries_1_and_6.md`: Corollary 1 and Corollary 6

Namespace `ColouredSand.Corollaries`.  Reuses `RequestProject/Strings` (`B_m`, `H`, `U`,
`opM = q(c+H)+U`), `RequestProject/Splitting` (Theorem A, `X_q(m,c) = Xq q m c`, (A4)),
`RequestProject/TheoremB` (`coker L`, `sandpile`, (B1), `torsion_tensor_equiv_syl`) and
`RequestProject/NumberOfFactors` (`tensorXqEquiv`, `tensorPrimaryEquiv`).

* **(Q1)** `corollary1_piece`, `corollary1_piece_pow` (`Valuation.lean`).
* **(Q2)** `corollary1_whole` (`Valuation.lean`).
* **(Q3)** `U_cube_zmod_three`, `rank_U_zmod_three`, `jordanABC_closed`, `fCoker_formula`,
  collected in `jordan_type_U_zmod_three` (`JordanType.lean`).
* **(Q4)** `corollary6` and `corollary6_q_three` (`CorollarySix.lean`), proved without Wilson's
  diagonal form and without `theorem_D`.
* **(Q5)** `fCoker_values`, `corN_values`, `cycFactors3_values` (`Checks.lean`).
-/
