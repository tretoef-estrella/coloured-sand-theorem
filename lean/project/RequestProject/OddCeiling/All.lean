module

public import RequestProject.OddCeiling.Order
public import RequestProject.OddCeiling.NaturalMinor
public import RequestProject.OddCeiling.PDivisors
public import RequestProject.OddCeiling.Smith
public import RequestProject.OddCeiling.Assembly

/-!
# `CSI14_the_ceiling_at_p.md`: the ceiling at a prime p (namespace `ColouredSand.OddTwist`)

Index of the formalized statements (each docstring names its part of the file and explains its
encoding):

* **Part A** (`Order.lean`): `oP` (= CSI12's `oW`, `oP_eq_oW`); (A1) `A1_same_order`;
  (A2) `A2_rank`, `A2_Lr`, `A2_Fr` (with `rankP`, `LrP`, `FrP`) and `theorem_O_P` (Theorem O
  in the base-`p` order); (A3) `A3_complement`.
* **Part B** (`NaturalMinor.lean`): `cHatP`, `xP`, `UP`; (B1) `B1_cost`.
* **Part C** (`NaturalMinor.lean`): (C1) `C1_natural_minor`.
* **Part D** (`PDivisors.lean`): `minorValsP`, `ddP`; (D0) `D0_two` (and `D0_minorVals`);
  (D1) `D1_invariance`; (D2) `D2_diagonal`; (D3) `D3_sum`, `D3_increment`, `D3_convex`.
* **Part Q** (`Smith.lean`): (Q1) `Q1_smith`; (Q2) `Q2_smith`.
* **Part T** (`Assembly.lean`): (T1) `T1_assembly` (and `T1_assembly_of_smith`, for a given
  Smith form).

The short names `A1`, `D1`, `Q1`, … are not used because names such as
`ColouredSand.OddTwist.D1` already exist in this namespace (CSI11).

Reused, not redefined: `Rulers.oE`, `Rulers.gamma` (C3); `GoldenMatching.rank`, `Lr`, `Fr`,
`IsGoldenArrow`, `theorem_B`, `lemma_C1_bijOn` (C4); `Divisors.minor`, `Divisors.minorVals`,
`Divisors.dd`, `Divisors.cauchy_binet` (through `Divisors.minor_mul`),
`Divisors.theorem_B_without_M` (C5); `SmithBounds.corollary_B'` (C2); `AntitonicFit.ifit` (C1);
the block-matrix helpers of `DanceSmith` (C15); `oW` (CSI12).
-/
