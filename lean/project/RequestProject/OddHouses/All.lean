module

public import RequestProject.OddHouses.Basic
public import RequestProject.OddHouses.LemmaA
public import RequestProject.OddHouses.Windows
public import RequestProject.OddHouses.TopDigit

/-!
# `CSI15_houses_at_p.md` — houses at a prime `p`: the four window types, Lemmas 7.5_p, 7.6_p, 7.7_p

Namespace `ColouredSand.OddTwist`.  Encodings: see `RequestProject/OddHouses/Basic.lean`.

* *Setting*: `digP`, `rP` (`rP_spec`), `RHP` (`RHP_eq_rulerP`), `JHP`, `xHP`, `cHatHP`, `cinP`,
  `carP`; Part B data `thetaP`, `kapP`, `satP`, `WinTypeP`, `typP`, `tauP`, `firesP`; Part C `d1P`.
* **Part A (Lemma 7.5_p)**: `houseP_A0_antisymm`, `houseP_A0_upset`, `houseP_A1`
  (and `houseP_A1_rulerP`), `houseP_A2_residue`, `houseP_A2_at_most_one`
  (remarks: `houseP_A2_two`, `houseP_A2_both_zero`), `houseP_A3_cost`, `houseP_A3_clock`.
* **Part B (Lemma 7.6_p)**: `houseP_B1`, `houseP_B2`, `houseP_B2_fires_iff`, `houseP_B3`,
  `houseP_B4`, `houseP_B5`, `houseP_B6`.
* **Part C (Lemma 7.7_p)**: `houseP_C1`, `houseP_C2`, `houseP_C3`, `houseP_C4`,
  `houseP_C5_not_mem`, `houseP_C5_mem`, `houseP_C6`, `houseP_C7`.
-/
