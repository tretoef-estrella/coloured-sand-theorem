module

public import RequestProject.Exponent.Inverse
public import RequestProject.Exponent.Criterion
public import RequestProject.Exponent.Carries
public import RequestProject.Exponent.Pieces
public import RequestProject.Exponent.TheoremC
public import RequestProject.Exponent.Checks

/-!
# Theorem C: the exponent of `Syl_p K(H(d,q))` — index

Formalization of `CS4_theorem_C_exponent.md`, namespace `ColouredSand.Exponent`, reusing
`RequestProject/Strings/` (CS1: `B_m`, `H`, `U`, `opM`), `RequestProject/Splitting/`
(CS2: Theorem A) and `RequestProject/TheoremB/` (CS3: `sandpile`, (B1)):

* (C1) Lemma 4: `RequestProject/Exponent/Inverse.lean` (`lemma4`; general field version
  `inverse_formula`; the column computation `opM_invVec`).
* (C2) The exponent criterion: `RequestProject/Exponent/Criterion.lean` (`exponent_criterion`
  for a discrete valuation ring; `exponent_criterion_padic` for `ℤ_[p]` with `AddMonoid.exponent`
  and valuations; `kills_coker_iff_integral` for any domain).
* (C3) Lemma 5: `RequestProject/Exponent/Carries.lean` (`lemma5`, `lemma5_zero`,
  `vp_add_vp_choose_le_log`).
* (C4) Theorem C: `RequestProject/Exponent/TheoremC.lean` (`theorem_C`, `expE`), using
  `RequestProject/Exponent/Pieces.lean` (`piece_kills_iff`, `piece_zero_kills_torsion`).
* (C5) Checks: `RequestProject/Exponent/Checks.lean` (`expE_three_three_ten`,
  `check_attained_nine`, `check_not_attained_ten`, `exponent_three_three_ten`, `expE_of_lt`,
  `exponent_of_lt`).
-/
