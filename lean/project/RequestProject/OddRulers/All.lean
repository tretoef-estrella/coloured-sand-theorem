module

public import RequestProject.OddRulers.Digits
public import RequestProject.OddRulers.Carries
public import RequestProject.OddRulers.CostForm
public import RequestProject.OddRulers.Valuations

/-!
# `CSI13_the_odd_cost_form.md` — rulers with base-`p` carries and the odd cost form
(Proposition 4.3 of «the odd dance»)

Namespace `ColouredSand.OddTwist`.  Reuses, unchanged, C3 (`Rulers.minOr`, `Rulers.h`,
`Rulers.delta`, `Rulers.gamma` — the gold —, `Rulers.G`, `Rulers.lemma_5_1_a`), CSI10 (`digitL`,
`kTop`, `Iset`, `slots`, `Mp`), CSI11 (`starPow`, `aP`, `dsL`, `D1_lambda`) and CSI12 (`oW`,
`piW`, `bW`, `cW`, `labL`, `slots_as_subsets`, `W2_Mp`, `C1_lambda`, `starPow_scale`,
`cast_starPow_int`).

Files:
* `Digits.lean` — *Setting*: `sP` (`s_p`), `kappaP` (`κ_p`, with Kummer
  `kappaP_eq_padicValNat_choose`); **(L1)** `L1_legendre`, `L1_sum`, `L1_sum_neg`; **(L2)** `L2`.
* `Carries.lean` — **(L3)** `L3_sP_K`, `L3_kappa` (and `kappaP_K_sub_one` with `min ∅ := k`);
  **(L4)** `L4`.
* `CostForm.lean` — the rulers `rulerP` (`R_μ`), `rulerSharpP` (`R^♯`); **(P1)** `P1`
  (`i ≥ 1`) and `P1_zero` (`i = 0`, `a ≠ ∅`).
* `Valuations.lean` — **(P2)** `P2_support` (`Mp_{ab} = 0` unless `b ⊆ a`), `P2_pos` (`i ≥ 1`),
  `P2_zero_row` and `P2_zero` (`i = 0`).

Hypotheses: Part L and (P1) hold for every prime `p` (oddness is not used) and for any set
`I ⊆ [0, k)` whose digits are in `[1, p − 1]`, and (P1) holds for every `e`; (P2) assumes, as the
file, `p` an odd prime (needed by CSI11's deficit law) and `e ≥ 1` (needed by CSI12's (W2)).
-/
