module

public import RequestProject.Rulers.Basic
public import RequestProject.Rulers.Family
public import RequestProject.Rulers.Bits
public import RequestProject.Rulers.CostForm
public import RequestProject.Rulers.Clocks

/-!
# Rulers, gold and clocks (`C3_rulers_gold_clocks.md`)

Index of the formalization (namespace `Rulers`):

* `Basic.lean` — *Setting*: `s2` (`s_2`, via `Nat.digits`), `v2` (`v_2`, via
  `padicValNat 2`), `kappa` (`κ`), `phi` (`φ`), `oE` (`o_E`); the **Legendre sums**
  (`legendre_sum_shift`, `legendre_sum`).
* `Family.lean` — *A family*: `minOr` (with `min ∅ := k`), `next`, `h`, `t1`, `hSum` (`h(E)`),
  `G`, `lam` (`λ`), the deficit `delta` (`δ`, with `δ(∅) = 0`), the gold `gamma` (`γ`, with
  `γ(∅) = 0`), the rulers `ruler` (`R_μ`) and `rulerSharp` (`R^♯`), `xi` (`ξ_D`), the raw clock
  `clock` (`u_i(D)`), `xD` (`x_D`) and `xSharp` (`x^♯_D`); **Lemma 5.0** (`lemma_5_0_xi`,
  `lemma_5_0_sdiff`) and **Lemma 5.1** (`lemma_5_1_a`, `lemma_5_1_b`).
* `Bits.lean` — auxiliary digit counts (`s2_K_sub_one_add`, `kappa_K_sub_one`, `s2_core`).
* `CostForm.lean` — **Proposition 5.2** (`proposition_5_2`) and **Proposition 5.4 (a), (b)**
  (`proposition_5_4_a`, `proposition_5_4_b`).
* `Clocks.lean` — **Proposition 5.3** (`proposition_5_3`) and **Proposition 5.4 (c)**
  (`proposition_5_4_c`).
-/
