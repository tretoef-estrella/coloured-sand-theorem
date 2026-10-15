module

public import RequestProject.OddWindows.Basic
public import RequestProject.OddWindows.Chain
public import RequestProject.OddWindows.Steps
public import RequestProject.OddWindows.General
public import RequestProject.OddWindows.Rescaling
public import RequestProject.OddWindows.Lambda

/-!
# `CSI12_the_odd_windows.md` — the odd windows theorem (Theorem 4.1 of «the odd dance»)

Namespace `ColouredSand.OddTwist`.  Reuses, unchanged, CSI10 (`SData`, `stepD`, `iterD`,
`digitL`, `kTop`, `Iset`, `Qdata`, `slots`, `Mp`), CSI7 (`QT`), CSI8 (`prodQ`, `QA`, `QC`, `KS`,
`blockS`, `QS`), CSI9 (`Q0`), CSI11 (`starPow`, `Iod`, `aP`, `dsL`, `Q1_support`, `Iod_lambda`) and
C10 (`Deficit.starMul`).

Files:
* `Basic.lean` — *Setting*: `oW` (`o_D`), `piW` (`π_0`), `bW` (`b_h`), `xMul` (`x_h · f`),
  **Part C** `cW` (`c^{(h)}`), the slot labels `slotLab` (with `slotLab_succ_zero`,
  `slotLab_succ_pos`) and `LabP` (bijection onto subsets).  The docstring explains all encodings.
* `Chain.lean` — the chain argument: window form `WinF`, `WinF_mul`, `WinF_prodList`.
* `Steps.lean` — the moves: `base_win`, `twist_step`, `split_step`, `split_lab`.
* `General.lean` — abstract digits: `labels_gen`, `win_iter`, **(W1)** `W1_gen`,
  **(W2)** `W2_gen` (any level, any number `s ≥ 1` of factors), `cW_supp`.
* `Rescaling.lean` — **(C1)** `C1_rescaling` (CSI11's digit lists).
* `Lambda.lean` — CSI10's data: `labL`, `slots_as_subsets`, **(W1)** `W1_windows`,
  **(W2)** `W2_Mp`, **(C1)** `C1_lambda`.

Hypotheses: `p` prime for the `ℤ_[p]` statements (`p ≥ 2` in the abstract ones), `e ≥ 1`,
`h ≤ k`.  Oddness of `p` is never used.
-/
