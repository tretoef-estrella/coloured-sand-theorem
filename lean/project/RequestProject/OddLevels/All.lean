module

public import RequestProject.OddLevels.Basic
public import RequestProject.OddLevels.LastLevel
public import RequestProject.OddLevels.Floors
public import RequestProject.OddLevels.Graded

/-!
# `CSI9_last_level_and_floors.md` — the last level (Proposition 2.3) and the floors of `danceL`

Namespace `ColouredSand.OddTwist`. Files:

* `Basic.lean` — encodings (`dsE`, `opDS`, `famF`, `sysUnitE`, `Dop`, `Q0`) and the general form
  of (G3), `Gp_Q0_eq`.
* `LastLevel.lean` — **Part L**: `L1` (for `ℤ_[p]`, `p` prime, `1 ≤ d ≤ p − 1`) and the more general
  `L1_general` (any commutative ring in which `1, …, d − 1` are units).
* `Floors.lean` — **Part G (G1)**: `flL`, `wt_danceL`, `G1_parity`, `G1_nonneg`, `G1_Fd`,
  `G1_Fd_floor`, `G1_delta`, `G1_twist`, `G1_psi`.
* `Graded.lean` — **Part G (G2)**: `G2_twist`, `G2_psi` (from the lattice-level statements
  `opDS_twist`, `opDS_psi`), and **(G3)**: `G3_operator`.

## Main results (exact Lean names, namespace `ColouredSand.OddTwist`)

* (L1) `L1`, `L1_general`.
* (G1) `flL`, `wt_danceL`, `G1_parity`, `G1_nonneg`, `G1_Fd`, `G1_Fd_floor`, `G1_delta`,
  `G1_twist`, `G1_psi`.
* (G2) `G2_twist`, `G2_psi`; for an arbitrary lattice `N`: `opDS_twist`, `opDS_psi`.
* (G3) `G3_operator`; general form `Gp_Q0_eq`.
-/
