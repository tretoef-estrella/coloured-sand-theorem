module

public import RequestProject.OddSmith.Basic
public import RequestProject.OddSmith.Bounds
public import RequestProject.OddSmith.Coker
public import RequestProject.OddSmith.Positive
public import RequestProject.OddSmith.Zero
public import RequestProject.OddSmith.Closed

/-!
# `CSI18_theorem_4_4_smith_form_of_Mp.md`: Theorem 4.4 at an odd prime — the Smith form of `Mp` and
the closed form of `Y_p(λ, i, e)`

Index of the formalization (namespace `ColouredSand.OddTwist`, every new name prefixed `oddSmith`).

## Encodings

* `p` is a prime (`[Fact p.Prime]`), odd where needed (`hodd : Odd p`); `λ` is `l`; CSI10's
  `k = kTop p l`, `d_t = digitL p l t`, `I = Iset p l`; `N = 2 ^ #I`; `K = oddSmithK p l = d_k p^k`;
  `e, i : ℕ` with `e ≥ 1` (`he`), and `i ≥ 1` (`hi`) in Part S.
* Slots are listed in o-order: `oddSmithSlot p l i e : Fin N ≃ slots p l i e` sends the position `q`
  to the slot whose CSI12 label is `TheoremF.dancer I q`; `oddSmithMo = Mp` read in this order.
* Part Z0: `oddSmithMZ p l i e : Matrix (Fin N) (Fin N) ℤ` with `oddSmithMo = MZ.map Int.cast`.
* Part S: `oddSmithC = e K + κ_p(i − 1, K)`, clocks `oddSmithX` (`x`, CSI13's rulers),
  `oddSmithYhat = ifit N x` (`ŷ`).
* Part Z: `oddSmithXSharp` (`x^♯`, CSI13's `R^♯`), `oddSmithYhatSharp = ifit (N − 1) x^♯` (`ŷ^♯`);
  the position of `∅` is `oddSmithZeroPos`.
* Divisors are CSI14's `ddP`; Smith forms are `P * MZ * Q = diagonal …` with `¬ (p : ℤ) ∣ det P`,
  `¬ (p : ℤ) ∣ det Q`, units `u j` with `¬ (p : ℤ) ∣ u j`, and natural exponents `E j` given with
  their value in `ℤ`. Sums `Σ_{j ∈ [a, b)}` are over `Finset.Ico a b`.
* Part Y: CSI10's `Cmod`, `Zq`, `Yp`, `Sp`; products `Π_{j<N}` are `(j : Fin N) → …`.

## Where each statement is

* **Part Z0** (`Basic.lean`): `oddSmith_Mp_mem_bot` (every entry of `Mp` is an integer),
  `oddSmith_Z0`, `oddSmith_Z0_exists`, `oddSmith_Z0_unique`; permutations: `oddSmith_ddP_perm`.
* **Part S** (`Positive.lean`): (S1) `oddSmith_S1`; (S2) `oddSmith_S2`; (S3) `oddSmith_S3`.
* **Part Z** (`Zero.lean`): (Z1) `oddSmith_Z1`; (Z2) `oddSmith_Z2`; (Z3) `oddSmith_Z3`.
* **Part Y** (`Closed.lean`): (Y1) `oddSmith_Y1_pos`, `oddSmith_Y1_zero`, `oddSmith_Y1_zero_empty`;
  (Y2) `oddSmith_Y2_pos`, `oddSmith_Y2_zero`, `oddSmith_Y2_zero_empty`.
* Skeleton at `p` (`Bounds.lean`): `oddSmith_floor_minor`, `oddSmith_smith_of_bounds`,
  `oddSmith_ceiling`; cokernel algebra (`Coker.lean`, `Closed.lean`): `oddSmithDiagQuot`,
  `oddSmithUnitQuot`, `oddSmithReindexQuot`, `oddSmithSnocEquiv`, `oddSmith_coker_of_smith`.
-/
