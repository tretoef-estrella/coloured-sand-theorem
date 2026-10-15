module

public import RequestProject.DanceSmith.Basic
public import RequestProject.DanceSmith.SmithForm
public import RequestProject.DanceSmith.Bounds
public import RequestProject.DanceSmith.Golden
public import RequestProject.DanceSmith.Positive
public import RequestProject.DanceSmith.Zero

/-!
# `C15_smith_form_of_the_dance_matrix.md`: the Smith form of the dance matrix (Theorem 7.10)

Index of the formalization (namespace `DanceSmith`).

## Encodings

* `ds : List Bool` with `k = ds.length`, `I = Windows.Ids ds`, `m = Dance.mCount ds` (`= #I`,
  `Windows.card_Ids`), `N = 2 ^ Dance.mCount ds`, `K = 2 ^ ds.length`; `α i : ℕ`, with `α` cast to
  `ℤ` where the reused definitions need an integer.
* `M = Windows.finalMatrix ℤ ds α i : Matrix (Fin N) (Fin N) ℤ` (C14).
* `bitRev m p` is the bit reversal of `p` on `m` bits; `sl ds : Fin N → Fin N` is `p ↦ bitRev m p`
  and `slPerm ds` the same map as a permutation; `Mo ds α i = M.submatrix (sl ds) (sl ds)`, i.e.
  `Mo p q = M (sl p) (sl q)`.
* The dancers in o-order are `TheoremF.dancer I p` (C7), read at `p : Fin N` through `p.val`.
* Clocks for `i ≥ 1`: `xClk ds α i j = GoldenMatching.xVal k I α (i − 1) (TheoremF.dancer I j)`,
  `yHat ds α i = AntitonicFit.ifit N (xClk ds α i)` (`ŷ`),
  `Cst ds α i = α K + Rulers.kappa (i − 1) K` (`C`).
* For `i = 0`: `yHatS ds α = CellFloor.yhatSharp I k (K − 1) α` (`ŷ^♯`).
* Divisors and minors: `Divisors.dd`, `Divisors.minor` (C5); "`det P` odd" is `Odd P.det`.
* Smith forms: `P * A * Q = Matrix.diagonal D` with `D j = u j * 2 ^ e j` (and `0` beyond `ρ`);
  exponents that the file writes as integers known to be natural are natural numbers `E j` with the
  equation `(E j : ℤ) = …`.
* Sums `Σ_{j ∈ [a, b)}` are sums over `Finset.Ico a b`; `Σ_{j<r} e j` is a sum over
  `Finset.range r`; "non-increasing on `[0, L)`" is `∀ j, j + 1 < L → f (j + 1) ≤ f j`.

## Where each statement is

* **Part P** (`Basic.lean`): (P1) `P1`; (P2) `P2_general` (any `n`, any permutation) and `P2`
  (for `Mo`).
* **Part Q** (`SmithForm.lean`): (Q1) `Q1`; (Q2) `Q2` (and `Q2_nonempty`).  (Q1) is proved by
  elimination with a pivot of least 2-valuation; Mathlib's Smith normal form is not used.
* **Part S** (`Positive.lean`): (S1) `S1`; (S2) `S2`; (S3) `S3`.
* **Part Z** (`Zero.lean`): (Z1) `Z1`; (Z2) `Z2`; (Z3) `Z3`.
* The common skeleton (floor via `SmithBounds.lemma_A1`, conclusion via (Q1), (Q2) and
  `Divisors.theorem_B_without_M`) is in `Bounds.lean`; the ceiling via
  `GoldenMatching.corollary_D` is in `Golden.lean`.

## Hypotheses

* `1 ≤ k` is used through `Windows.theorem_D_iii` (S1–S3, Z2, Z3); (Z1) does not need it.
* `1 ≤ α` is used by `Windows.theorem_D_ii`/`theorem_D_iii` and by the CellFloor results.
* `1 ≤ i` (Part S) and `I ≠ ∅` (Z2, Z3) are used.
* In the floor for `i = 0` we use `CellFloor.theorem_B_floor` for the house `H^♯ = (I, k, K − 1, α)`
  with zero penalties (its tail sums equal those of `ŷ^♯` by `CellFloor.lemma_7_9_I3`), which also
  covers the minors through the zero row of `∅` and the column of `I`; `CellFloor.theorem_C_floor`
  is not needed.  For the ceiling at `i = 0`, `GoldenMatching.corollary_D` is applied with
  `μ = K − 1` to `Mo` with its columns `D ≠ ∅` multiplied by `2` and its row `∅` replaced by
  `(2^{αK}, 0, …, 0)`, which does not change the rows `[N − r, N)`, `r ≤ N − 1`.
-/
