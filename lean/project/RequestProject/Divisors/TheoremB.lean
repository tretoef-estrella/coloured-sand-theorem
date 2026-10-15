module

public import RequestProject.SmithBounds.Convexity

/-!
# Part B of `C5_divisors_theorem_65.md`: Theorem B (Theorem 6.5, abstract form) and Corollary B′

## Encoding

* As in pieces C1 and C2, the integer sequence `x_0, …, x_{N−1}` is `x : ℕ → ℤ` (only positions
  `< N` matter) and `ŷ = ifit(x)` is `AntitonicFit.ifit N x` (piece C1).
* `U(r) = Σ_{j=N−r}^{N−1} x_j` and `Y(r) = Σ_{j=N−r}^{N−1} ŷ_j` are written as sums over
  `Finset.Ico (N - r) N`, exactly as in piece C2 (they are definitionally `SmithBounds.U N x r`
  and `SmithBounds.Y N x r`).
* The exponents `e_0 ≤ ⋯ ≤ e_{N−1}` are `e : ℕ → ℤ` with `e i ≤ e j` whenever `i ≤ j < N`
  (only the values at positions `< N` matter).
* **`d̂`.** `dHat C e r = (e_0 + ⋯ + e_{r−1}) − r·C`, where `e_0 + ⋯ + e_{r−1}` is
  `∑ i ∈ Finset.range r, e i`; it is used for `0 ≤ r ≤ N`.
* (M) "`ŷ` is non-increasing on `{0, …, N − 1}`" is `∀ j, j + 1 < N → ŷ (j + 1) ≤ ŷ j`.
-/

@[expose] public section

namespace Divisors

open Finset AntitonicFit SmithBounds

/-- *Part B, Setting* of `C5_divisors_theorem_65.md`: the normalized divisors
`d̂(r) = (e_0 + ⋯ + e_{r−1}) − r·C`. -/
def dHat (C : ℤ) (e : ℕ → ℤ) (r : ℕ) : ℤ := (∑ i ∈ range r, e i) - r * C

theorem dHat_zero (C : ℤ) (e : ℕ → ℤ) : dHat C e 0 = 0 := by simp [dHat]

/-- The increments of `d̂` are `d̂(r+1) − d̂(r) = e_r − C`. (Proof of Theorem B of
`C5_divisors_theorem_65.md`.) -/
theorem dHat_succ (C : ℤ) (e : ℕ → ℤ) (r : ℕ) : dHat C e (r + 1) - dHat C e r = e r - C := by
  simp only [dHat, sum_range_succ]; push_cast; ring

/-- `d̂` is convex when `e` is non-decreasing. (Proof of Theorem B of
`C5_divisors_theorem_65.md`.) -/
theorem dHat_convex {N : ℕ} (C : ℤ) {e : ℕ → ℤ} (he : ∀ i j, i ≤ j → j < N → e i ≤ e j) :
    IsConvexOn N (dHat C e) := by
  intro r hr
  rw [dHat_succ, show r + 2 = (r + 1) + 1 by rfl, dHat_succ]
  linarith [he r (r + 1) (by omega) (by omega)]

/-- **Theorem B** (Theorem 6.5) of `C5_divisors_theorem_65.md`, **stated without hypothesis
(M)**, which is redundant: if
(F) `Y(r) ≤ d̂(r)` and (U) `d̂(r) ≤ U(r)` for every `0 ≤ r ≤ N`, then `d̂(r) = Y(r)` for every
`0 ≤ r ≤ N` and `e_i = C + ŷ_{N−1−i}` for every `0 ≤ i < N`. -/
theorem theorem_B_without_M (N : ℕ) (x : ℕ → ℤ) (C : ℤ) (e : ℕ → ℤ)
    (he : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, ifit N x j ≤ dHat C e r)
    (hU : ∀ r ≤ N, dHat C e r ≤ ∑ j ∈ Ico (N - r) N, x j) :
    (∀ r ≤ N, dHat C e r = ∑ j ∈ Ico (N - r) N, ifit N x j) ∧
      ∀ i < N, e i = C + ifit N x (N - 1 - i) := by
  have hle := lemma_6_4 (x := x) (dHat C e) (dHat_convex C he) (dHat_zero C e) hU
  have heq : ∀ r ≤ N, dHat C e r = ∑ j ∈ Ico (N - r) N, ifit N x j :=
    fun r hr => le_antisymm (hle r hr) (hF r hr)
  refine ⟨heq, fun i hi => ?_⟩
  have h1 := dHat_succ C e i
  rw [heq (i + 1) hi, heq i hi.le] at h1
  have h2 := tailSum_succ (N := N) (r := i) hi (ifit N x)
  simp only [tailSum] at h2
  linarith

/-- **Theorem B** (Theorem 6.5, abstract form) of `C5_divisors_theorem_65.md`: suppose
(F) `Y(r) ≤ d̂(r)` for every `0 ≤ r ≤ N`, (U) `d̂(r) ≤ U(r)` for every `0 ≤ r ≤ N`, and
(M) `ŷ` is non-increasing on `{0, …, N − 1}`.  Then `d̂(r) = Y(r)` for every `0 ≤ r ≤ N`, and
`e_i = C + ŷ_{N−1−i}` for every `0 ≤ i < N`.

Hypothesis (M) is kept as in the file but is **unused** by the proof (see
`theorem_B_without_M`, and Corollary B′ `corollary_B'` which derives (M) from (F) and (U)). -/
theorem theorem_B (N : ℕ) (x : ℕ → ℤ) (C : ℤ) (e : ℕ → ℤ)
    (he : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, ifit N x j ≤ dHat C e r)
    (hU : ∀ r ≤ N, dHat C e r ≤ ∑ j ∈ Ico (N - r) N, x j)
    (_hM : ∀ j, j + 1 < N → ifit N x (j + 1) ≤ ifit N x j) :
    (∀ r ≤ N, dHat C e r = ∑ j ∈ Ico (N - r) N, ifit N x j) ∧
      ∀ i < N, e i = C + ifit N x (N - 1 - i) :=
  theorem_B_without_M N x C e he hF hU

/-- **Corollary B′** of `C5_divisors_theorem_65.md`: under (F) and (U) alone (and `e`
non-decreasing), `ŷ = ifit(x)` is non-increasing on `{0, …, N − 1}`. -/
theorem corollary_B' (N : ℕ) (x : ℕ → ℤ) (C : ℤ) (e : ℕ → ℤ)
    (he : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, ifit N x j ≤ dHat C e r)
    (hU : ∀ r ≤ N, dHat C e r ≤ ∑ j ∈ Ico (N - r) N, x j) :
    ∀ j, j + 1 < N → ifit N x (j + 1) ≤ ifit N x j := by
  intro j hj
  obtain ⟨-, h⟩ := theorem_B_without_M N x C e he hF hU
  have h1 := h (N - 2 - j) (by omega)
  have h2 := h (N - 1 - j) (by omega)
  rw [show N - 1 - (N - 2 - j) = j + 1 by omega] at h1
  rw [show N - 1 - (N - 1 - j) = j by omega] at h2
  linarith [he (N - 2 - j) (N - 1 - j) (by omega) (by omega)]

end Divisors
