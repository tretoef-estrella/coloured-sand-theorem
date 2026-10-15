module

public import Mathlib

/-!
# Sums over the last `r` positions (Parts C and D of `C2_smith_bounds.md`)

## Encoding

* As in `RequestProject/AntitonicFit/`, a sequence of length `N` (positions `0, …, N − 1`) is a
  function `ℕ → α`; only the values at positions `< N` matter.
* `tailSum N r f = Σ_{j=N−r}^{N−1} f j`, as the sum of `f` over `Finset.Ico (N - r) N`, is the
  sum of the last `r` entries (for `0 ≤ r ≤ N`).  With `f = x` it is `U(r)` and with
  `f = ŷ` it is `Y(r)` of Parts C and D.
* A sequence `f` is non-increasing on the positions if `f (j + 1) ≤ f j` whenever `j + 1 < N`
  (`NonIncrOn N f`).
-/

@[expose] public section

namespace SmithBounds

open Finset

/-- *Parts C and D* of `C2_smith_bounds.md`: the sum `Σ_{j=N−r}^{N−1} f j` of the last `r`
entries of a sequence `f` of length `N` (this is `U(r)` for `f = x` and `Y(r)` for `f = ŷ`). -/
def tailSum {α : Type*} [AddCommMonoid α] (N r : ℕ) (f : ℕ → α) : α :=
  ∑ j ∈ Ico (N - r) N, f j

/-- *Part D* ((U1), Lemma D0) of `C2_smith_bounds.md`: `f` is non-increasing on the positions
`0, …, N − 1`, i.e. `f (j + 1) ≤ f j` for `j + 1 < N`. -/
def NonIncrOn {α : Type*} [Preorder α] (N : ℕ) (f : ℕ → α) : Prop :=
  ∀ j, j + 1 < N → f (j + 1) ≤ f j

theorem NonIncrOn.anti {α : Type*} [Preorder α] {N : ℕ} {f : ℕ → α} (h : NonIncrOn N f)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : f j ≤ f i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (h k hj).trans (ih (by omega))

theorem NonIncrOn.mono {α : Type*} [Preorder α] {N M : ℕ} {f : ℕ → α} (h : NonIncrOn N f)
    (hM : M ≤ N) : NonIncrOn M f := fun j hj => h j (by omega)

theorem tailSum_zero {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) : tailSum N 0 f = 0 := by
  simp [tailSum]

/-- One more entry from the end: `Y(r+1) = Y(r) + ŷ_{N−1−r}`. (Auxiliary for Parts C and D of
`C2_smith_bounds.md`.) -/
theorem tailSum_succ {α : Type*} [AddCommMonoid α] {N r : ℕ} (hr : r + 1 ≤ N) (f : ℕ → α) :
    tailSum N (r + 1) f = tailSum N r f + f (N - 1 - r) := by
  unfold tailSum
  rw [show N - r = (N - (r + 1)) + 1 by omega,
    sum_eq_sum_Ico_succ_bot (by omega : N - (r + 1) < N), add_comm,
    show N - (r + 1) = N - 1 - r by omega]

end SmithBounds
