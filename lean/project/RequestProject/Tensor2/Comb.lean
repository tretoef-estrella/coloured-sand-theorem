module

public import Mathlib

/-!
# `C23_the_tensor_product.md`: combinatorial identities for (P1)

Auxiliary identities used in the proof of (P1) (proof sketch, items "(P1), (P1)" and
"(P1), (K)"): Vandermonde's identity over `ℕ` (`Nat.add_choose_eq`) and over `ℤ`
(`Ring.add_choose_eq`, negative tops included), together with the reindexings of the sums.
-/

@[expose] public section

namespace Tensor2

open Finset

section P1comb

variable {X : Type*} [AddCommMonoid X]

/-- (P1), (P1) of the proof sketch (auxiliary): one row of the Vandermonde reindexing. -/
lemma vand_P1_inner (a b c : ℕ) (hc : c ≤ a) (T : ℕ → ℕ → X) :
    ∑ d ∈ range (b + 1), ((c + d).choose c * ((a - c) + (b - d)).choose (a - c)) •
        T (c + d) ((a - c) + (b - d)) =
      ∑ x ∈ range (a + b + 1), (x.choose c * (a + b - x).choose (a - c)) • T x (a + b - x) := by
  have hsub : Ico c (c + b + 1) ⊆ range (a + b + 1) := by
    intro x hx; simp at hx ⊢; omega
  rw [← sum_subset hsub, sum_Ico_eq_sum_range, show c + b + 1 - c = b + 1 by omega]
  · refine sum_congr rfl fun d hd => ?_
    simp at hd
    rw [show a + b - (c + d) = a - c + (b - d) by omega]
  · intro x hx hx'
    simp at hx hx'
    rcases Nat.lt_or_ge x c with h | h
    · simp [Nat.choose_eq_zero_of_lt h]
    · have h2 : a + b - x < a - c := by omega
      simp [Nat.choose_eq_zero_of_lt h2]

/-- (P1), (P1) of the proof sketch (auxiliary): the Vandermonde reindexing
`Σ_{c ≤ a} Σ_{d ≤ b} C(c+d, c) C(c'+d', c') T(c+d, c'+d') = C(a+b, a) Σ_{x+y=a+b} T(x, y)`
with `c' = a − c`, `d' = b − d`. -/
lemma vand_P1 (a b : ℕ) (T : ℕ → ℕ → X) :
    ∑ c ∈ range (a + 1), ∑ d ∈ range (b + 1),
      ((c + d).choose c * ((a - c) + (b - d)).choose (a - c)) • T (c + d) ((a - c) + (b - d)) =
      (a + b).choose a • ∑ x ∈ range (a + b + 1), T x (a + b - x) := by
  rw [sum_congr rfl fun c hc => vand_P1_inner a b c (by simp at hc; omega) T, sum_comm, smul_sum]
  refine sum_congr rfl fun x hx => ?_
  simp at hx
  rw [← sum_smul]
  congr 1
  have := Nat.add_choose_eq x (a + b - x) a
  rw [show x + (a + b - x) = a + b by omega, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => x.choose i * (a + b - x).choose j)] at this
  exact this.symm

end P1comb

section Kcomb

variable {X : Type*} [AddCommGroup X]

/-- (P1), (K) of the proof sketch (auxiliary): Vandermonde over `ℤ` on the right-hand side. -/
lemma vand_K_rhs (x y : ℤ) (r s : ℕ) (T : ℕ → ℕ → ℕ → ℕ → X) :
    ∑ m ∈ range (min r s + 1), Ring.choose (x + y + s - r) m •
      ∑ c' ∈ range (s - m + 1), ∑ a' ∈ range (r - m + 1), T a' c' (r - m - a') (s - m - c') =
    ∑ m ∈ range (min r s + 1), ∑ c' ∈ range (s - m + 1), ∑ a' ∈ range (r - m + 1),
      ∑ k ∈ range (m + 1), (Ring.choose (x + c' - a') k *
        Ring.choose (y + ((s - m - c' : ℕ) : ℤ) - ((r - m - a' : ℕ) : ℤ)) (m - k)) •
          T a' c' (r - m - a') (s - m - c') := by
  refine sum_congr rfl fun m hm => ?_
  rw [smul_sum]
  refine sum_congr rfl fun c' hc' => ?_
  rw [smul_sum]
  refine sum_congr rfl fun a' ha' => ?_
  simp only [mem_range] at hm hc' ha'
  rw [← sum_smul]
  congr 1
  have h : x + y + s - r = (x + c' - a') + (y + ((s - m - c' : ℕ) : ℤ) - ((r - m - a' : ℕ) : ℤ)) := by
    omega
  rw [h, Ring.add_choose_eq _ (Commute.all _ _), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Ring.choose (x + c' - a') i *
      Ring.choose (y + ((s - m - c' : ℕ) : ℤ) - ((r - m - a' : ℕ) : ℤ)) j)]

/-- (P1), (K) of the proof sketch (auxiliary): the coefficient comparison. Writing
`T(a', c', b', d')` for `F^{(a')}E^{(c')} δ_i ⊗ F^{(b')}E^{(d')} δ_j`, the expansion of
`E^{(s)} F^{(r)} (δ_i ⊗ δ_j)` by (K) of both factors (left) equals the expansion of
`Σ_m C(w_i + w_j + s − r, m) F^{(r−m)} E^{(s−m)} (δ_i ⊗ δ_j)` (right). -/
lemma vand_K (x y : ℤ) (r s : ℕ) (T : ℕ → ℕ → ℕ → ℕ → X) :
    ∑ a ∈ range (r + 1), ∑ c ∈ range (s + 1), ∑ k ∈ range (min a c + 1),
      ∑ l ∈ range (min (r - a) (s - c) + 1),
        (Ring.choose (x + c - a) k * Ring.choose (y + ((s - c : ℕ) : ℤ) - ((r - a : ℕ) : ℤ)) l) •
          T (a - k) (c - k) (r - a - l) (s - c - l) =
    ∑ m ∈ range (min r s + 1), Ring.choose (x + y + s - r) m •
      ∑ c' ∈ range (s - m + 1), ∑ a' ∈ range (r - m + 1), T a' c' (r - m - a') (s - m - c') := by
  rw [vand_K_rhs]
  simp only [sum_sigma']
  refine sum_bij' (fun p _ => ⟨p.2.2.1 + p.2.2.2, p.2.1 - p.2.2.1, p.1 - p.2.2.1, p.2.2.1⟩)
    (fun q _ => ⟨q.2.2.1 + q.2.2.2, q.2.1 + q.2.2.2, q.2.2.2, q.1 - q.2.2.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, c, k, l⟩ h
    simp only [mem_sigma, mem_range] at h ⊢
    omega
  · rintro ⟨m, c', a', k⟩ h
    simp only [mem_sigma, mem_range] at h ⊢
    omega
  · rintro ⟨a, c, k, l⟩ h
    simp only [mem_sigma, mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    omega
  · rintro ⟨m, c', a', k⟩ h
    simp only [mem_sigma, mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨a, c, k, l⟩ h
    simp only [mem_sigma, mem_range] at h
    dsimp only
    have e1 : r - (k + l) - (a - k) = r - a - l := by omega
    have e2 : s - (k + l) - (c - k) = s - c - l := by omega
    have e3 : (x + ((c - k : ℕ) : ℤ) - ((a - k : ℕ) : ℤ)) = x + c - a := by omega
    have e4 : y + ((s - c : ℕ) : ℤ) - ((r - a : ℕ) : ℤ) =
      y + ((s - c - l : ℕ) : ℤ) - ((r - a - l : ℕ) : ℤ) := by omega
    rw [e1, e2, e3, e4, show k + l - k = l by omega]

end Kcomb

end Tensor2
