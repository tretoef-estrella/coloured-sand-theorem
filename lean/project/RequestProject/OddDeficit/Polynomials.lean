module

public import RequestProject.OddDeficit.Algebra

/-!
# `CSI11_the_odd_deficit_law.md` — **Part Q**: the polynomials `q_t`

Namespace `ColouredSand.OddTwist`.  The encoding is explained in `OddDeficit/Basic.lean`:
`aP p ds t Δ` is `[q_t]_Δ`, `starPow f N` is `f^N`, and `Iod ds` is `I(ds)`.

* **(Q0)** The defining equations: `Q0_zero` and `Q0_succ`.  The second one is restated with
  `[t ∈ I]` as `Q0_succ_I`.
* **(Q1)** `Q1_support`: `aP t Δ ≠ 0 → Δ ⊆ I ∩ [0, t)`, with `I ∩ [0,t)` encoded as
  `(Iod ds).filter (· < t)`.
* **(Q2)** `Q2_const`: `aP t ∅ = 1` for every `t`.
* **(Q3)** `Q3_const`: `(starPow (aP t) N)(∅) = 1`.  The set-partition formula is in
  `OddDeficit/Partition.lean`.

None of these needs `p` prime or the digits `< p`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Deficit

variable (p : ℕ) (ds : List ℕ)

/-- **(Q0)** of `CSI11_the_odd_deficit_law.md`, base case: `aP 0 Δ = [Δ = ∅]`. -/
theorem Q0_zero (Δ : Finset ℕ) : aP p ds 0 Δ = if Δ = ∅ then 1 else 0 := rfl

/-- **(Q0)** of `CSI11_the_odd_deficit_law.md`, recursion:
`aP (t+1) Δ = (starPow (aP t) p)(Δ) − [t < k ∧ d_t ≠ 0]·[t ∈ Δ]·(starPow (aP t) (p − d_t))(Δ ∖ {t})`. -/
theorem Q0_succ (t : ℕ) (Δ : Finset ℕ) :
    aP p ds (t + 1) Δ = starPow (aP p ds t) p Δ -
      (if t < ds.length ∧ ds.getD t 0 ≠ 0 then 1 else 0) * (if t ∈ Δ then 1 else 0) *
        starPow (aP p ds t) (p - ds.getD t 0) (Δ \ {t}) := rfl

lemma mem_Iod_iff (t : ℕ) : t ∈ Iod ds ↔ t < ds.length ∧ ds.getD t 0 ≠ 0 := by
  simp [Iod]

/-- **(Q0)** of `CSI11_the_odd_deficit_law.md`, recursion written with `[t ∈ I]`:
`q_{t+1} = q_t^p − [t ∈ I] y_t q_t^{p − d_t}`. -/
theorem Q0_succ_I (t : ℕ) (Δ : Finset ℕ) :
    aP p ds (t + 1) Δ = starPow (aP p ds t) p Δ -
      (if t ∈ Iod ds then 1 else 0) * (if t ∈ Δ then 1 else 0) *
        starPow (aP p ds t) (p - ds.getD t 0) (Δ \ {t}) := by
  rw [Q0_succ]; simp only [mem_Iod_iff]

/-- Support of `q_t`, in the form used in the proofs: `aP t` vanishes off the subsets of
`I ∩ [0, t)`. -/
lemma aP_support (t : ℕ) :
    ∀ Γ, ¬ Γ ⊆ (Iod ds).filter (· < t) → aP p ds t Γ = 0 := by
  induction t with
  | zero =>
    intro Γ hΓ
    have : Γ ≠ ∅ := by rintro rfl; exact hΓ (empty_subset _)
    simp [Q0_zero, this]
  | succ t ih =>
    intro Γ hΓ
    have hΓ' : ¬ Γ ⊆ (Iod ds).filter (· < t) := fun h =>
      hΓ (h.trans fun x hx => by simp only [mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)
    rw [Q0_succ_I, starPow_support ih p Γ hΓ']
    by_cases hc : t ∈ Iod ds ∧ t ∈ Γ
    · have : ¬ Γ \ {t} ⊆ (Iod ds).filter (· < t) := by
        intro h; apply hΓ
        intro x hx
        by_cases hxt : x = t
        · subst hxt; simp [hc.1]
        · have := h (mem_sdiff.2 ⟨hx, by simpa using hxt⟩)
          simp only [mem_filter] at this ⊢; exact ⟨this.1, by omega⟩
      rw [starPow_support ih _ _ this]; simp
    · rw [not_and_or] at hc
      rcases hc with hc | hc <;> simp [hc]

/-- **(Q1) Support** (`CSI11_the_odd_deficit_law.md`, Part Q):
`aP t Δ ≠ 0 → Δ ⊆ I ∩ [0, t)`. -/
theorem Q1_support (t : ℕ) (Δ : Finset ℕ) (h : aP p ds t Δ ≠ 0) :
    Δ ⊆ (Iod ds).filter (· < t) := by
  by_contra hc; exact h (aP_support p ds t Δ hc)

/-- **(Q2) Constant term** (`CSI11_the_odd_deficit_law.md`, Part Q): `aP t ∅ = 1` for every
`t`. -/
theorem Q2_const (t : ℕ) : aP p ds t ∅ = 1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Q0_succ_I, starPow_empty_of_one ih]; simp

/-- **(Q3) Powers**, constant term (`CSI11_the_odd_deficit_law.md`, Part Q):
`(starPow (aP t) N)(∅) = 1` for every `t` and `N`. -/
theorem Q3_const (t N : ℕ) : starPow (aP p ds t) N ∅ = 1 :=
  starPow_empty_of_one (Q2_const p ds t) N

end ColouredSand.OddTwist
