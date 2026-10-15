module

public import RequestProject.SmithBounds.Basic

/-!
# Part D of `C2_smith_bounds.md`: Lemma D0 and Theorem 7.4 (Theorem U)

## Encoding

* Positions are natural numbers `< N`; sequences (`ŷ`, `v`, `w`) are functions `ℕ → ℝ` and
  `Y(r) = tailSum N r ŷ = Σ_{j=N−r}^{N−1} ŷ_j` (see `RequestProject/SmithBounds/Basic.lean`).
* The arrows are a relation `arr : ℕ → ℕ → Prop` and the costs `c : ℕ → ℕ → ℝ`.
* An `r`-matching (`IsRMatching N arr r Rows β`) is a finite set `Rows ⊆ {0, …, N−1}` with
  `|Rows| = r`, together with a map `β : ℕ → ℕ` (only its values on `Rows` matter) which is
  injective on `Rows`, takes values in `{0, …, N−1}` on `Rows`, and satisfies `arr a (β a)` for
  every `a ∈ Rows`.  Its cost is `Σ_{a∈Rows} c(a, β a)`.
* (U3) is only required for arrows between positions `a, b < N` (this is what the file says;
  it is weaker than asking it for all natural numbers).
-/

@[expose] public section

namespace SmithBounds

open Finset

/-- Upper half of Lemma D0: the sum over a set `S` of positions is at most the sum of the first
`|S|` values. (Auxiliary for Lemma D0 of `C2_smith_bounds.md`.) -/
theorem sum_le_sum_range_card {N : ℕ} {f : ℕ → ℝ} (hf : NonIncrOn N f) {S : Finset ℕ}
    (hS : S ⊆ range N) : ∑ j ∈ S, f j ≤ ∑ j ∈ range S.card, f j := by
  induction N generalizing S with
  | zero =>
    have : S = ∅ := by simpa using hS
    simp [this]
  | succ N ih =>
    by_cases hN : N ∈ S
    · have hS' : S.erase N ⊆ range N := by
        intro i hi
        have := hS (mem_of_mem_erase hi)
        simp only [mem_range] at this ⊢
        have := ne_of_mem_erase hi
        omega
      have hcard : (S.erase N).card ≤ N := by simpa using card_le_card hS'
      rw [← add_sum_erase S f hN, ← card_erase_add_one hN, sum_range_succ, add_comm]
      exact add_le_add (ih (hf.mono (by omega)) hS') (hf.anti hcard (by omega))
    · have hS' : S ⊆ range N := by
        intro i hi
        have := hS hi
        simp only [mem_range] at this ⊢
        have : i ≠ N := fun h => hN (h ▸ hi)
        omega
      exact ih (hf.mono (by omega)) hS'

/-- Lower half of Lemma D0: the sum over a set `S` of positions is at least the sum of the last
`|S|` values. (Auxiliary for Lemma D0 of `C2_smith_bounds.md`.) -/
theorem tailSum_card_le_sum {N : ℕ} {f : ℕ → ℝ} (hf : NonIncrOn N f) {S : Finset ℕ}
    (hS : S ⊆ range N) : tailSum N S.card f ≤ ∑ j ∈ S, f j := by
  induction N generalizing S with
  | zero =>
    have : S = ∅ := by simpa using hS
    simp [this, tailSum]
  | succ N ih =>
    by_cases hN : N ∈ S
    · have hS' : S.erase N ⊆ range N := by
        intro i hi
        have := hS (mem_of_mem_erase hi)
        simp only [mem_range] at this ⊢
        have := ne_of_mem_erase hi
        omega
      have hcard : (S.erase N).card ≤ N := by simpa using card_le_card hS'
      have h1 := ih (hf.mono (by omega)) hS'
      rw [← add_sum_erase S f hN, ← card_erase_add_one hN]
      unfold tailSum at h1 ⊢
      rw [show N + 1 - ((S.erase N).card + 1) = N - (S.erase N).card by omega,
        sum_Ico_succ_top (by omega), add_comm]
      linarith
    · have hS' : S ⊆ range N := by
        intro i hi
        have := hS hi
        simp only [mem_range] at this ⊢
        have : i ≠ N := fun h => hN (h ▸ hi)
        omega
      have hcard : S.card ≤ N := by simpa using card_le_card hS'
      refine le_trans ?_ (ih (hf.mono (by omega)) hS')
      unfold tailSum
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · simp [h0]
      · rw [sum_Ico_succ_top (by omega), sum_eq_sum_Ico_succ_bot (by omega : N - S.card < N),
          show N + 1 - S.card = N - S.card + 1 by omega]
        have := hf.anti (show N - S.card ≤ N by omega) (by omega)
        linarith

/-- **Lemma D0** (the two sum facts) of `C2_smith_bounds.md`: if `f` is non-increasing on
`{0, …, N−1}` and `S` is a set of `r ≤ N` positions, then
`Σ_{j=N−r}^{N−1} f(j) ≤ Σ_{j∈S} f(j) ≤ Σ_{j=0}^{r−1} f(j)`. -/
theorem lemma_D0 {N r : ℕ} {f : ℕ → ℝ} (hf : NonIncrOn N f) {S : Finset ℕ}
    (hS : S ⊆ range N) (hcard : S.card = r) :
    tailSum N r f ≤ ∑ j ∈ S, f j ∧ ∑ j ∈ S, f j ≤ ∑ j ∈ range r, f j := by
  subst hcard
  exact ⟨tailSum_card_le_sum hf hS, sum_le_sum_range_card hf hS⟩

/-- *Part D, Setting* of `C2_smith_bounds.md`: an `r`-matching is a set `Rows` of `r` positions
with an injective map `β : Rows → {0, …, N−1}` such that `arr a (β a)` for every `a ∈ Rows`
(`β` is a function on `ℕ`, of which only the values on `Rows` matter). -/
def IsRMatching (N : ℕ) (arr : ℕ → ℕ → Prop) (r : ℕ) (Rows : Finset ℕ) (β : ℕ → ℕ) : Prop :=
  Rows ⊆ range N ∧ Rows.card = r ∧ Set.InjOn β Rows ∧ (∀ a ∈ Rows, β a < N) ∧
    ∀ a ∈ Rows, arr a (β a)

/-- The reflection `j ↦ N − 1 − j` sends the last `r` positions onto the first `r`.
(Auxiliary for Theorem 7.4 of `C2_smith_bounds.md`.) -/
theorem tailSum_reflect {N r : ℕ} (hr : r ≤ N) (w : ℕ → ℝ) :
    tailSum N r (fun j => w (N - 1 - j)) = ∑ j ∈ range r, w j := by
  unfold tailSum
  rw [sum_Ico_eq_sum_range, show N - (N - r) = r by omega, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  congr 1
  omega

/-- **Theorem 7.4 (Theorem U)** of `C2_smith_bounds.md`: if there are real functions `v`, `w`
on the positions with (U1) `v`, `w` non-increasing, (U2) `v(j) − w(N−1−j) = ŷ_j` for every
position `j`, and (U3) `v(a) − w(b) ≤ c(a, b)` for every arrow `arr a b`, then every
`r`-matching costs at least `Y(r) = Σ_{j=N−r}^{N−1} ŷ_j`. -/
theorem theorem_U {N : ℕ} (arr : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℝ) (yhat v w : ℕ → ℝ)
    (hU1v : NonIncrOn N v) (hU1w : NonIncrOn N w)
    (hU2 : ∀ j < N, v j - w (N - 1 - j) = yhat j)
    (hU3 : ∀ a < N, ∀ b < N, arr a b → v a - w b ≤ c a b)
    {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ} (hm : IsRMatching N arr r Rows β) :
    tailSum N r yhat ≤ ∑ a ∈ Rows, c a (β a) := by
  obtain ⟨hRows, hcard, hinj, hβN, harr⟩ := hm
  have hrN : r ≤ N := by simpa [hcard] using card_le_card hRows
  have hC : Rows.image β ⊆ range N := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    exact mem_range.2 (hβN a ha)
  have hCcard : (Rows.image β).card = r := by rw [card_image_of_injOn hinj, hcard]
  calc tailSum N r yhat = tailSum N r v - ∑ j ∈ range r, w j := by
        rw [← tailSum_reflect hrN w]
        unfold tailSum
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j hj => ?_
        exact (hU2 j (mem_Ico.1 hj).2).symm
    _ ≤ ∑ a ∈ Rows, v a - ∑ b ∈ Rows.image β, w b :=
        sub_le_sub (lemma_D0 hU1v hRows hcard).1 (lemma_D0 hU1w hC hCcard).2
    _ = ∑ a ∈ Rows, (v a - w (β a)) := by rw [sum_image hinj, sum_sub_distrib]
    _ ≤ ∑ a ∈ Rows, c a (β a) := by
        refine sum_le_sum fun a ha => ?_
        exact hU3 a (mem_range.1 (hRows ha)) (β a) (hβN a ha) (harr a ha)

end SmithBounds
