module

public import RequestProject.SmithBounds.Basic
public import RequestProject.AntitonicFit.IntegerFit

/-!
# Part C of `C2_smith_bounds.md`: Lemma C0 and Lemma 6.4 (convexity)

## Encoding

* The integer sequence `x = (x_0, …, x_{N−1})` is a function `x : ℕ → ℤ` (only positions
  `< N` matter), `fit(x)` is `AntitonicFit.fit N (AntitonicFit.toR x)` and the integer fit
  `ŷ = ifit(x)` is `AntitonicFit.ifit N x`, both from piece C1
  (`RequestProject/AntitonicFit/`).
* `U N x r = Σ_{j=N−r}^{N−1} x_j` and `Y N x r = Σ_{j=N−r}^{N−1} ŷ_j` are sums over
  `Finset.Ico (N - r) N`, i.e. over the last `r` positions (see `tailSum` in
  `RequestProject/SmithBounds/Basic.lean`); they are used for `0 ≤ r ≤ N`.
* A function `d : {0, …, N} → ℤ` is encoded as `d : ℕ → ℤ` (only the values at `r ≤ N`
  matter).  It is convex (`IsConvexOn N d`) if `d(r+1) − d(r) ≤ d(r+2) − d(r+1)` for every
  `r` with `r + 2 ≤ N`.
* "`N − r` is the first position of a level set of `fit(x)`" is encoded as
  `∃ q, AntitonicFit.IsLevelInterval N (fit N (toR x)) (N - r) q`, i.e. `[N − r, q]` is a level
  set of `fit(x)`.
-/

@[expose] public section

namespace SmithBounds

open Finset AntitonicFit

/-- *Part C, Setting* of `C2_smith_bounds.md`: `U(r) = Σ_{j=N−r}^{N−1} x_j`, the sum of the last
`r` entries of `x`. -/
def U (N : ℕ) (x : ℕ → ℤ) (r : ℕ) : ℤ := tailSum N r x

/-- *Part C, Setting* of `C2_smith_bounds.md`: `Y(r) = Σ_{j=N−r}^{N−1} ŷ_j`, the sum of the last
`r` entries of the integer fit `ŷ = ifit(x)` (`AntitonicFit.ifit` of piece C1). -/
noncomputable def Y (N : ℕ) (x : ℕ → ℤ) (r : ℕ) : ℤ := tailSum N r (ifit N x)

/-- *Part C, Setting* of `C2_smith_bounds.md`: `d : {0, …, N} → ℤ` is convex if
`d(r+1) − d(r) ≤ d(r+2) − d(r+1)` for every `r` with `r + 2 ≤ N`. -/
def IsConvexOn (N : ℕ) (d : ℕ → ℤ) : Prop :=
  ∀ r, r + 2 ≤ N → d (r + 1) - d r ≤ d (r + 2) - d (r + 1)

variable {N : ℕ} {x : ℕ → ℤ}

/-- After a level set `[p, q]` of a non-increasing sequence, position `q + 1` (if `< N`) starts
the next level set. (Auxiliary for Lemma C0 of `C2_smith_bounds.md`.) -/
theorem exists_next_level {z : ℕ → ℝ} (hz : NonIncr N z) {p q : ℕ}
    (h : IsLevelInterval N z p q) (hq : q + 1 < N) : ∃ q', IsLevelInterval N z (q + 1) q' := by
  obtain ⟨p', q', hp', hq', h'⟩ := exists_levelInterval hz hq
  refine ⟨q', ?_⟩
  obtain rfl : p' = q + 1 := by
    by_contra hne
    have hpq : max p p' ≤ q := max_le h.1 (by omega)
    have e1 : z (max p p') = z p' := (h'.2.2 _ (by omega)).2 ⟨le_max_right _ _, by omega⟩
    have e2 : z (q + 1) = z p' := (h'.2.2 _ hq).2 ⟨hp', hq'⟩
    have e3 : z (max p p') = z p := h.eq (le_max_left _ _) hpq
    have := ((h.2.2 (q + 1) hq).1 (by rw [e2, ← e1, e3])).2
    omega
  exact h'

/-- Suffix form of Lemma C0: if `p = N` or `p` is the first position of a level set of
`fit(x)`, then `Σ_{j=p}^{N−1} ŷ_j = Σ_{j=p}^{N−1} x_j`. (Auxiliary for Lemma C0 of
`C2_smith_bounds.md`.) -/
theorem sum_Ico_ifit_eq (p : ℕ) (hpN : p ≤ N)
    (hp : p = N ∨ ∃ q, IsLevelInterval N (fit N (toR x)) p q) :
    ∑ j ∈ Ico p N, ifit N x j = ∑ j ∈ Ico p N, x j := by
  induction h : N - p using Nat.strong_induction_on generalizing p with
  | _ k ih =>
    rcases hp with rfl | ⟨q, hq⟩
    · simp
    · have hqN := hq.2.1
      have hpq := hq.1
      rw [← sum_Ico_consecutive _ (show p ≤ q + 1 by omega) (show q + 1 ≤ N by omega),
        ← sum_Ico_consecutive x (show p ≤ q + 1 by omega) (show q + 1 ≤ N by omega),
        Finset.Ico_add_one_right_eq_Icc, (consequence_L hq).2]
      congr 1
      refine ih (N - (q + 1)) (by omega) (q + 1) (by omega) ?_ rfl
      rcases Nat.lt_or_ge (q + 1) N with hlt | hge
      · exact Or.inr (exists_next_level (fit_nonIncr _ _) hq hlt)
      · exact Or.inl (by omega)

/-- **Lemma C0** of `C2_smith_bounds.md` (general form): if `r ≤ N` and `r = 0` or `N − r` is
the first position of a level set of `fit(x)`, then `Y(r) = U(r)`. -/
theorem lemma_C0 {r : ℕ} (hr : r ≤ N)
    (h : r = 0 ∨ ∃ q, IsLevelInterval N (fit N (toR x)) (N - r) q) : Y N x r = U N x r := by
  unfold Y U tailSum
  refine sum_Ico_ifit_eq (N - r) (by omega) ?_
  rcases h with rfl | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- **Lemma C0** of `C2_smith_bounds.md` (first statement): `Y(N) = U(N)`. -/
theorem lemma_C0_total : Y N x N = U N x N := by
  unfold Y U tailSum
  exact sum_Ico_ifit_eq (N - N) (by omega) (by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inl (by omega)
    · obtain ⟨p, q, hp, -, hpq⟩ := exists_levelInterval (fit_nonIncr N (toR x)) h
      obtain rfl : p = 0 := by omega
      exact Or.inr ⟨q, by simpa using hpq⟩)

/-- If all increments of `f` on `[a, b)` are `≤ c`, then `f b − f a ≤ (b − a) c`.
(Auxiliary for Lemma 6.4 of `C2_smith_bounds.md`.) -/
theorem sub_le_of_incr_le {f : ℕ → ℤ} {c : ℤ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → f (i + 1) - f i ≤ c) : f b - f a ≤ ((b : ℤ) - a) * c := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    have h1 := ih (fun i hi hik => h i hi (by omega))
    have h2 := h k hak (by omega)
    push_cast
    linarith

/-- If all increments of `f` on `[a, b)` are `≥ c`, then `f b − f a ≥ (b − a) c`.
(Auxiliary for Lemma 6.4 of `C2_smith_bounds.md`.) -/
theorem le_sub_of_le_incr {f : ℕ → ℤ} {c : ℤ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → c ≤ f (i + 1) - f i) : ((b : ℤ) - a) * c ≤ f b - f a := by
  have := sub_le_of_incr_le (f := fun i => -f i) (c := -c) hab
    (fun i hi hib => by have := h i hi hib; linarith)
  linarith

/-- The block step of the proof of Lemma 6.4: on a block of `P` steps where the increments of
`G` lie in `{q, q + 1}`, a convex `D` with `D ≤ G` at both ends stays `≤ G` inside.
(Auxiliary for Lemma 6.4 of `C2_smith_bounds.md`.) -/
theorem block_le {P : ℕ} {q : ℤ} {D G : ℕ → ℤ}
    (hconv : ∀ i, i + 2 ≤ P → D (i + 1) - D i ≤ D (i + 2) - D (i + 1))
    (hG : ∀ i < P, q ≤ G (i + 1) - G i ∧ G (i + 1) - G i ≤ q + 1)
    (h0 : D 0 ≤ G 0) (hP : D P ≤ G P) : ∀ k ≤ P, D k ≤ G k := by
  have hmono : ∀ i j, i ≤ j → j + 1 ≤ P → D (i + 1) - D i ≤ D (j + 1) - D j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ m him ih => exact (ih (by omega)).trans (hconv m (by omega))
  intro k hk
  by_contra hlt
  push_neg at hlt
  by_cases hall : ∀ i, 0 ≤ i → i < k → D (i + 1) - D i ≤ q
  · have h1 := sub_le_of_incr_le (Nat.zero_le k) hall
    have h2 := le_sub_of_le_incr (f := G) (c := q) (Nat.zero_le k)
      (fun i _ hi => (hG i (by omega)).1)
    push_cast at h1 h2
    linarith
  · push_neg at hall
    obtain ⟨i, -, hik, hi⟩ := hall
    have h1 := le_sub_of_le_incr (f := D) (c := q + 1) hk
      (fun j hj hjP => (show q + 1 ≤ D (i + 1) - D i by omega).trans
        (hmono i j (by omega) (by omega)))
    have h2 := sub_le_of_incr_le (f := G) (c := q + 1) hk (fun j _ hj => (hG j hj).2)
    linarith

/-- **Lemma 6.4** (convexity) of `C2_smith_bounds.md`: let `d : {0, …, N} → ℤ` be convex with
`d(0) = 0` and `d(r) ≤ U(r)` for every `0 ≤ r ≤ N`.  Then `d(r) ≤ Y(r)` for every
`0 ≤ r ≤ N`, where `Y` is built from the integer fit `AntitonicFit.ifit` of piece C1. -/
theorem lemma_6_4 (d : ℕ → ℤ) (hconv : IsConvexOn N d) (hd0 : d 0 = 0)
    (hdU : ∀ r ≤ N, d r ≤ U N x r) : ∀ r ≤ N, d r ≤ Y N x r := by
  intro r hr
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [hd0, Y, tailSum_zero]
  obtain ⟨p, q, hpj, hjq, hpq⟩ :=
    exists_levelInterval (fit_nonIncr N (toR x)) (show N - r < N by omega)
  have hqN := hpq.2.1
  have hpq' := hpq.1
  -- the block occupies the steps `r₀, …, r₀ + P` counted from the end
  set r₀ := N - 1 - q with hr₀
  set P := q - p + 1 with hP
  have hY0 : d r₀ ≤ Y N x r₀ := by
    rw [lemma_C0 (by omega) ?_]
    · exact hdU r₀ (by omega)
    rcases Nat.lt_or_ge (q + 1) N with hlt | hge
    · right
      rw [show N - r₀ = q + 1 by omega]
      exact exists_next_level (fit_nonIncr _ _) hpq hlt
    · left; omega
  have hY1 : d (r₀ + P) ≤ Y N x (r₀ + P) := by
    rw [lemma_C0 (by omega) (Or.inr ⟨q, by rwa [show N - (r₀ + P) = p by omega]⟩)]
    exact hdU _ (by omega)
  have key := block_le (P := P) (q := (∑ i ∈ Icc p q, x i) / (P : ℤ))
    (D := fun k => d (r₀ + k)) (G := fun k => Y N x (r₀ + k))
    (fun i hi => by
      have := hconv (r₀ + i) (by omega)
      simpa [add_assoc] using this)
    (fun i hi => by
      simp only
      rw [show r₀ + (i + 1) = r₀ + i + 1 by omega, Y, Y, tailSum_succ (by omega),
        add_sub_cancel_left, ifit_eq_of_level hpq (by omega) (by omega),
        blockF_eq _ (by omega), ← hP]
      split_ifs <;> omega)
    (by simpa using hY0) hY1 (r - r₀) (by omega)
  simpa [show r₀ + (r - r₀) = r by omega] using key

end SmithBounds
