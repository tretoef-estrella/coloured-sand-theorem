module

public import RequestProject.OddDeficit.Polynomials

/-!
# `CSI11_the_odd_deficit_law.md` — **(Q3)**: the set-partition formula for powers

Namespace `ColouredSand.OddTwist`.  A set partition of `Γ` is an element of `setPartitions Γ`
(see `OddDeficit/Basic.lean`): a finite set of non-empty, pairwise disjoint blocks whose union is
`Γ`.  The falling factorial `N(N−1)⋯(N−j+1)` is `N.descFactorial j`.

* `starPow_eq_sum_partitions`: for any `f` with `f(∅) = 1` (over any commutative ring) and
  **every** `Γ`,
  `[f^N]_Γ = Σ_{P partition of Γ} N(N−1)⋯(N−|P|+1) · ∏_{B ∈ P} f(B)`.
* `Q3_partition`: the same formula for `q = q_t`, i.e. `f = aP p ds t`.

**More general than the file.** The file states the formula for `Γ ≠ ∅` and partitions into
`j ≤ N` blocks.  Here the sum runs over all partitions: those with more than `N` blocks have the
falling factorial `0` and drop out.  The case `Γ = ∅` holds too (its only partition is the
empty one).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Deficit

lemma mem_setPartitions {Γ : Finset ℕ} {P : Finset (Finset ℕ)} :
    P ∈ setPartitions Γ ↔ (∀ B ∈ P, B.Nonempty) ∧
      (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧ P.sup id = Γ := by
  unfold setPartitions
  rw [mem_filter, and_iff_right_iff_imp]
  rintro ⟨-, -, hsup⟩
  rw [mem_powerset]
  intro B hB
  rw [mem_powerset, ← hsup]
  exact le_sup (f := id) hB

/-- `(N+1)_j = (N)_j + j·(N)_{j−1}` for falling factorials. -/
lemma descFactorial_succ_eq (N j : ℕ) :
    (N + 1).descFactorial j = N.descFactorial j + j * N.descFactorial (j - 1) := by
  rcases j with _ | i
  · simp
  · rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ, Nat.add_sub_cancel]
    by_cases hi : i ≤ N
    · have : N - i + (i + 1) = N + 1 := by omega
      rw [← add_mul, this]
    · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp

variable {R : Type*} [CommRing R]

/-- The splitting bijection: pairs (a non-empty block `Γ₁ ⊆ Γ`, a partition of `Γ ∖ Γ₁`)
correspond to pairs (a partition `Q` of `Γ`, a block `B ∈ Q`). -/
lemma sum_block_partition (Γ : Finset ℕ) (F : Finset (Finset ℕ) → Finset ℕ → R) :
    ∑ Γ₁ ∈ Γ.powerset.erase ∅, ∑ P ∈ setPartitions (Γ \ Γ₁), F (insert Γ₁ P) Γ₁ =
      ∑ Q ∈ setPartitions Γ, ∑ B ∈ Q, F Q B := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨insert x.1 x.2, x.1⟩) (fun y _ => ⟨y.2, y.1.erase y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨Γ₁, P⟩ hx
    simp only [mem_sigma, mem_erase, mem_powerset, mem_setPartitions] at hx ⊢
    obtain ⟨⟨hne, hsub⟩, hP1, hP2, hP3⟩ := hx
    have hne' : Γ₁.Nonempty := nonempty_iff_ne_empty.2 hne
    have hdisj : ∀ B ∈ P, Disjoint Γ₁ B := by
      intro B hB
      have : B ⊆ Γ \ Γ₁ := hP3 ▸ le_sup (f := id) hB
      exact disjoint_of_subset_right this disjoint_sdiff
    refine ⟨⟨?_, ?_, ?_⟩, mem_insert_self _ _⟩
    · intro B hB
      rcases mem_insert.1 hB with h | h
      · rw [h]; exact hne'
      · exact hP1 B h
    · intro B hB B' hB' hBB'
      rw [mem_insert] at hB hB'
      rcases hB with h1 | h1 <;> rcases hB' with h2 | h2
      · exact absurd (h1.trans h2.symm) hBB'
      · rw [h1]; exact hdisj B' h2
      · rw [h2]; exact (hdisj B h1).symm
      · exact hP2 B h1 B' h2 hBB'
    · rw [sup_insert, hP3]
      simpa using hsub
  · rintro ⟨Q, B⟩ hy
    simp only [mem_sigma, mem_erase, mem_powerset, mem_setPartitions] at hy ⊢
    obtain ⟨⟨hQ1, hQ2, hQ3⟩, hB⟩ := hy
    refine ⟨⟨(hQ1 B hB).ne_empty, hQ3 ▸ le_sup (f := id) hB⟩, ?_, ?_, ?_⟩
    · intro B' hB'; exact hQ1 B' hB'.2
    · intro B₁ h1 B₂ h2 h12; exact hQ2 B₁ h1.2 B₂ h2.2 h12
    · ext x
      simp only [mem_sup, id, mem_erase, mem_sdiff, ← hQ3]
      constructor
      · rintro ⟨B', ⟨hB'B, hB'Q⟩, hxB'⟩
        refine ⟨⟨B', hB'Q, hxB'⟩, fun hxB => ?_⟩
        exact disjoint_left.1 (hQ2 B' hB'Q B hB hB'B) hxB' hxB
      · rintro ⟨⟨B', hB'Q, hxB'⟩, hxB⟩
        exact ⟨B', ⟨fun h => hxB (h ▸ hxB'), hB'Q⟩, hxB'⟩
  · rintro ⟨Γ₁, P⟩ hx
    simp only [mem_sigma, mem_erase, mem_powerset, mem_setPartitions] at hx
    obtain ⟨⟨hne, -⟩, -, -, hP3⟩ := hx
    have hnot : Γ₁ ∉ P := by
      intro h
      have h1 : Γ₁ ⊆ Γ \ Γ₁ := hP3 ▸ le_sup (f := id) h
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
      exact (mem_sdiff.1 (h1 hx)).2 hx
    simp [erase_insert hnot]
  · rintro ⟨Q, B⟩ hy
    simp only [mem_sigma] at hy
    simp [insert_erase hy.2]
  · rintro ⟨Γ₁, P⟩ _
    rfl

/-- **(Q3) Powers, the set-partition formula** (`CSI11_the_odd_deficit_law.md`, Part Q), for
any coefficient function `f` with `f(∅) = 1` over any commutative ring:
`[f^N]_Γ = Σ_{P partition of Γ} N(N−1)⋯(N−|P|+1) · ∏_{B ∈ P} f(B)`.
More general than the file: it holds for every `Γ`, including `Γ = ∅`, and the partitions into
more than `N` blocks contribute `0`. -/
theorem starPow_eq_sum_partitions {f : Finset ℕ → R} (hf : f ∅ = 1) (N : ℕ) (Γ : Finset ℕ) :
    starPow f N Γ =
      ∑ P ∈ setPartitions Γ, (N.descFactorial P.card : R) * ∏ B ∈ P, f B := by
  induction N generalizing Γ with
  | zero =>
    simp only [starPow]
    have hz : ∀ P : Finset (Finset ℕ), P ≠ ∅ → (Nat.descFactorial 0 P.card : R) = 0 := by
      intro P hP
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.2
        (nonempty_iff_ne_empty.2 hP))
      rw [hn, Nat.zero_descFactorial_succ]; simp
    rcases Γ.eq_empty_or_nonempty with rfl | hΓ
    · rw [if_pos rfl, sum_eq_single (∅ : Finset (Finset ℕ))]
      · simp
      · intro P _ hP
        rw [hz P hP, zero_mul]
      · intro h; exact absurd (mem_setPartitions.2 ⟨by simp, by simp, by simp⟩) h
    · rw [if_neg hΓ.ne_empty]
      symm
      refine sum_eq_zero fun P hP => ?_
      have hPne : P ≠ ∅ := by
        rintro rfl
        have := (mem_setPartitions.1 hP).2.2
        simp at this; exact hΓ.ne_empty this.symm
      rw [hz P hPne, zero_mul]
  | succ N ih =>
    show starMul f (starPow f N) Γ = _
    unfold starMul
    simp_rw [ih]
    rw [← add_sum_erase _ _ (empty_mem_powerset Γ)]
    simp only [hf, one_mul, sdiff_empty]
    have hsplit : ∀ Γ₁ ∈ Γ.powerset.erase ∅,
        f Γ₁ * ∑ P ∈ setPartitions (Γ \ Γ₁), (N.descFactorial P.card : R) * ∏ B ∈ P, f B =
        ∑ P ∈ setPartitions (Γ \ Γ₁),
          (fun Q (_ : Finset ℕ) => (N.descFactorial (Q.card - 1) : R) * ∏ B ∈ Q, f B)
            (insert Γ₁ P) Γ₁ := by
      intro Γ₁ hΓ₁
      rw [mul_sum]
      refine sum_congr rfl fun P hP => ?_
      simp only [mem_erase, mem_powerset] at hΓ₁
      have hnot : Γ₁ ∉ P := by
        intro h
        have h1 : Γ₁ ⊆ Γ \ Γ₁ := (mem_setPartitions.1 hP).2.2 ▸ le_sup (f := id) h
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hΓ₁.1
        exact (mem_sdiff.1 (h1 hx)).2 hx
      beta_reduce
      rw [card_insert_of_notMem hnot, prod_insert hnot, Nat.add_sub_cancel]
      ring
    rw [sum_congr rfl hsplit,
      sum_block_partition Γ (fun Q _ => (N.descFactorial (Q.card - 1) : R) * ∏ B ∈ Q, f B),
      ← sum_add_distrib]
    refine sum_congr rfl fun Q _ => ?_
    rw [sum_const, nsmul_eq_mul, descFactorial_succ_eq]
    push_cast
    ring

/-- **(Q3) Powers, the set-partition formula** (`CSI11_the_odd_deficit_law.md`, Part Q), for
`q = q_t`:
`[q_t^N]_Γ = Σ_{P partition of Γ} N(N−1)⋯(N−|P|+1) · ∏_{B ∈ P} [q_t]_B`.
More general than the file: it holds for every `Γ` (also `Γ = ∅`), and partitions into more
than `N` blocks contribute `0`. -/
theorem Q3_partition (p : ℕ) (ds : List ℕ) (t N : ℕ) (Γ : Finset ℕ) :
    starPow (aP p ds t) N Γ =
      ∑ P ∈ setPartitions Γ, (N.descFactorial P.card : ℤ) * ∏ B ∈ P, aP p ds t B :=
  starPow_eq_sum_partitions (Q2_const p ds t) N Γ

end ColouredSand.OddTwist
