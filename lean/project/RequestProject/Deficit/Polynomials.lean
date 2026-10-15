module

public import RequestProject.Deficit.Basic

/-!
# Part A of `C10_deficit_law.md`: the polynomials `q_t`

(A1) support, (A2) constant term, (A3) the deficit (general form), Lemma 4.5 (the deficit law),
(A4) strict subadditivity, (A5) the example `λ = 6`.  The encoding is described in
`RequestProject/Deficit/Basic.lean`.
-/

@[expose] public section

namespace Deficit

open Finset

/-! ### (A1) -/

/-- **(A1) Support** (`C10_deficit_law.md`, Part A): for every `t` and `Δ`, if
`Δ ⊄ {u ∈ I : u < t}` then `a_t(Δ) = 0`. -/
theorem A1_support (I : Finset ℕ) (t : ℕ) (Δ : Finset ℕ)
    (hΔ : ¬ Δ ⊆ I.filter (· < t)) : a I t Δ = 0 := by
  induction t generalizing Δ with
  | zero =>
    have : Δ ≠ ∅ := by rintro rfl; exact hΔ (empty_subset _)
    simp [a, this]
  | succ t ih =>
    have h1 : starMul (a I t) (a I t) Δ = 0 := by
      apply sum_eq_zero
      intro Δ₁ hΔ₁
      rw [mem_powerset] at hΔ₁
      by_cases h : Δ₁ ⊆ I.filter (· < t)
      · rw [ih (Δ \ Δ₁), mul_zero]
        intro h2; apply hΔ; intro x hx
        by_cases hx1 : x ∈ Δ₁
        · have := mem_filter.1 (h hx1); exact mem_filter.2 ⟨this.1, by omega⟩
        · have := mem_filter.1 (h2 (mem_sdiff.2 ⟨hx, hx1⟩)); exact mem_filter.2 ⟨this.1, by omega⟩
      · rw [ih Δ₁ h, zero_mul]
    have h2 : (if t ∈ I then (1 : ℤ) else 0) * (if t ∈ Δ then 1 else 0) * a I t (Δ \ {t}) = 0 := by
      by_cases ht : t ∈ I ∧ t ∈ Δ
      · rw [ih (Δ \ {t}), mul_zero]
        intro h3; apply hΔ; intro x hx
        by_cases hxt : x = t
        · subst hxt; simp [ht.1]
        · have := mem_filter.1 (h3 (mem_sdiff.2 ⟨hx, by simpa using hxt⟩))
          exact mem_filter.2 ⟨this.1, by omega⟩
      · rcases not_and_or.1 ht with h | h <;> simp [h]
    simp only [a, h1, h2, sub_zero]

/-! ### (A2) -/

lemma a_succ_empty (I : Finset ℕ) (t : ℕ) : a I (t + 1) ∅ = a I t ∅ ^ 2 := by
  simp [a, starMul, sq]

/-- **(A2) Constant term** (`C10_deficit_law.md`, Part A): for every `t ≥ 1`, `a_t(∅) = 1`. -/
theorem A2_const (I : Finset ℕ) (t : ℕ) (ht : 1 ≤ t) : a I t ∅ = 1 := by
  induction t, ht using Nat.le_induction with
  | base => rw [a_succ_empty]; simp [a]
  | succ t _ ih => rw [a_succ_empty, ih]; norm_num

lemma a_empty_sq (I : Finset ℕ) (t : ℕ) : a I t ∅ = 1 ∨ a I t ∅ = -1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · right; simp [a]
  · left; exact A2_const I t ht

/-! ### (A3) -/

lemma card_add_min_le (Δ : Finset ℕ) (h : Δ.Nonempty) : Δ.card + Δ.min' h ≤ Δ.max' h + 1 := by
  have hs : Δ ⊆ Icc (Δ.min' h) (Δ.max' h) := fun x hx =>
    mem_Icc.2 ⟨min'_le _ _ hx, le_max' _ _ hx⟩
  have := card_le_card hs
  rw [Nat.card_Icc] at this
  have := min'_le_max' Δ h
  omega

/-- The square `f ⋆ f` at a set `Δ ∋ μ` is twice the sum over the decompositions whose first
part contains `μ`. -/
lemma starMul_self_eq_two_mul {R : Type*} [CommRing R] (f : Finset ℕ → R) (Δ : Finset ℕ)
    {μ : ℕ} (hμ : μ ∈ Δ) :
    starMul f f Δ = 2 * ∑ Δ₁ ∈ Δ.powerset.filter (μ ∈ ·), f Δ₁ * f (Δ \ Δ₁) := by
  unfold starMul
  rw [← sum_filter_add_sum_filter_not _ (μ ∈ ·), two_mul]
  congr 1
  apply sum_nbij' (Δ \ ·) (Δ \ ·)
  · intro x hx
    simp only [mem_filter, mem_powerset] at hx ⊢
    exact ⟨sdiff_subset, by simp [hμ, hx.2]⟩
  · intro x hx
    simp only [mem_filter, mem_powerset] at hx ⊢
    exact ⟨sdiff_subset, by simp [hx.2]⟩
  · intro x hx
    simp only [mem_filter, mem_powerset] at hx
    exact Finset.sdiff_sdiff_eq_self hx.1
  · intro x hx
    simp only [mem_filter, mem_powerset] at hx
    exact Finset.sdiff_sdiff_eq_self hx.1
  · intro x hx
    simp only [mem_filter, mem_powerset] at hx
    rw [Finset.sdiff_sdiff_eq_self hx.1, mul_comm]

/-- The odd-part form of (A3): `a_t(Δ) = 2^{t − |Δ| − min Δ} · u` with `u` odd. -/
lemma A3_odd (I : Finset ℕ) (Δ : Finset ℕ) (h : Δ.Nonempty) (hΔI : Δ ⊆ I) (t : ℕ)
    (ht : Δ.max' h < t) : ∃ u : ℤ, Odd u ∧ a I t Δ = 2 ^ (t - Δ.card - Δ.min' h) * u := by
  induction Δ using Finset.strongInduction generalizing t with
  | H Δ ih =>
  set m := Δ.max' h with hm
  set μ := Δ.min' h with hμ
  have hmΔ : m ∈ Δ := max'_mem Δ h
  have hμΔ : μ ∈ Δ := min'_mem Δ h
  have hcard := card_add_min_le Δ h
  induction t, ht using Nat.le_induction with
  | base =>
    have hstar : starMul (a I m) (a I m) Δ = 0 := by
      apply sum_eq_zero
      intro Δ₁ hΔ₁
      rw [mem_powerset] at hΔ₁
      by_cases hm1 : m ∈ Δ₁
      · rw [A1_support I m Δ₁ (fun hs => by simpa using (mem_filter.1 (hs hm1)).2), zero_mul]
      · rw [A1_support I m (Δ \ Δ₁) (fun hs => by
          simpa using (mem_filter.1 (hs (mem_sdiff.2 ⟨hmΔ, hm1⟩))).2), mul_zero]
    have hrec : a I (m + 1) Δ = -a I m (Δ \ {m}) := by
      simp only [a, hstar, if_pos (hΔI hmΔ), if_pos hmΔ]; ring
    rw [hrec]
    by_cases hne : (Δ \ {m}).Nonempty
    · set Δ' := Δ \ {m} with hΔ'
      have hsub : Δ' ⊂ Δ := by
        rw [hΔ', sdiff_singleton_eq_erase]; exact erase_ssubset hmΔ
      have hmax' : Δ'.max' hne < m := by
        have h1 := max'_mem Δ' hne
        simp only [hΔ', mem_sdiff, mem_singleton] at h1
        exact lt_of_le_of_ne (le_max' _ _ h1.1) h1.2
      have hμm : μ ≠ m := by
        intro hμm
        obtain ⟨x, hx⟩ := hne
        simp only [hΔ', mem_sdiff, mem_singleton] at hx
        have h1 := min'_le Δ x hx.1
        have h2 := le_max' Δ x hx.1
        omega
      have hmin' : Δ'.min' hne = μ := by
        apply le_antisymm
        · exact min'_le _ _ (by simp [hΔ', hμΔ, hμm])
        · exact min'_le _ _ (sdiff_subset (min'_mem Δ' hne))
      have hc' : Δ'.card = Δ.card - 1 := by
        rw [hΔ', sdiff_singleton_eq_erase, card_erase_of_mem hmΔ]
      have hcard' := card_add_min_le Δ' hne
      obtain ⟨u, hu, hu'⟩ := ih Δ' hsub hne (sdiff_subset.trans hΔI) m hmax'
      refine ⟨-u, hu.neg, ?_⟩
      rw [hu', hmin', hc']
      have hpos : 1 ≤ Δ.card := card_pos.2 h
      have : m - (Δ.card - 1) - μ = m + 1 - Δ.card - μ := by omega
      rw [this]; ring
    · have hsub : Δ ⊆ {m} := sdiff_eq_empty_iff_subset.1 (not_nonempty_iff_eq_empty.1 hne)
      have hΔm : Δ = {m} := Subset.antisymm hsub (singleton_subset_iff.2 hmΔ)
      have hc1 : Δ.card = 1 := by rw [hΔm, card_singleton]
      have hμm : μ = m := mem_singleton.1 (hsub hμΔ)
      have hemp : Δ \ {m} = ∅ := not_nonempty_iff_eq_empty.1 hne
      rw [hemp, hc1, hμm]
      rcases a_empty_sq I m with h1 | h1
      · exact ⟨-1, by decide, by rw [h1]; simp⟩
      · exact ⟨1, by decide, by rw [h1]; simp⟩
  | succ t hmt iht =>
    obtain ⟨u, hu, hu'⟩ := iht
    have htΔ : t ∉ Δ := fun htΔ => by have := le_max' Δ t htΔ; omega
    have hrec : a I (t + 1) Δ = starMul (a I t) (a I t) Δ := by
      simp only [a, if_neg htΔ]; ring
    have he : t - Δ.card - μ + 1 = t + 1 - Δ.card - μ := by omega
    -- the cross terms
    have hcross : (2 : ℤ) ^ (t - Δ.card - μ + 1) ∣
        ∑ Δ₁ ∈ (Δ.powerset.filter (μ ∈ ·)).erase Δ, a I t Δ₁ * a I t (Δ \ Δ₁) := by
      apply dvd_sum
      intro Δ₁ hΔ₁
      simp only [mem_erase, mem_filter, mem_powerset] at hΔ₁
      obtain ⟨hne1, hsub1, hμ1⟩ := hΔ₁
      have hn1 : Δ₁.Nonempty := ⟨μ, hμ1⟩
      have hn2 : (Δ \ Δ₁).Nonempty := by
        rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
        exact fun h' => hne1 (Subset.antisymm hsub1 h')
      have hs1 : Δ₁ ⊂ Δ := ssubset_of_subset_of_ne hsub1 hne1
      have hs2 : Δ \ Δ₁ ⊂ Δ := by
        refine ssubset_of_subset_of_ne sdiff_subset ?_
        intro h'
        have : μ ∈ Δ \ Δ₁ := by rw [h']; exact hμΔ
        exact (mem_sdiff.1 this).2 hμ1
      have hmax1 : Δ₁.max' hn1 ≤ m := max'_le _ _ _ (fun x hx => le_max' Δ x (hsub1 hx))
      have hmax2 : (Δ \ Δ₁).max' hn2 ≤ m :=
        max'_le _ _ _ (fun x hx => le_max' Δ x (sdiff_subset hx))
      obtain ⟨u1, -, hu1⟩ := ih Δ₁ hs1 hn1 (hsub1.trans hΔI) t (by omega)
      obtain ⟨u2, -, hu2⟩ := ih (Δ \ Δ₁) hs2 hn2 (sdiff_subset.trans hΔI) t (by omega)
      have hmin1 : Δ₁.min' hn1 = μ :=
        le_antisymm (min'_le _ _ hμ1) (le_min' _ _ _ (fun x hx => min'_le Δ x (hsub1 hx)))
      have hmin2 : (Δ \ Δ₁).min' hn2 ≤ m := le_max' Δ _ (sdiff_subset (min'_mem _ hn2))
      have hc12 : Δ₁.card + (Δ \ Δ₁).card = Δ.card := by
        rw [card_sdiff_of_subset hsub1]; have := card_le_card hsub1; omega
      have hb1 := card_add_min_le Δ₁ hn1
      have hb2 := card_add_min_le (Δ \ Δ₁) hn2
      rw [hu1, hu2, hmin1]
      have hle : t - Δ.card - μ + 1 ≤ (t - Δ₁.card - μ) + (t - (Δ \ Δ₁).card -
          (Δ \ Δ₁).min' hn2) := by omega
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨2 ^ r * u1 * u2, ?_⟩
      rw [mul_mul_mul_comm, ← pow_add, hr, pow_add]; ring
    obtain ⟨w, hw⟩ := hcross
    refine ⟨u + 2 * w, by
      rcases hu with ⟨j, rfl⟩; exact ⟨j + w, by ring⟩, ?_⟩
    rw [hrec, starMul_self_eq_two_mul _ Δ hμΔ, ← add_sum_erase _ _ (mem_filter.2 ⟨mem_powerset_self Δ, hμΔ⟩),
      Finset.sdiff_self, A2_const I t (by omega), hu', hw, ← he]
    ring

/-- From the odd-part form to the valuation. -/
lemma padicValInt_two_pow_mul_odd (e : ℕ) (u : ℤ) (hu : Odd u) :
    (2 : ℤ) ^ e * u ≠ 0 ∧ padicValInt 2 ((2 : ℤ) ^ e * u) = e := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have h2 : (2 : ℤ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨mul_ne_zero h2 hu0, ?_⟩
  rw [padicValInt.mul h2 hu0]
  have h1 : padicValInt 2 ((2 : ℤ) ^ e) = e := by
    have : ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
    rw [this, padicValInt.of_nat, padicValNat.prime_pow]
  have h3 : padicValInt 2 u = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    rintro ⟨j, rfl⟩
    exact (Int.not_even_iff_odd.2 hu) ⟨j, by ring⟩
  rw [h1, h3, add_zero]

/-- **(A3) The deficit, general form** (`C10_deficit_law.md`, Part A): for every `t` and every
non-empty `Δ ⊆ I` with `max Δ < t`, `a_t(Δ) ≠ 0` and `v_2(a_t(Δ)) = t − |Δ| − min Δ`, an
identity of natural numbers; the first conjunct `|Δ| + min Δ ≤ t` records that the right side
does not truncate (it is `≥ 0`). -/
theorem A3_deficit (I : Finset ℕ) (t : ℕ) (Δ : Finset ℕ) (h : Δ.Nonempty) (hΔI : Δ ⊆ I)
    (ht : Δ.max' h < t) :
    Δ.card + Δ.min' h ≤ t ∧ a I t Δ ≠ 0 ∧
      padicValInt 2 (a I t Δ) = t - Δ.card - Δ.min' h := by
  obtain ⟨u, hu, hu'⟩ := A3_odd I Δ h hΔI t ht
  have := card_add_min_le Δ h
  rw [hu']
  exact ⟨by omega, padicValInt_two_pow_mul_odd _ u hu⟩

end Deficit
