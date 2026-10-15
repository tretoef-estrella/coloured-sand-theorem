module

public import RequestProject.Houses.LemmaA

/-!
# Part C of `C6_houses_windows_penalties.md`: the top digit (Lemma 7.7)

**Lemma C** (Lemma 7.7), parts (C1)–(C7).  Encodings as in `RequestProject/Houses/Basic.lean`.
The hypothesis «`I ≠ ∅`, `c := max I`» is written `hne : I.Nonempty` and `hc : c = I.max' hne`;
`I' := I ∖ {c}` is `I.erase c`; the house `H' = (I', c, ℓ mod 2^c, α)` has
`R_{H'} = RH (I.erase c) c (ℓ % 2 ^ c) α` (i.e. `Rulers.ruler c (I.erase c) α (ℓ % 2 ^ c)`),
`J_{H'} = JH c (ℓ % 2 ^ c)`, `x_{H'} = xH (I.erase c) c (ℓ % 2 ^ c) α` and
`γ' = Rulers.gamma c (I.erase c)`.  The data `T, κ, sat, τ` of the window `W_c = [c, k)` of `H` are
`typ ℓ c`, `kap I k ℓ c`, `sat I k ℓ c`, `tau I k ℓ α c`, and its length is `h = k − c`
(`h_max`).  `D₀ ⊆ I'` is `D₀ ⊆ I.erase c`.
-/

@[expose] public section

namespace Houses

open Finset Rulers

variable {I : Finset ℕ} {k ℓ : ℕ}

section Setup

variable {c : ℕ}

lemma next_max (hI : ∀ t ∈ I, t < k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) :
    next k I c = k := by
  unfold next
  apply minOr_eq_of_mem (by simp [hI c hc])
  intro x hx
  simp only [mem_filter, mem_insert] at hx
  rcases hx.1 with rfl | hx'
  · exact le_rfl
  · have := hcmax x hx'; omega

/-- The window of `c = max I` has length `h_c = k − c`. -/
lemma h_max (hI : ∀ t ∈ I, t < k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) :
    h k I c = k - c := by
  unfold h; rw [next_max hI hc hcmax]

lemma next_erase (hI : ∀ t ∈ I, t < k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) {u : ℕ}
    (hu : u ∈ I.erase c) : next k I u = next c (I.erase c) u := by
  have hu' := mem_erase.1 hu
  have huc : u < c := lt_of_le_of_ne (hcmax u hu'.2) hu'.1
  have hcS : c ∈ (insert c (I.erase c)).filter (fun v => u < v) := by simp [huc]
  set m := next c (I.erase c) u
  have hm : m ∈ (insert c (I.erase c)).filter (fun v => u < v) := minOr_mem ⟨c, hcS⟩
  have hmc : m ≤ c := minOr_le hcS
  unfold next
  apply minOr_eq_of_mem
  · simp only [mem_filter, mem_insert, mem_erase] at hm ⊢
    rcases hm.1 with h' | h'
    · exact ⟨Or.inr (h' ▸ hc), hm.2⟩
    · exact ⟨Or.inr h'.2, hm.2⟩
  · intro x hx
    simp only [mem_filter, mem_insert] at hx
    rcases hx.1 with rfl | hx'
    · have := hI c hc; omega
    · by_cases hxc : x = c
      · subst hxc; exact hmc
      · exact minOr_le (by simp [hxc, hx', hx.2])

/-- The windows of the digits of `I'` are the same in `H` and in `H'`. -/
lemma h_erase (hI : ∀ t ∈ I, t < k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) {u : ℕ}
    (hu : u ∈ I.erase c) : h k I u = h c (I.erase c) u := by
  unfold h; rw [next_erase hI hc hcmax hu]

lemma sum_h_erase (hI : ∀ t ∈ I, t < k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) (α : ℤ)
    {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    ∑ t ∈ D₀, ((h k I t : ℤ) - α * 2 ^ t) = ∑ t ∈ D₀, ((h c (I.erase c) t : ℤ) - α * 2 ^ t) :=
  sum_congr rfl (fun t ht => by rw [h_erase hI hc hcmax (hD ht)])

lemma oE_lt_erase (hcmax : ∀ t ∈ I, t ≤ c) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    oE D₀ < 2 ^ c := by
  apply oE_lt
  intro t ht
  have := mem_erase.1 (hD ht)
  exact lt_of_le_of_ne (hcmax t this.2) this.1

lemma q_lt (hℓ : ℓ < 2 ^ k) (hck : c < k) : ℓ / 2 ^ c < 2 ^ (k - c) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c), ← pow_add, Nat.sub_add_cancel hck.le]
  exact hℓ

lemma q_half_lt (hℓ : ℓ < 2 ^ k) (hck : c < k) : ℓ / 2 ^ c / 2 < 2 ^ (k - c - 1) := by
  have := q_lt hℓ hck
  rw [show k - c = (k - c - 1) + 1 by omega, pow_succ] at this
  omega

/-- `κ_c = 1 + v_2(⌊q/2⌋ + 1)` with `q = ⌊ℓ / 2^c⌋`. -/
lemma kap_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) :
    kap I k ℓ c = 1 + v2 (ℓ / 2 ^ c / 2 + 1) := by
  have hck := hI c hc
  have hw := v2_succ_le (q_half_lt hℓ hck)
  have hr2 : r (c + 1) ℓ = v2 (ℓ / 2 ^ c / 2 + 1) := by
    unfold r; rw [Nat.div_div_eq_div_mul, ← pow_succ]
  unfold kap typ bit
  rw [hr2, h_max hI hc hcmax]
  unfold r
  rcases Nat.mod_two_eq_zero_or_one (ℓ / 2 ^ c) with hq | hq
  · simp only [hq, zero_ne_one, if_false]; omega
  · rw [if_pos hq, v2_succ_of_odd hq]; omega

/-- `[T = 1] κ = v_2(q + 1)` with `q = ⌊ℓ / 2^c⌋`. -/
lemma typ_kap_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hc : c ∈ I)
    (hcmax : ∀ t ∈ I, t ≤ c) :
    (if typ ℓ c = 1 then kap I k ℓ c else 0) = v2 (ℓ / 2 ^ c + 1) := by
  rw [kap_max hI hℓ hc hcmax]
  unfold typ bit
  rcases Nat.mod_two_eq_zero_or_one (ℓ / 2 ^ c) with hq | hq
  · simp [hq, v2_succ_of_even hq]
  · simp [hq, v2_succ_of_odd hq]

/-- `sat_c = 1` iff `⌊q/2⌋ + 1 = 2^{h−1}`. -/
lemma sat_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) :
    sat I k ℓ c = if ℓ / 2 ^ c / 2 + 1 = 2 ^ (k - c - 1) then 1 else 0 := by
  have hck := hI c hc
  have hlt := q_half_lt hℓ hck
  have hw := v2_succ_le hlt
  have hiff := le_v2_iff (ℓ / 2 ^ c / 2) (k - c - 1)
  rw [Nat.mod_eq_of_lt hlt] at hiff
  unfold sat
  rw [kap_max hI hℓ hc hcmax, h_max hI hc hcmax]
  by_cases h1 : 1 + v2 (ℓ / 2 ^ c / 2 + 1) = k - c
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

/-- The carry out of `H` in terms of the carry out of `H'`. -/
lemma JH_top (hcmax : ∀ t ∈ I, t ≤ c) (hck : c < k) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) (e : ℕ) :
    (2 ^ k ≤ ℓ + (oE D₀ + e * 2 ^ c)) ↔ 2 ^ (k - c) ≤ JH c (ℓ % 2 ^ c) D₀ + (ℓ / 2 ^ c + e) := by
  have hx := oE_lt_erase hcmax hD
  have ha := Nat.mod_lt ℓ (Nat.two_pow_pos c)
  have key := carry_aux (P := 2 ^ c) (M := 2 ^ (k - c)) (X := ℓ % 2 ^ c + oE D₀)
    (Y := ℓ / 2 ^ c + e) (by omega)
  have hℓ := Nat.mod_add_div ℓ (2 ^ c)
  rw [← pow_add, Nat.add_sub_cancel' hck.le] at key
  have hsum : ℓ + (oE D₀ + e * 2 ^ c) = ℓ % 2 ^ c + oE D₀ + 2 ^ c * (ℓ / 2 ^ c + e) := by
    rw [mul_add]; nth_rewrite 1 [← hℓ]; ring
  rw [hsum, key, JH]

lemma oE_insert_max {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) : oE (D₀ ∪ {c}) = oE D₀ + 1 * 2 ^ c := by
  have hcD : c ∉ D₀ := fun h => by simpa using hD h
  rw [oE_union (disjoint_singleton_right.2 hcD)]
  simp [oE]

end Setup

variable {c : ℕ}

/-- **(C1)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `R_H(D₀) = R_{H'}(D₀) − [T = 1] κ J_{H'}(D₀)`. -/
theorem lemma_C1 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    RH I k ℓ α D₀ = RH (I.erase c) c (ℓ % 2 ^ c) α D₀
      - (if typ ℓ c = 1 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hx := oE_lt_erase hcmax hD
  have htk : (if typ ℓ c = 1 then (kap I k ℓ c : ℤ) else 0) = (v2 (ℓ / 2 ^ c + 1) : ℤ) := by
    rw [← typ_kap_max hI hℓ hcI hcmax]; split_ifs <;> simp
  unfold RH ruler
  rw [kappa_split c ℓ (oE D₀) hx, sum_h_erase hI hcI hcmax α hD, htk, JH]
  ring

/-- **(C2)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `R_H(D₀ ∪ {c}) = τ + R_{H'}(D₀) − [T = 0] κ J_{H'}(D₀)`. -/
theorem lemma_C2 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    RH I k ℓ α (D₀ ∪ {c}) = tau I k ℓ α c + RH (I.erase c) c (ℓ % 2 ^ c) α D₀
      - (if typ ℓ c = 0 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hx := oE_lt_erase hcmax hD
  have hcD : c ∉ D₀ := fun h => by simpa using hD h
  have hkap := kap_max hI hℓ hcI hcmax
  have hoE : oE (D₀ ∪ {c}) = oE D₀ + 2 ^ c := by
    rw [oE_insert_max hD, one_mul]
  unfold RH ruler tau
  rw [sum_union (disjoint_singleton_right.2 hcD), sum_singleton, hoE,
    kappa_split_top c ℓ (oE D₀) hx, sum_h_erase hI hcI hcmax α hD, hkap, JH]
  unfold typ bit
  rcases Nat.mod_two_eq_zero_or_one (ℓ / 2 ^ c) with hq | hq
  · rw [v2_succ_of_even hq]
    simp only [hq, zero_ne_one, if_false, if_true]
    split_ifs <;> push_cast <;> ring
  · rw [v2_succ_of_odd hq]
    simp only [hq, one_ne_zero, if_false, if_true]
    split_ifs <;> push_cast <;> ring

/-- **(C3)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `J_H(D₀) = [T = 1] · sat · J_{H'}(D₀)`. -/
theorem lemma_C3 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    JH k ℓ D₀ = (if typ ℓ c = 1 then 1 else 0) * sat I k ℓ c * JH c (ℓ % 2 ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hck := hI c hcI
  have key := JH_top (ℓ := ℓ) hcmax hck hD 0
  simp only [zero_mul, add_zero] at key
  have hq := q_lt hℓ hck
  have hP : 2 ^ (k - c) = 2 * 2 ^ (k - c - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hJ : JH c (ℓ % 2 ^ c) D₀ ≤ 1 := by unfold JH; split_ifs <;> omega
  rw [sat_max hI hℓ hcI hcmax]
  unfold typ bit
  conv_lhs => unfold JH
  rw [hP] at key hq
  generalize JH c (ℓ % 2 ^ c) D₀ = J at key hJ ⊢
  generalize 2 ^ (k - c - 1) = P at key hq ⊢
  generalize ℓ / 2 ^ c = q at key hq ⊢
  by_cases h1 : 2 ^ k ≤ ℓ + oE D₀
  · have := key.1 h1
    rw [if_pos h1]; split_ifs <;> omega
  · rw [if_neg h1]; rw [key] at h1; split_ifs <;> omega

/-- **(C4)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `J_H(D₀ ∪ {c}) = sat · ([T = 1] + [T = 0] J_{H'}(D₀))`. -/
theorem lemma_C4 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    JH k ℓ (D₀ ∪ {c}) = sat I k ℓ c *
      ((if typ ℓ c = 1 then 1 else 0) + (if typ ℓ c = 0 then 1 else 0) * JH c (ℓ % 2 ^ c) D₀) := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hck := hI c hcI
  have key := JH_top (ℓ := ℓ) hcmax hck hD 1
  have hq := q_lt hℓ hck
  have hP : 2 ^ (k - c) = 2 * 2 ^ (k - c - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hJ : JH c (ℓ % 2 ^ c) D₀ ≤ 1 := by unfold JH; split_ifs <;> omega
  rw [sat_max hI hℓ hcI hcmax]
  unfold typ bit
  conv_lhs => unfold JH
  rw [oE_insert_max hD]
  rw [hP] at key hq
  generalize JH c (ℓ % 2 ^ c) D₀ = J at key hJ ⊢
  generalize 2 ^ (k - c - 1) = P at key hq ⊢
  generalize ℓ / 2 ^ c = q at key hq ⊢
  by_cases h1 : 2 ^ k ≤ ℓ + (oE D₀ + 1 * 2 ^ c)
  · have := key.1 h1
    rw [if_pos h1]; split_ifs <;> omega
  · rw [if_neg h1]; rw [key] at h1; split_ifs <;> omega

/-- **(C5)**, first half, of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with
`c = max I`, for `Δ ⊆ I` with `c ∉ Δ` and `Δ ≠ ∅`, `γ(Δ) = γ'(Δ) + h` where `h = k − c`.
(More general than the file: `ℓ < 2^k` plays no role here.) -/
theorem lemma_C5_not_mem (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) (hc : c = I.max' hne)
    {Δ : Finset ℕ} (hΔ : Δ ⊆ I) (hcΔ : c ∉ Δ) (hΔne : Δ ≠ ∅) :
    gamma k I Δ = gamma c (I.erase c) Δ + (k - c) := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hΔn : Δ.Nonempty := nonempty_iff_ne_empty.2 hΔne
  have hmin : minOr k Δ = minOr c Δ := by simp [minOr, hΔn]
  have hm := minOr_mem (k := c) hΔn
  have hmc : minOr c Δ < c :=
    lt_of_le_of_ne (hcmax _ (hΔ hm)) (fun h => hcΔ (h ▸ hm))
  unfold gamma
  rw [if_neg hΔne, if_neg hΔne, hmin]
  have hset : (I \ Δ).filter (fun u => minOr c Δ < u) =
      insert c ((I.erase c \ Δ).filter (fun u => minOr c Δ < u)) := by
    ext u
    simp only [mem_filter, mem_sdiff, mem_insert, mem_erase]
    constructor
    · rintro ⟨⟨huI, huΔ⟩, hmu⟩
      by_cases huc : u = c
      · left; exact huc
      · right; exact ⟨⟨⟨huc, huI⟩, huΔ⟩, hmu⟩
    · rintro (rfl | ⟨⟨⟨_, huI⟩, huΔ⟩, hmu⟩)
      · exact ⟨⟨hcI, hcΔ⟩, hmc⟩
      · exact ⟨⟨huI, huΔ⟩, hmu⟩
  rw [hset, sum_insert (by simp), h_max hI hcI hcmax, add_comm]
  congr 1
  apply sum_congr rfl
  intro u hu
  exact h_erase hI hcI hcmax (mem_sdiff.1 (mem_filter.1 hu).1).1

/-- **(C5)**, second half, of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with
`c = max I`, for `Δ₀ ⊆ I'`, `γ(Δ₀ ∪ {c}) = γ'(Δ₀)`.
(More general than the file: `ℓ < 2^k` plays no role here.) -/
theorem lemma_C5_mem (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) (hc : c = I.max' hne)
    {Δ₀ : Finset ℕ} (hΔ : Δ₀ ⊆ I.erase c) :
    gamma k I (Δ₀ ∪ {c}) = gamma c (I.erase c) Δ₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hne' : Δ₀ ∪ {c} ≠ ∅ := by simp
  unfold gamma
  rw [if_neg hne']
  by_cases hΔ0 : Δ₀ = ∅
  · subst hΔ0
    rw [if_pos rfl]
    apply sum_eq_zero
    intro u hu
    simp only [empty_union, mem_filter, mem_sdiff, mem_singleton] at hu
    have := hcmax u hu.1.1
    have hm : minOr k ({c} : Finset ℕ) = c := minOr_eq_of_mem (by simp) (by simp)
    rw [hm] at hu
    omega
  · rw [if_neg hΔ0]
    have hΔn : Δ₀.Nonempty := nonempty_iff_ne_empty.2 hΔ0
    have hm := minOr_mem (k := c) hΔn
    have hmlt : ∀ t ∈ Δ₀, t < c := fun t ht => by
      have := mem_erase.1 (hΔ ht); exact lt_of_le_of_ne (hcmax t this.2) this.1
    have hmin : minOr k (Δ₀ ∪ {c}) = minOr c Δ₀ := by
      apply minOr_eq_of_mem (by simp [hm])
      intro x hx
      simp only [mem_union, mem_singleton] at hx
      rcases hx with hx | rfl
      · exact minOr_le hx
      · exact (hmlt _ hm).le
    rw [hmin]
    have hset : (I \ (Δ₀ ∪ {c})).filter (fun u => minOr c Δ₀ < u) =
        (I.erase c \ Δ₀).filter (fun u => minOr c Δ₀ < u) := by
      ext u
      simp only [mem_filter, mem_sdiff, mem_union, mem_singleton, mem_erase]
      tauto
    rw [hset]
    apply sum_congr rfl
    intro u hu
    exact h_erase hI hcI hcmax (mem_sdiff.1 (mem_filter.1 hu).1).1

lemma sdiff_max_eq (hcI : c ∈ I) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    I \ D₀ = (I.erase c \ D₀) ∪ {c} := by
  have hcD : c ∉ D₀ := fun h => by simpa using hD h
  ext u
  simp only [mem_sdiff, mem_union, mem_erase, mem_singleton]
  constructor
  · rintro ⟨huI, huD⟩
    by_cases huc : u = c
    · right; exact huc
    · left; exact ⟨⟨huc, huI⟩, huD⟩
  · rintro (⟨⟨_, huI⟩, huD⟩ | rfl)
    · exact ⟨huI, huD⟩
    · exact ⟨hcI, hcD⟩

/-- **(C6)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `x_H(D₀) = x_{H'}(D₀) + d_1(D₀)`, where
`d_1(D₀) = −τ − [T = 1] κ J_{H'}(D₀) + [T = 0] κ J_{H'}(I' ∖ D₀)` (the definition `d1`). -/
theorem lemma_C6 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    xH I k ℓ α D₀ = xH (I.erase c) c (ℓ % 2 ^ c) α D₀ + d1 I k ℓ α c D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  unfold xH d1
  rw [sdiff_max_eq hcI hD, lemma_C1 hI hℓ α hne hc hD,
    lemma_C2 hI hℓ α hne hc (sdiff_subset (s := I.erase c) (t := D₀))]
  ring

/-- **(C7)** of Lemma C (Lemma 7.7), `C6_houses_windows_penalties.md`: with `c = max I` and
`D₀ ⊆ I'`, `x_H(D₀ ∪ {c}) = −(x_{H'}(I' ∖ D₀) + d_1(I' ∖ D₀))`. -/
theorem lemma_C7 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    xH I k ℓ α (D₀ ∪ {c}) =
      -(xH (I.erase c) c (ℓ % 2 ^ c) α (I.erase c \ D₀) + d1 I k ℓ α c (I.erase c \ D₀)) := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hsub : D₀ ∪ {c} ⊆ I := union_subset (hD.trans (erase_subset c I)) (by simp [hcI])
  have hcompl : I \ (D₀ ∪ {c}) = I.erase c \ D₀ := by
    ext u; simp only [mem_sdiff, mem_union, mem_singleton, mem_erase]; tauto
  have hA0 := lemma_A0_antisymm (k := k) ℓ α hsub
  rw [hcompl] at hA0
  rw [← lemma_C6 hI hℓ α hne hc (sdiff_subset (s := I.erase c) (t := D₀)), hA0]
  ring

end Houses
