module

public import RequestProject.Houses.Basic

/-!
# Part B of `C6_houses_windows_penalties.md`: windows and gates (Lemma 7.6)

**Lemma B** (Lemma 7.6), parts (B1)–(B6).  Encodings as in `RequestProject/Houses/Basic.lean`:
the house `H = (I, k, ℓ, α)` is given by its components; the window of `t ∈ I` is
`W_t = Finset.Ico t (next k I t)`; `T_t = typ ℓ t`, `κ_t = kap I k ℓ t`, `sat_t = sat I k ℓ t`,
`τ_t = tau I k ℓ α t`, `c_u(E) = cin ℓ u E`, `car_t(E) = car I k ℓ t E`.  The indicator
`d := [t ∈ E]` of the file is used through `t ∈ E` (`d = 1 ↔ t ∈ E`).
-/

@[expose] public section

namespace Houses

open Finset Rulers

variable {I : Finset ℕ} {k ℓ : ℕ}

lemma cin_le_one (u : ℕ) (E : Finset ℕ) : cin ℓ u E = 0 ∨ cin ℓ u E = 1 := by
  unfold cin; split_ifs <;> simp

lemma typ_le_one (t : ℕ) : typ ℓ t = 0 ∨ typ ℓ t = 1 := by
  unfold typ bit; omega

/-- Inside the window of `t`, the addend `o_E` has at most the bit `t`. -/
lemma oE_mod_window {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ}
    {u : ℕ} (htu : t < u) (hun : u ≤ next k I t) :
    oE E % 2 ^ u = oE E % 2 ^ t + (if t ∈ E then 1 else 0) * 2 ^ t := by
  rw [oE_mod, oE_mod]
  have hf : E.filter (· < u) = E.filter (· < t + 1) := by
    ext s; simp only [mem_filter]; constructor
    · rintro ⟨hs, hsu⟩; refine ⟨hs, ?_⟩; by_contra hc
      have := next_le_of_mem (k := k) (hE hs) (show t < s by omega); omega
    · rintro ⟨hs, hst⟩; exact ⟨hs, by omega⟩
  rw [hf]; simp only [oE, sum_filter]
  rw [show (∑ s ∈ E, if s < t + 1 then 2 ^ s else 0) =
      ∑ s ∈ E, ((if s < t then 2 ^ s else 0) + (if t = s then 2 ^ s else 0)) from
    sum_congr rfl (fun s _ => by split_ifs <;> omega)]
  rw [sum_add_distrib, sum_ite_eq]
  split_ifs <;> simp

/-- The carry into bit `t + j` inside the window of `t` (`1 ≤ j ≤ h_t`). -/
lemma cin_window (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I)
    {j : ℕ} (hj1 : 1 ≤ j) (hjh : j ≤ h k I t) :
    cin ℓ (t + j) E = 1 ↔
      2 ^ j ≤ (cin ℓ t E + (if t ∈ E then 1 else 0)) + ℓ / 2 ^ t % 2 ^ j := by
  have hn := next_spec hI ht
  have hw := oE_mod_window (k := k) hE (t := t) (u := t + j) (by omega) (by unfold h at hjh; omega)
  have hl : ℓ % 2 ^ (t + j) = ℓ % 2 ^ t + 2 ^ t * (ℓ / 2 ^ t % 2 ^ j) := by
    rw [pow_add, Nat.mod_mul]
  have hX : ℓ % 2 ^ t + oE E % 2 ^ t < 2 * 2 ^ t := by
    have := Nat.mod_lt ℓ (Nat.two_pow_pos t)
    have := Nat.mod_lt (oE E) (Nat.two_pow_pos t)
    omega
  have key := carry_aux (M := 2 ^ j)
    (Y := (if t ∈ E then 1 else 0) + ℓ / 2 ^ t % 2 ^ j) hX
  have hsum : ℓ % 2 ^ t + 2 ^ t * (ℓ / 2 ^ t % 2 ^ j) +
      (oE E % 2 ^ t + (if t ∈ E then 1 else 0) * 2 ^ t) =
      ℓ % 2 ^ t + oE E % 2 ^ t + 2 ^ t * ((if t ∈ E then 1 else 0) + ℓ / 2 ^ t % 2 ^ j) := by
    ring
  have hc : cin ℓ (t + j) E = 1 ↔ 2 ^ (t + j) ≤ ℓ % 2 ^ (t + j) + oE E % 2 ^ (t + j) := by
    unfold cin; split_ifs with h <;> simp [h]
  rw [hc, hl, hw, hsum, pow_add, key, add_assoc]
  rfl

/-- The length of the run of carries started by `e ∈ {0, 1, 2}` incoming units on
`q = ⌊ℓ / 2^t⌋`. -/
def runLen (e q : ℕ) : ℕ := if e = 0 then 0 else if e = 1 then v2 (q + 1) else 1 + v2 (q / 2 + 1)

lemma le_runLen_iff {e q j : ℕ} (he : e ≤ 2) (hj : 1 ≤ j) :
    2 ^ j ≤ e + q % 2 ^ j ↔ j ≤ runLen e q := by
  have hlt := Nat.mod_lt q (Nat.two_pow_pos j)
  unfold runLen
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 by omega) with rfl | rfl | rfl
  · simp only [if_true]; omega
  · simp only [one_ne_zero, if_false, if_true]; rw [le_v2_iff]; omega
  · simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false]; exact two_le_iff q j hj

lemma h_eq (t : ℕ) : h k I t = next k I t - t := rfl

/-- `car_t(E) = min(L, h_t)` where `L` is the length of the run of carries. -/
lemma car_eq_min (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    car I k ℓ t E =
      min (runLen (cin ℓ t E + (if t ∈ E then 1 else 0)) (ℓ / 2 ^ t)) (h k I t) := by
  have hn := next_spec hI ht
  have he : cin ℓ t E + (if t ∈ E then 1 else 0) ≤ 2 := by
    rcases cin_le_one (ℓ := ℓ) t E with h | h <;> rw [h] <;> split_ifs <;> omega
  set L := runLen (cin ℓ t E + (if t ∈ E then 1 else 0)) (ℓ / 2 ^ t)
  have hset : (Ico t (next k I t)).filter (fun u => cin ℓ (u + 1) E = 1) =
      Ico t (t + min L (h k I t)) := by
    ext u; simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [show u + 1 = t + (u + 1 - t) by omega,
        cin_window hI hE ht (by omega) (by rw [h_eq]; omega), le_runLen_iff he (by omega)] at h3
      rw [h_eq]; omega
    · rintro ⟨h1, h2⟩
      rw [h_eq] at h2
      refine ⟨⟨h1, by omega⟩, ?_⟩
      rw [show u + 1 = t + (u + 1 - t) by omega,
        cin_window hI hE ht (by omega) (by rw [h_eq]; omega), le_runLen_iff he (by omega)]
      omega
  unfold car
  rw [hset, Nat.card_Ico]
  omega

/-- The case analysis behind (B2) and (B3). -/
lemma car_cases (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    car I k ℓ t E =
      if (typ ℓ t = 1 ∧ (t ∈ E ∨ cin ℓ t E = 1)) ∨ (typ ℓ t = 0 ∧ t ∈ E ∧ cin ℓ t E = 1)
      then kap I k ℓ t else 0 := by
  rw [car_eq_min hI hE ht]
  have h1 := one_le_h hI ht
  have hr2 : r (t + 1) ℓ = v2 (ℓ / 2 ^ t / 2 + 1) := by
    unfold r; rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hT : typ ℓ t = ℓ / 2 ^ t % 2 := rfl
  have hr1 : r t ℓ = v2 (ℓ / 2 ^ t + 1) := rfl
  unfold kap runLen
  rw [hT, hr1, hr2]
  rcases Nat.mod_two_eq_zero_or_one (ℓ / 2 ^ t) with hq | hq
  · have hv := v2_succ_of_even hq
    by_cases htE : t ∈ E <;> rcases cin_le_one (ℓ := ℓ) t E with hc | hc
    all_goals simp [hq, htE, hc, hv]
    all_goals omega
  · have hv := v2_succ_of_odd hq
    by_cases htE : t ∈ E <;> rcases cin_le_one (ℓ := ℓ) t E with hc | hc <;>
      simp [hq, htE, hc, hv]

/-- **(B1)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: if `I ≠ ∅`, then
`c_{min I}(E) = 0` for `E ⊆ I`.  (More general than the file: neither `I ⊆ {0, …, k − 1}` nor
`ℓ < 2^k` is needed.) -/
theorem lemma_B1 (hne : I.Nonempty) {E : Finset ℕ} (hE : E ⊆ I) : cin ℓ (I.min' hne) E = 0 := by
  unfold cin
  rw [if_neg]
  rw [oE_mod, show E.filter (· < I.min' hne) = ∅ from ?_, oE_empty]
  · have := Nat.mod_lt ℓ (Nat.two_pow_pos (I.min' hne)); omega
  · rw [filter_eq_empty_iff]; intro x hx; exact not_lt.2 (min'_le I x (hE hx))

/-- **(B2)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: for `E ⊆ I`, `t ∈ I` and
`d = [t ∈ E]`, if `T_t = 1` then `car_t(E) = κ_t` if `d = 1` or `c_t(E) = 1`, and `car_t(E) = 0`
otherwise.  (More general than the file: `ℓ < 2^k` is not needed.) -/
theorem lemma_B2 (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I)
    (hT : typ ℓ t = 1) :
    car I k ℓ t E = if t ∈ E ∨ cin ℓ t E = 1 then kap I k ℓ t else 0 := by
  rw [car_cases hI hE ht]; simp [hT]

/-- **(B3)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: for `E ⊆ I`, `t ∈ I` and
`d = [t ∈ E]`, if `T_t = 0` then `car_t(E) = κ_t` if `d = 1` and `c_t(E) = 1`, and `car_t(E) = 0`
otherwise.  (More general than the file: `ℓ < 2^k` is not needed.) -/
theorem lemma_B3 (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I)
    (hT : typ ℓ t = 0) :
    car I k ℓ t E = if t ∈ E ∧ cin ℓ t E = 1 then kap I k ℓ t else 0 := by
  rw [car_cases hI hE ht]; simp [hT]

/-- **(B4)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: for `E ⊆ I` and `t ∈ I`,
`c_{next(t)}(E) = 1` if and only if `car_t(E) > 0` and `sat_t = 1`.  (More general than the
file: `ℓ < 2^k` is not needed.) -/
theorem lemma_B4 (hI : ∀ t ∈ I, t < k) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    cin ℓ (next k I t) E = 1 ↔ 0 < car I k ℓ t E ∧ sat I k ℓ t = 1 := by
  have hn := next_spec hI ht
  have h1 := one_le_h hI ht
  have he : cin ℓ t E + (if t ∈ E then 1 else 0) ≤ 2 := by
    rcases cin_le_one (ℓ := ℓ) t E with h | h <;> rw [h] <;> split_ifs <;> omega
  have hcc := car_cases (ℓ := ℓ) hI hE ht
  have hmin := car_eq_min (ℓ := ℓ) hI hE ht
  rw [show next k I t = t + h k I t by rw [h_eq]; omega, cin_window hI hE ht h1 le_rfl,
    le_runLen_iff he h1]
  unfold sat
  generalize runLen (cin ℓ t E + if t ∈ E then 1 else 0) (ℓ / 2 ^ t) = L at hmin ⊢
  generalize car I k ℓ t E = C at hcc hmin ⊢
  generalize h k I t = H at h1 hmin ⊢
  split_ifs at hcc with hcond <;> split_ifs <;> constructor <;> intro hh
  all_goals (simp only [and_true, and_false] at * <;> omega)

/-- The total number of carries of `ℓ + o_E` is the sum of the carries made by the windows. -/
lemma kappa_eq_sum_car (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) {E : Finset ℕ} (hE : E ⊆ I) :
    kappa ℓ (oE E) = ∑ t ∈ I, (car I k ℓ t E : ℤ) := by
  have hx := oE_lt E k (fun t ht => hI t (hE ht))
  rw [kappa_eq_sum ℓ (oE E) (k + 1) (by rw [pow_succ]; omega)]
  change ∑ u ∈ range (k + 1), ((cin ℓ (u + 1) E : ℕ) : ℤ) = _
  have hcar : ∀ t ∈ I, (car I k ℓ t E : ℤ) =
      ∑ u ∈ Ico t (next k I t), ((cin ℓ (u + 1) E : ℕ) : ℤ) := by
    intro t _; unfold car; rw [card_filter]; push_cast
    apply sum_congr rfl; intro u _
    rcases cin_le_one (ℓ := ℓ) (u + 1) E with h | h <;> simp [h]
  have hpair : (I : Set ℕ).PairwiseDisjoint (fun t => Ico t (next k I t)) := by
    intro t ht t' ht' hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    simp only [mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := next_le_of_mem (k := k) (I := I) ht' hlt; omega
    · have := next_le_of_mem (k := k) (I := I) ht hlt; omega
  rw [sum_congr rfl hcar, ← sum_biUnion hpair]
  symm
  apply sum_subset
  · intro u hu
    obtain ⟨t, ht, hut⟩ := mem_biUnion.1 hu
    have := next_spec hI ht
    simp only [mem_Ico] at hut; simp only [mem_range]; omega
  · intro u hu hnot
    simp only [mem_range] at hu
    by_cases huk : u < k
    · by_cases hex : ∃ s ∈ I, s ≤ u
      · exfalso; apply hnot
        have hne : (I.filter (· ≤ u)).Nonempty := by
          obtain ⟨s, hs, hsu⟩ := hex; exact ⟨s, mem_filter.2 ⟨hs, hsu⟩⟩
        set t := (I.filter (· ≤ u)).max' hne
        have htm := mem_filter.1 (max'_mem _ hne)
        refine mem_biUnion.2 ⟨t, htm.1, mem_Ico.2 ⟨htm.2, ?_⟩⟩
        by_contra hc; push_neg at hc
        have hmem : next k I t ∈ (insert k I).filter (fun v => t < v) :=
          minOr_mem ⟨k, by simp [hI t htm.1]⟩
        simp only [mem_filter, mem_insert] at hmem
        rcases hmem.1 with h' | h'
        · omega
        · have := le_max' (I.filter (· ≤ u)) (next k I t) (mem_filter.2 ⟨h', hc⟩)
          omega
      · push_neg at hex
        have h0 : oE E % 2 ^ (u + 1) = 0 := by
          rw [oE_mod, show E.filter (· < u + 1) = ∅ from ?_, oE_empty]
          rw [filter_eq_empty_iff]; intro x hx; have := hex x (hE hx); omega
        have := Nat.mod_lt ℓ (Nat.two_pow_pos (u + 1))
        simp [cin, h0]; omega
    · have hu' : u = k := by omega
      subst hu'
      have h1 := Nat.mod_le ℓ (2 ^ (u + 1))
      have h2 := Nat.mod_le (oE E) (2 ^ (u + 1))
      have h3 : 2 ^ (u + 1) = 2 * 2 ^ u := by rw [pow_succ]; ring
      simp only [cin]; rw [if_neg (by omega)]; simp

/-- **(B5)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: for `E ⊆ I`,
`R_H(E) = Σ_{t∈E} τ_t − Σ_{t∈I} κ_t · c_t(E) · [(T_t = 1 ∧ t ∉ E) ∨ (T_t = 0 ∧ t ∈ E)]`. -/
theorem lemma_B5 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) {E : Finset ℕ} (hE : E ⊆ I) :
    RH I k ℓ α E = ∑ t ∈ E, tau I k ℓ α t
      - ∑ t ∈ I, (kap I k ℓ t : ℤ) * (cin ℓ t E : ℤ) *
          (if (typ ℓ t = 1 ∧ t ∉ E) ∨ (typ ℓ t = 0 ∧ t ∈ E) then 1 else 0) := by
  unfold RH ruler
  rw [kappa_eq_sum_car hI hℓ hE]
  have hpt : ∀ t ∈ I, (car I k ℓ t E : ℤ) =
      (if t ∈ E then (if typ ℓ t = 1 then (kap I k ℓ t : ℤ) else 0) else 0) +
      (kap I k ℓ t : ℤ) * (cin ℓ t E : ℤ) *
          (if (typ ℓ t = 1 ∧ t ∉ E) ∨ (typ ℓ t = 0 ∧ t ∈ E) then 1 else 0) := by
    intro t ht
    rw [car_cases hI hE ht]
    by_cases htE : t ∈ E <;> rcases cin_le_one (ℓ := ℓ) t E with hc | hc <;>
      rcases typ_le_one (ℓ := ℓ) t with hT | hT <;> simp [htE, hc, hT]
  rw [sum_congr rfl hpt, sum_add_distrib, sum_ite_mem, inter_eq_right.2 hE]
  unfold tau
  simp only [sum_sub_distrib]
  ring

/-- **(B6)** of Lemma B (Lemma 7.6), `C6_houses_windows_penalties.md`: for `E ⊆ I`,
`J_H(E) = c_k(E)`. -/
theorem lemma_B6 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) {E : Finset ℕ} (hE : E ⊆ I) :
    JH k ℓ E = cin ℓ k E := by
  unfold JH cin
  rw [Nat.mod_eq_of_lt hℓ, Nat.mod_eq_of_lt (oE_lt E k (fun t ht => hI t (hE ht)))]

end Houses
