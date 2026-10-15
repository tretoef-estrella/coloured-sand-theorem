module

public import RequestProject.OddHouses.Basic

/-!
# `CSI15_houses_at_p.md` — **Part B**: windows and gates (Lemma 7.6_p)

Namespace `ColouredSand.OddTwist`; encodings as in `RequestProject/OddHouses/Basic.lean`: the
house `H = (I, k, ℓ, e, d)` is given by its components; the window of `t ∈ I` is
`W_t = Finset.Ico t (Rulers.next k I t)`; `ℓ_t = digP p t ℓ`, `θ_t = thetaP p ℓ t`,
`κ_t = kapP p k I ℓ t`, `sat_t = satP p k I ℓ t`, the type is `typP p dg ℓ t : WinTypeP`,
`τ_t = tauP p k I dg ℓ e t`, `c_u(E) = cinP p dg ℓ u E`, `car_t(E) = carP p k I dg ℓ t E`.
The indicator `δ := [t ∈ E]` of the file is used through `t ∈ E` (`δ = 1 ↔ t ∈ E`), or as
`if t ∈ E then 1 else 0` where it is a number.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

variable {p : ℕ} [hp : Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ}

omit hp in
lemma cinP_le_one (u : ℕ) (E : Finset ℕ) : cinP p dg ℓ u E = 0 ∨ cinP p dg ℓ u E = 1 := by
  unfold cinP; split_ifs <;> simp

omit hp in
lemma digit_lt_of_mem (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (h2 : 2 ≤ p) {E : Finset ℕ}
    (hE : E ⊆ I) : ∀ t ∈ E, dg t < p :=
  fun t ht => by have := hd t (hE ht); omega

/-- Inside the window of `t`, the addend `o_E` has at most the digit `δ d_t`, at `t`. -/
lemma oW_mod_window (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ} (hE : E ⊆ I)
    {t u : ℕ} (htu : t < u) (hun : u ≤ Rulers.next k I t) :
    oW p dg E % p ^ u = oW p dg E % p ^ t + (if t ∈ E then dg t else 0) * p ^ t := by
  have hdE := digit_lt_of_mem hd oddHou_two_le_p hE
  rw [oW_mod dg E hdE, oW_mod dg E hdE]
  have hf : E.filter (· < u) = E.filter (· < t + 1) := by
    ext s; simp only [mem_filter]; constructor
    · rintro ⟨hs, hsu⟩; refine ⟨hs, ?_⟩; by_contra hc
      have := Rulers.next_le_of_mem (k := k) (hE hs) (show t < s by omega); omega
    · rintro ⟨hs, hst⟩; exact ⟨hs, by omega⟩
  rw [hf]; simp only [oW, sum_filter]
  rw [show (∑ s ∈ E, if s < t + 1 then dg s * p ^ s else 0) =
      ∑ s ∈ E, ((if s < t then dg s * p ^ s else 0) + (if t = s then dg s * p ^ s else 0)) from
    sum_congr rfl (fun s _ => by split_ifs <;> omega)]
  rw [sum_add_distrib, sum_ite_eq]
  split_ifs <;> simp

/-- The carry into digit `t + j` inside the window of `t` (`1 ≤ j ≤ h_t`). -/
lemma cinP_window (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ}
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : t + j ≤ Rulers.next k I t) :
    cinP p dg ℓ (t + j) E = 1 ↔
      p ^ j ≤ (cinP p dg ℓ t E + (if t ∈ E then dg t else 0)) + ℓ / p ^ t % p ^ j := by
  have hpt : 0 < p ^ t := pow_pos hp.out.pos t
  have hw := oW_mod_window (k := k) hd hE (t := t) (u := t + j) (by omega) hjn
  have hl : ℓ % p ^ (t + j) = ℓ % p ^ t + p ^ t * (ℓ / p ^ t % p ^ j) := by
    rw [pow_add, Nat.mod_mul]
  have hX : ℓ % p ^ t + oW p dg E % p ^ t < 2 * p ^ t := by
    have := Nat.mod_lt ℓ hpt
    have := Nat.mod_lt (oW p dg E) hpt
    omega
  have key := Houses.carry_aux (M := p ^ j)
    (Y := (if t ∈ E then dg t else 0) + ℓ / p ^ t % p ^ j) hX
  have hsum : ℓ % p ^ t + p ^ t * (ℓ / p ^ t % p ^ j) +
      (oW p dg E % p ^ t + (if t ∈ E then dg t else 0) * p ^ t) =
      ℓ % p ^ t + oW p dg E % p ^ t +
        p ^ t * ((if t ∈ E then dg t else 0) + ℓ / p ^ t % p ^ j) := by
    ring
  have hc : cinP p dg ℓ (t + j) E = 1 ↔
      p ^ (t + j) ≤ ℓ % p ^ (t + j) + oW p dg E % p ^ (t + j) := by
    unfold cinP; split_ifs with h <;> simp [h]
  rw [hc, hl, hw, hsum, pow_add, key, add_assoc]
  rfl

/-- The run of carries started by `n ≤ p` incoming units on `Q`. -/
lemma le_run_iff {n Q j : ℕ} (hn : n ≤ p) (hj : 1 ≤ j) :
    p ^ j ≤ n + Q % p ^ j ↔ p ≤ Q % p + n ∧ j - 1 ≤ padicValNat p (Q / p + 1) := by
  have h2 := oddHou_two_le_p (p := p)
  have hph : p ^ j = p * p ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have hm : Q % p ^ j = Q % p + p * (Q / p % p ^ (j - 1)) := by rw [hph, Nat.mod_mul]
  have hlt := Nat.mod_lt Q (show 0 < p by omega)
  have hY := Nat.mod_lt (Q / p) (pow_pos (show 0 < p by omega) (j - 1))
  have key := Houses.carry_aux (P := p) (M := p ^ (j - 1)) (X := Q % p + n)
    (Y := Q / p % p ^ (j - 1)) (by omega)
  have hv := le_vP_iff (p := p) (Q / p) (j - 1)
  rw [hm, show n + (Q % p + p * (Q / p % p ^ (j - 1))) = Q % p + n + p * (Q / p % p ^ (j - 1))
    by ring, hph, key, hv]
  split_ifs <;> constructor <;> intro hh <;> omega

/-- `car_t(E) = κ_t` if `p ≤ ℓ_t + c_t(E) + δ d_t`, and `0` otherwise. -/
lemma carP_eq (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ}
    (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    carP p k I dg ℓ t E =
      if p ≤ digP p t ℓ + (cinP p dg ℓ t E + (if t ∈ E then dg t else 0))
      then kapP p k I ℓ t else 0 := by
  have hn := Rulers.next_spec hI ht
  have hh : Rulers.h k I t = Rulers.next k I t - t := rfl
  have hnp : cinP p dg ℓ t E + (if t ∈ E then dg t else 0) ≤ p := by
    have := hd t ht
    rcases cinP_le_one (p := p) (dg := dg) (ℓ := ℓ) t E with h | h <;> rw [h] <;>
      split_ifs <;> omega
  set n := cinP p dg ℓ t E + (if t ∈ E then dg t else 0) with hn_def
  set v := padicValNat p (ℓ / p ^ t / p + 1)
  set M : ℕ := if p ≤ digP p t ℓ + n then 1 + min v (Rulers.h k I t - 1) else 0 with hM
  have hset : (Ico t (Rulers.next k I t)).filter (fun u => cinP p dg ℓ (u + 1) E = 1) =
      Ico t (t + M) := by
    ext u; simp only [mem_filter, mem_Ico]
    have hiff : ∀ u, t ≤ u → u < Rulers.next k I t →
        (cinP p dg ℓ (u + 1) E = 1 ↔ p ≤ digP p t ℓ + n ∧ u - t ≤ v) := by
      intro u h1 h2
      rw [show u + 1 = t + (u + 1 - t) by omega, cinP_window (k := k) hd hE (by omega) (by omega),
        le_run_iff hnp (by omega)]
      unfold digP
      constructor
      · rintro ⟨a, b⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨a, b⟩; exact ⟨by omega, by omega⟩
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [hiff u h1 h2] at h3
      rw [hM, if_pos h3.1]; omega
    · rintro ⟨h1, h2⟩
      rw [hM] at h2
      split_ifs at h2 with hF
      · refine ⟨⟨h1, by omega⟩, ?_⟩
        rw [hiff u h1 (by omega)]; exact ⟨hF, by omega⟩
      · omega
  unfold carP
  rw [hset, Nat.card_Ico, Nat.add_sub_cancel_left, hM]
  unfold kapP
  rw [rP_succ]

/-- The firing condition in arithmetic form: the window fires iff `p ≤ ℓ_t + c_t(E) + δ d_t`. -/
lemma firesP_iff_arith (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ} {t : ℕ}
    (ht : t ∈ I) :
    firesP p dg ℓ t E ↔
      p ≤ digP p t ℓ + (cinP p dg ℓ t E + (if t ∈ E then dg t else 0)) := by
  have hdt := hd t ht
  have hlt : digP p t ℓ < p := Nat.mod_lt _ hp.out.pos
  unfold firesP typP thetaP
  rcases cinP_le_one (p := p) (dg := dg) (ℓ := ℓ) t E with hc | hc <;> rw [hc] <;>
    by_cases htE : t ∈ E <;> simp only [htE, if_true, if_false] <;>
    split_ifs <;> simp <;> omega

/-- **(B1)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): if `I ≠ ∅`, then
`c_{min I}(E) = 0` for `E ⊆ I`.  (More general than the file: neither `I ⊆ {0, …, k − 1}` nor
`ℓ < p^k` is needed.) -/
theorem houseP_B1 (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hne : I.Nonempty) {E : Finset ℕ}
    (hE : E ⊆ I) : cinP p dg ℓ (I.min' hne) E = 0 := by
  unfold cinP
  rw [if_neg]
  rw [oW_mod dg E (digit_lt_of_mem hd oddHou_two_le_p hE), show E.filter (· < I.min' hne) = ∅ from ?_]
  · have := Nat.mod_lt ℓ (pow_pos hp.out.pos (I.min' hne)); simp [oW]; omega
  · rw [filter_eq_empty_iff]; intro x hx; exact not_lt.2 (min'_le I x (hE hx))

open Classical in
/-- **(B2)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): for `E ⊆ I` and `t ∈ I`,
`car_t(E) = κ_t` if the window of `t` fires (OR: `δ = 1 ∨ c_t(E) = 1`; DIG: `δ = 1`;
AND: `δ = 1 ∧ c_t(E) = 1`; NEV: never — the definition `firesP`), and `0` otherwise.
(More general than the file: `ℓ < p^k` is not needed.) -/
theorem houseP_B2 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ}
    (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    carP p k I dg ℓ t E = if firesP p dg ℓ t E then kapP p k I ℓ t else 0 := by
  rw [carP_eq hI hd hE ht]
  by_cases hF : firesP p dg ℓ t E
  · rw [if_pos hF, if_pos ((firesP_iff_arith hd ht).1 hF)]
  · rw [if_neg hF, if_neg (fun h => hF ((firesP_iff_arith hd ht).2 h))]

/-- **(B2)**, the equivalent form, of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): the window
of `t ∈ I` fires iff `δ·d_t + c_t(E) ≥ θ_t`, with `δ = [t ∈ E]`. -/
theorem houseP_B2_fires_iff (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ} {t : ℕ}
    (ht : t ∈ I) :
    firesP p dg ℓ t E ↔ thetaP p ℓ t ≤ (if t ∈ E then 1 else 0) * dg t + cinP p dg ℓ t E := by
  rw [firesP_iff_arith hd ht]
  have hlt : digP p t ℓ < p := Nat.mod_lt _ hp.out.pos
  unfold thetaP
  by_cases htE : t ∈ E <;> simp only [htE, if_true, if_false] <;> omega

/-- **(B3)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): for `E ⊆ I` and `t ∈ I`,
`c_{next(t)}(E) = 1 ↔ car_t(E) > 0 ∧ sat_t = 1`.  (More general than the file: `ℓ < p^k` is not
needed.) -/
theorem houseP_B3 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {E : Finset ℕ}
    (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    cinP p dg ℓ (Rulers.next k I t) E = 1 ↔ 0 < carP p k I dg ℓ t E ∧ satP p k I ℓ t = 1 := by
  have hn := Rulers.next_spec hI ht
  have h1 := Rulers.one_le_h hI ht
  have hh : Rulers.h k I t = Rulers.next k I t - t := rfl
  have hnp : cinP p dg ℓ t E + (if t ∈ E then dg t else 0) ≤ p := by
    have := hd t ht
    rcases cinP_le_one (p := p) (dg := dg) (ℓ := ℓ) t E with h | h <;> rw [h] <;>
      split_ifs <;> omega
  rw [show Rulers.next k I t = t + Rulers.h k I t by omega,
    cinP_window (k := k) hd hE h1 (by omega), le_run_iff hnp h1, carP_eq hI hd hE ht]
  unfold satP kapP digP
  rw [rP_succ]
  obtain ⟨H, hH⟩ : ∃ H, Rulers.h k I t = H + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  rw [hH, Nat.add_sub_cancel]
  generalize (cinP p dg ℓ t E + if t ∈ E then dg t else 0) = n at hnp ⊢
  generalize padicValNat p (ℓ / p ^ t / p + 1) = v
  have e1 : (0 < if p ≤ ℓ / p ^ t % p + n then 1 + min v H else 0) ↔ p ≤ ℓ / p ^ t % p + n := by
    split_ifs with h <;> simp [h]
  have e2 : ((if 1 + min v H = H + 1 then 1 else 0) = 1) ↔ H ≤ v := by
    rw [min_def]; split_ifs <;> simp <;> omega
  rw [e1, e2]

/-- **(B4)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): for `E ⊆ I`, the total number of
carries of `ℓ + o_E` is the sum of the carries made by the windows:
`κ_p(ℓ, o_E) = Σ_{t∈I} car_t(E)`. -/
theorem houseP_B4 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) {E : Finset ℕ} (hE : E ⊆ I) :
    kappaP p ℓ (oW p dg E) = ∑ t ∈ I, (carP p k I dg ℓ t E : ℤ) := by
  have h2 := oddHou_two_le_p (p := p)
  have hdE := digit_lt_of_mem hd h2 hE
  have hx : oW p dg E < p ^ k := oW_lt_pow h2 dg E (fun t ht => hI t (hE ht)) hdE
  have hpk : p ^ (k + 1) = p * p ^ k := by rw [pow_succ']
  have hk2 : 2 * p ^ k ≤ p ^ (k + 1) := by rw [hpk]; exact Nat.mul_le_mul_right _ h2
  rw [kappaP_eq_sum ℓ (oW p dg E) (k + 1) (by omega)]
  change ∑ u ∈ range (k + 1), ((cinP p dg ℓ (u + 1) E : ℕ) : ℤ) = _
  have hcar : ∀ t ∈ I, (carP p k I dg ℓ t E : ℤ) =
      ∑ u ∈ Ico t (Rulers.next k I t), ((cinP p dg ℓ (u + 1) E : ℕ) : ℤ) := by
    intro t _; unfold carP; rw [card_filter]; push_cast
    apply sum_congr rfl; intro u _
    rcases cinP_le_one (p := p) (dg := dg) (ℓ := ℓ) (u + 1) E with h | h <;> simp [h]
  have hpair : (I : Set ℕ).PairwiseDisjoint (fun t => Ico t (Rulers.next k I t)) := by
    intro t ht t' ht' hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    simp only [mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := Rulers.next_le_of_mem (k := k) (I := I) ht' hlt; omega
    · have := Rulers.next_le_of_mem (k := k) (I := I) ht hlt; omega
  rw [sum_congr rfl hcar, ← sum_biUnion hpair]
  symm
  apply sum_subset
  · intro u hu
    obtain ⟨t, ht, hut⟩ := mem_biUnion.1 hu
    have := Rulers.next_spec hI ht
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
        have hmem : Rulers.next k I t ∈ (insert k I).filter (fun v => t < v) :=
          Rulers.minOr_mem ⟨k, by simp [hI t htm.1]⟩
        simp only [mem_filter, mem_insert] at hmem
        rcases hmem.1 with h' | h'
        · omega
        · have := le_max' (I.filter (· ≤ u)) (Rulers.next k I t) (mem_filter.2 ⟨h', hc⟩)
          omega
      · push_neg at hex
        have h0 : oW p dg E % p ^ (u + 1) = 0 := by
          rw [oW_mod dg E hdE, show E.filter (· < u + 1) = ∅ from ?_]
          · simp [oW]
          rw [filter_eq_empty_iff]; intro x hx; have := hex x (hE hx); omega
        have := Nat.mod_lt ℓ (pow_pos (show 0 < p by omega) (u + 1))
        simp [cinP, h0]; omega
    · have hu' : u = k := by omega
      subst hu'
      have h1 := Nat.mod_le ℓ (p ^ (u + 1))
      have h3 := Nat.mod_le (oW p dg E) (p ^ (u + 1))
      simp only [cinP]; rw [if_neg (by omega)]; simp

open Classical in
/-- **(B5)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): for `E ⊆ I`,
`R_H(E) = Σ_{t∈E} τ_t − Σ_{t∈I} κ_t·c_t(E)·[(type t = OR ∧ t ∉ E) ∨ (type t = AND ∧ t ∈ E)]`. -/
theorem houseP_B5 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) {E : Finset ℕ} (hE : E ⊆ I) :
    RHP p k I dg ℓ e E = ∑ t ∈ E, tauP p k I dg ℓ e t
      - ∑ t ∈ I, (kapP p k I ℓ t : ℤ) * (cinP p dg ℓ t E : ℤ) *
          (if (typP p dg ℓ t = .OR ∧ t ∉ E) ∨ (typP p dg ℓ t = .AND ∧ t ∈ E) then 1 else 0) := by
  unfold RHP
  rw [houseP_B4 hI hd hℓ hE]
  have hpt : ∀ t ∈ I, (carP p k I dg ℓ t E : ℤ) =
      (if t ∈ E then
        (if typP p dg ℓ t = .OR ∨ typP p dg ℓ t = .DIG then (kapP p k I ℓ t : ℤ) else 0)
        else 0) +
      (kapP p k I ℓ t : ℤ) * (cinP p dg ℓ t E : ℤ) *
          (if (typP p dg ℓ t = .OR ∧ t ∉ E) ∨ (typP p dg ℓ t = .AND ∧ t ∈ E) then 1 else 0) := by
    intro t ht
    rw [houseP_B2 hI hd hE ht]
    unfold firesP
    cases hT : typP p dg ℓ t <;>
      rcases cinP_le_one (p := p) (dg := dg) (ℓ := ℓ) t E with hc | hc <;>
      by_cases htE : t ∈ E <;> simp [hc, htE]
  rw [sum_congr rfl hpt, sum_add_distrib, sum_ite_mem, inter_eq_right.2 hE]
  unfold tauP
  simp only [sum_sub_distrib]
  ring

/-- **(B6)** of `CSI15_houses_at_p.md` (Part B, Lemma 7.6_p): for `E ⊆ I`, `J_H(E) = c_k(E)`. -/
theorem houseP_B6 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) {E : Finset ℕ} (hE : E ⊆ I) :
    JHP p k dg ℓ E = cinP p dg ℓ k E := by
  unfold JHP cinP
  rw [Nat.mod_eq_of_lt hℓ, Nat.mod_eq_of_lt (oW_lt_pow oddHou_two_le_p dg E (fun t ht => hI t (hE ht))
    (digit_lt_of_mem hd oddHou_two_le_p hE))]

end ColouredSand.OddTwist
