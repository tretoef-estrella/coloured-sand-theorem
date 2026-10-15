module

public import RequestProject.OddWindows.Basic
public import RequestProject.GoldenMatching.All

/-!
# Part A of `CSI14_the_ceiling_at_p.md`: the o-order with base-p digits

## Encoding

* The prime (or, here, any integer) `p ≥ 2` is `p : ℕ`; the digits are a function `d : ℕ → ℕ`
  with `1 ≤ d t ≤ p − 1` for `t ∈ I` (hypothesis `hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1`).
* The finite set `I` is `I : Finset ℕ`; the dancers are the subsets `D ⊆ I`.
* The base-p order `oP p d E = Σ_{t∈E} d t · p^t` is **CSI12's `oW p d E`**, reused; the
  name `oP` is an abbreviation for `oW`, with the `rfl` lemma `oP_eq_oW`.
* The binary order is C3's `Rulers.oE`; ranks, `L_r`, `F_r`, golden arrows and Theorem O are
  C4's `GoldenMatching.rank`, `GoldenMatching.Lr`, `GoldenMatching.Fr`,
  `GoldenMatching.IsGoldenArrow`, `GoldenMatching.theorem_B`.
* The base-p rank and the base-p sets of last / first `r` dancers are `rankP`, `LrP`, `FrP`
  (defined exactly as C4's, with `oW p d` instead of `oE`); (A2) proves they coincide with C4's.

The hypothesis `I ⊆ {0, …, k − 1}` of the setting is not needed for (A1)–(A3) (more general),
and `p` need not be prime there; `I ⊆ {0, …, k − 1}` is only used through
`GoldenMatching.theorem_B` in `theorem_O_P`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- *Part A, Setting* of `CSI14_the_ceiling_at_p.md`: `oP p d E := Σ_{t∈E} d t · p^t`; this is
CSI12's `oW`. -/
abbrev oP (p : ℕ) (d : ℕ → ℕ) (E : Finset ℕ) : ℕ := oW p d E

/-- *Part A, Setting* of `CSI14_the_ceiling_at_p.md`: `oP = oW` (by definition). -/
theorem oP_eq_oW (p : ℕ) (d : ℕ → ℕ) (E : Finset ℕ) : oP p d E = oW p d E := rfl

/-- A weighted subset sum is decided by the colexicographic order as soon as every weight
dominates the sum of the smaller weights of `I`. (Auxiliary for (A1) of
`CSI14_the_ceiling_at_p.md`: "both orders are decided at the largest element of the symmetric
difference".) -/
theorem sum_lt_of_colex (w : ℕ → ℕ) {I : Finset ℕ}
    (hw : ∀ t ∈ I, ∑ s ∈ I.filter (· < t), w s < w t) {D D' : Finset ℕ} (hD : D ⊆ I)
    (hD' : D' ⊆ I) (h : toColex D < toColex D') : ∑ s ∈ D, w s < ∑ s ∈ D', w s := by
  obtain ⟨k, hkD', hkD, hlt⟩ := Colex.toColex_lt_toColex_iff_exists_forall_lt.1 h
  have hsplit : ∀ E : Finset ℕ, ∑ s ∈ E, w s =
      ∑ s ∈ E.filter (fun s => k < s), w s + ∑ s ∈ E.filter (fun s => ¬ k < s), w s :=
    fun E => (sum_filter_add_sum_filter_not E _ _).symm
  rw [hsplit D, hsplit D']
  have h1 : ∑ s ∈ D.filter (fun s => k < s), w s ≤ ∑ s ∈ D'.filter (fun s => k < s), w s := by
    apply sum_le_sum_of_subset
    intro s hs
    simp only [mem_filter] at hs ⊢
    refine ⟨?_, hs.2⟩
    by_contra hns
    exact absurd (hlt s hs.1 hns) (not_lt.2 hs.2.le)
  have h2 : ∑ s ∈ D.filter (fun s => ¬ k < s), w s ≤ ∑ s ∈ I.filter (· < k), w s := by
    apply sum_le_sum_of_subset
    intro s hs
    simp only [mem_filter, not_lt] at hs ⊢
    refine ⟨hD hs.1, lt_of_le_of_ne hs.2 ?_⟩
    rintro rfl; exact hkD hs.1
  have h3 : w k ≤ ∑ s ∈ D'.filter (fun s => ¬ k < s), w s :=
    single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (by simp [hkD'])
  have h4 := hw k (hD' hkD')
  omega

/-- A weighted subset sum on subsets of `I` induces the colexicographic order, when every
weight dominates the sum of the smaller weights. (Auxiliary for (A1) of
`CSI14_the_ceiling_at_p.md`.) -/
theorem sum_lt_iff_colex (w : ℕ → ℕ) {I : Finset ℕ}
    (hw : ∀ t ∈ I, ∑ s ∈ I.filter (· < t), w s < w t) {D D' : Finset ℕ} (hD : D ⊆ I)
    (hD' : D' ⊆ I) : ∑ s ∈ D, w s < ∑ s ∈ D', w s ↔ toColex D < toColex D' := by
  refine ⟨fun h => ?_, sum_lt_of_colex w hw hD hD'⟩
  rcases lt_trichotomy (toColex D) (toColex D') with h' | h' | h'
  · exact h'
  · simp only [toColex_inj] at h'; subst h'; exact absurd h (lt_irrefl _)
  · exact absurd (sum_lt_of_colex w hw hD' hD h') (not_lt.2 h.le)

/-- `Σ_{s<t} (p − 1) p^s < p^t`. (Auxiliary for (A1) of `CSI14_the_ceiling_at_p.md`.) -/
theorem sum_range_digit_lt {p : ℕ} (hp : 2 ≤ p) (t : ℕ) :
    ∑ s ∈ range t, (p - 1) * p ^ s < p ^ t := by
  have : ∀ t, ∑ s ∈ range t, (p - 1) * p ^ s + 1 = p ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [sum_range_succ, add_right_comm, ih, pow_succ]
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
  have := this t
  omega

/-- The base-`p` digit weights `d t · p^t` dominate the sums of the smaller weights of `I`.
(Proof of (A1) of `CSI14_the_ceiling_at_p.md`.) -/
theorem digit_weight_dominates {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) :
    ∀ t ∈ I, ∑ s ∈ I.filter (· < t), d s * p ^ s < d t * p ^ t := by
  intro t ht
  calc ∑ s ∈ I.filter (· < t), d s * p ^ s ≤ ∑ s ∈ I.filter (· < t), (p - 1) * p ^ s :=
        sum_le_sum fun s hs => Nat.mul_le_mul_right _ (hd s (mem_filter.1 hs).1).2
    _ ≤ ∑ s ∈ range t, (p - 1) * p ^ s :=
        sum_le_sum_of_subset (fun s hs => by simpa using (mem_filter.1 hs).2)
    _ < p ^ t := sum_range_digit_lt hp t
    _ ≤ d t * p ^ t := Nat.le_mul_of_pos_left _ (hd t ht).1

/-- The base-`p` order of subsets of `I` is the colexicographic order. (Proof of (A1) of
`CSI14_the_ceiling_at_p.md`.) -/
theorem oP_lt_iff_colex {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I) :
    oP p d D < oP p d D' ↔ toColex D < toColex D' :=
  sum_lt_iff_colex (fun t => d t * p ^ t) (digit_weight_dominates hp hd) hD hD'

/-- **(A1)** (the same order) of `CSI14_the_ceiling_at_p.md`: for `p ≥ 2`, digits
`1 ≤ d t ≤ p − 1` on `I` and `D, D' ⊆ I`, `oP p d D < oP p d D' ↔ Rulers.oE D < Rulers.oE D'`.
(More general than stated: `I ⊆ {0, …, k−1}` is not needed and `p` need not be prime.) -/
theorem A1_same_order {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I) :
    oP p d D < oP p d D' ↔ Rulers.oE D < Rulers.oE D' := by
  rw [oP_lt_iff_colex hp hd hD hD', Rulers.oE, Rulers.oE,
    geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl]

/-- *Part A, (A2)* of `CSI14_the_ceiling_at_p.md`: the base-`p` rank
`#{D' ⊆ I : oP p d D' < oP p d D}`. -/
def rankP (p : ℕ) (d : ℕ → ℕ) (I D : Finset ℕ) : ℕ :=
  #(I.powerset.filter (fun D' => oP p d D' < oP p d D))

/-- *Part A, (A2)* of `CSI14_the_ceiling_at_p.md`: the last `r` dancers in the base-`p` order,
`{D ⊆ I : rankP(D) ≥ 2^{|I|} − r}`. -/
def LrP (p : ℕ) (d : ℕ → ℕ) (I : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun D => 2 ^ #I - r ≤ rankP p d I D)

/-- *Part A, (A2)* of `CSI14_the_ceiling_at_p.md`: the first `r` dancers in the base-`p` order,
`{D ⊆ I : rankP(D) < r}`. -/
def FrP (p : ℕ) (d : ℕ → ℕ) (I : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun D => rankP p d I D < r)

/-- **(A2)** (ranks) of `CSI14_the_ceiling_at_p.md`: for `D ⊆ I`,
`#{D' ⊆ I : oP p d D' < oP p d D} = GoldenMatching.rank I D`. -/
theorem A2_rank {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) {D : Finset ℕ} (hD : D ⊆ I) :
    rankP p d I D = GoldenMatching.rank I D := by
  unfold rankP GoldenMatching.rank
  congr 1
  exact filter_congr fun D' hD' => A1_same_order hp hd (mem_powerset.1 hD') hD

/-- **(A2)** of `CSI14_the_ceiling_at_p.md`: the last `r` dancers in the base-`p` order are
exactly `GoldenMatching.Lr I r`. -/
theorem A2_Lr {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) (r : ℕ) : LrP p d I r = GoldenMatching.Lr I r := by
  unfold LrP GoldenMatching.Lr
  exact filter_congr fun D hD => by rw [A2_rank hp hd (mem_powerset.1 hD)]

/-- **(A2)** of `CSI14_the_ceiling_at_p.md`: the first `r` dancers in the base-`p` order are
exactly `GoldenMatching.Fr I r`. -/
theorem A2_Fr {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) (r : ℕ) : FrP p d I r = GoldenMatching.Fr I r := by
  unfold FrP GoldenMatching.Fr
  exact filter_congr fun D hD => by rw [A2_rank hp hd (mem_powerset.1 hD)]

/-- **(A2)** of `CSI14_the_ceiling_at_p.md`, last sentence: `GoldenMatching.theorem_B`
(Theorem O) applies unchanged in the base-`p` order: for `I ⊆ {0, …, k−1}` and
`r ≤ 2^{|I|}` there is exactly one bijection from the last `r` to the first `r` dancers of the
base-`p` order all of whose arrows are golden ("exactly one" = existence and uniqueness). -/
theorem theorem_O_P (k : ℕ) {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) (r : ℕ) (hr : r ≤ 2 ^ #I) :
    (∃ β : LrP p d I r ≃ FrP p d I r,
        ∀ D : LrP p d I r, GoldenMatching.IsGoldenArrow k I D (β D)) ∧
      ∀ β β' : LrP p d I r ≃ FrP p d I r,
        (∀ D : LrP p d I r, GoldenMatching.IsGoldenArrow k I D (β D)) →
        (∀ D : LrP p d I r, GoldenMatching.IsGoldenArrow k I D (β' D)) → ∀ D, β D = β' D := by
  have hL := A2_Lr hp hd r
  have hF := A2_Fr hp hd r
  generalize LrP p d I r = L at hL ⊢
  generalize FrP p d I r = F at hF ⊢
  subst hL hF
  exact GoldenMatching.theorem_B k hI r hr

/-- **(A3)** (the complement) of `CSI14_the_ceiling_at_p.md`: for `D ⊆ I`,
`oP p d (I ∖ D) + oP p d D = oP p d I`. (No hypothesis on `p` or the digits is needed.) -/
theorem A3_complement (p : ℕ) (d : ℕ → ℕ) {I D : Finset ℕ} (hD : D ⊆ I) :
    oP p d (I \ D) + oP p d D = oP p d I :=
  sum_sdiff hD

end ColouredSand.OddTwist
