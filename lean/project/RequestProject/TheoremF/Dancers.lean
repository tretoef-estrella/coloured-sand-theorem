module

public import RequestProject.GoldenMatching.Complement
public import RequestProject.Houses.LemmaA

/-!
# Part 0 of `C7_theorem_F_walk_and_cut.md`: dancers in o-order (Lemma 0)

## Encoding

* `I : Finset ℕ` is an arbitrary finite set of naturals; `N = 2^{|I|}` is written `2 ^ #I`.
* `dancer I p` is `dancer_I(p) := {t ∈ I : bit_{j(t)}(p) = 1}`, literally
  `I.filter (fun t => Houses.bit (#(I.filter (· < t))) p = 1)`, where
  `j(t) = #(I.filter (· < t))` and `Houses.bit u x = ⌊x / 2^u⌋ mod 2` (piece C6).
  It is defined for every `p : ℕ`; the statements only use `p < N`.
* `o = Rulers.oE` (piece C3) and `rank = GoldenMatching.rank` (piece C4).
* In (0e), `c := max I` is written `hne : I.Nonempty`, `c = I.max' hne`, and
  `I' := I ∖ {c}` is `I.erase c`; `M = 2^{|I'|}` is `2 ^ #(I.erase c)`.
-/

@[expose] public section

namespace TheoremF

open Finset Rulers GoldenMatching

/-- *Setting* (dancers in o-order) of `C7_theorem_F_walk_and_cut.md`: the dancer at position `p`,
`dancer_I(p) := {t ∈ I : bit_{j(t)}(p) = 1}` with `j(t) := #{u ∈ I : u < t}`. -/
def dancer (I : Finset ℕ) (p : ℕ) : Finset ℕ :=
  I.filter (fun t => Houses.bit (#(I.filter (· < t))) p = 1)

/-- The set of binary digits `j < n` of `p` equal to `1`. (Auxiliary for Lemma 0 of
`C7_theorem_F_walk_and_cut.md`.) -/
def bitsOf (n p : ℕ) : Finset ℕ := (range n).filter (fun j => Houses.bit j p = 1)

/-- Auxiliary for Lemma 0 of `C7_theorem_F_walk_and_cut.md`: `bitsOf n p ⊆ {0,…,n−1}`. -/
lemma bitsOf_subset (n p : ℕ) : bitsOf n p ⊆ range n := filter_subset _ _

/-- Auxiliary for Lemma 0 of `C7_theorem_F_walk_and_cut.md`: `o(bitsOf n p) = p mod 2^n`. -/
lemma oE_bitsOf (n p : ℕ) : oE (bitsOf n p) = p % 2 ^ n := by
  induction n with
  | zero => simp [bitsOf, oE, Nat.mod_one]
  | succ n ih =>
    rw [Nat.mod_pow_succ, ← ih]
    have hb : Houses.bit n p = p / 2 ^ n % 2 := rfl
    have hnot : n ∉ bitsOf n p := by simp [bitsOf]
    unfold bitsOf at hnot ⊢
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [oE, sum_insert hnot, ← oE]; rw [← hb, h]; ring
    · have : p / 2 ^ n % 2 = 0 := by omega
      rw [this]; ring

section Enum

variable {I : Finset ℕ} {τ : ℕ → ℕ}

/-- Auxiliary for Lemma 0 of `C7_theorem_F_walk_and_cut.md`: for an increasing enumeration `τ`
of `I`, `{u ∈ I : u < τ(i)} = τ({0,…,i−1})`. -/
lemma filter_lt_enum (hτ : StrictMono τ) (hτI : (range #I).image τ = I) {i : ℕ} (hi : i < #I) :
    I.filter (· < τ i) = (range i).image τ := by
  ext t
  constructor
  · intro ht
    rw [mem_filter] at ht
    have : t ∈ (range #I).image τ := by rw [hτI]; exact ht.1
    obtain ⟨j, -, rfl⟩ := mem_image.1 this
    exact mem_image.2 ⟨j, mem_range.2 (hτ.lt_iff_lt.1 ht.2), rfl⟩
  · intro ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    have hj' := mem_range.1 hj
    refine mem_filter.2 ⟨?_, hτ hj'⟩
    rw [← hτI]; exact mem_image.2 ⟨j, mem_range.2 (by omega), rfl⟩

/-- Auxiliary for Lemma 0 of `C7_theorem_F_walk_and_cut.md`: `j(τ(i)) = i`. -/
lemma card_filter_lt_enum (hτ : StrictMono τ) (hτI : (range #I).image τ = I) {i : ℕ}
    (hi : i < #I) : #(I.filter (· < τ i)) = i := by
  rw [filter_lt_enum hτ hτI hi, card_image_of_injective _ hτ.injective, card_range]

/-- Auxiliary for Lemma 0 of `C7_theorem_F_walk_and_cut.md`: `dancer_I(p)` is the image of the
binary digits of `p` under the increasing enumeration of `I`. -/
lemma dancer_eq_image (hτ : StrictMono τ) (hτI : (range #I).image τ = I) (p : ℕ) :
    dancer I p = (bitsOf #I p).image τ := by
  ext t
  simp only [dancer, bitsOf, mem_filter, mem_image, mem_range]
  constructor
  · rintro ⟨ht, hb⟩
    have : t ∈ (range #I).image τ := by rw [hτI]; exact ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 this
    rw [card_filter_lt_enum hτ hτI (mem_range.1 hj)] at hb
    exact ⟨j, ⟨mem_range.1 hj, hb⟩, rfl⟩
  · rintro ⟨j, ⟨hj, hb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hτI]; exact mem_image.2 ⟨j, mem_range.2 hj, rfl⟩
    · rw [card_filter_lt_enum hτ hτI hj]; exact hb

end Enum

variable {I : Finset ℕ}

/-- **(0a)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`: `dancer_I(p) ⊆ I`.  (More general than
the file: true for every `p`, not only `p < N`.) -/
theorem lemma_0a (I : Finset ℕ) (p : ℕ) : dancer I p ⊆ I := filter_subset _ _

/-- `rank(dancer_I(p)) = p mod N` for every `p`. (Auxiliary for (0c) of Lemma 0 of
`C7_theorem_F_walk_and_cut.md`.) -/
lemma rank_dancer (I : Finset ℕ) (p : ℕ) : rank I (dancer I p) = p % 2 ^ #I := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  rw [rank_eq_pos hτ hτI (lemma_0a I p), dancer_eq_image hτ hτI,
    idx_image hτ (bitsOf_subset _ _), oE_bitsOf]

/-- Two dancers with the same rank are equal. (Auxiliary for Lemma 0 of
`C7_theorem_F_walk_and_cut.md`.) -/
lemma rank_injOn {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I) (h : rank I D = rank I D') :
    D = D' := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  rw [rank_eq_pos hτ hτI hD, rank_eq_pos hτ hτI hD'] at h
  exact pos_injOn hτI hD hD' h

/-- **(0b)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`: for `p < q < N`,
`o(dancer_I(p)) < o(dancer_I(q))`. -/
theorem lemma_0b {p q : ℕ} (hpq : p < q) (hq : q < 2 ^ #I) :
    oE (dancer I p) < oE (dancer I q) := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  rw [oE_lt_iff_idx hτ hτI (lemma_0a I p) (lemma_0a I q), ← rank_eq_pos hτ hτI (lemma_0a I p),
    ← rank_eq_pos hτ hτI (lemma_0a I q), rank_dancer, rank_dancer, Nat.mod_eq_of_lt hq,
    Nat.mod_eq_of_lt (by omega)]
  exact hpq

/-- `p ↦ o(dancer_I(p))` is monotone on `[0, N)`. (Consequence of (0b) of Lemma 0 of
`C7_theorem_F_walk_and_cut.md`.) -/
lemma oE_dancer_mono {p q : ℕ} (hpq : p ≤ q) (hq : q < 2 ^ #I) :
    oE (dancer I p) ≤ oE (dancer I q) := by
  rcases hpq.lt_or_eq with h | rfl
  · exact (lemma_0b h hq).le
  · exact le_rfl

/-- **(0c)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`, first claim: every `D ⊆ I` is
`dancer_I(p)` for exactly one `p < N`. -/
theorem lemma_0c_existsUnique {D : Finset ℕ} (hD : D ⊆ I) :
    ∃! p, p < 2 ^ #I ∧ dancer I p = D := by
  refine ⟨rank I D, ⟨rank_lt hD, ?_⟩, ?_⟩
  · apply rank_injOn (lemma_0a I _) hD
    rw [rank_dancer, Nat.mod_eq_of_lt (rank_lt hD)]
  · rintro p ⟨hp, rfl⟩
    rw [rank_dancer, Nat.mod_eq_of_lt hp]

/-- **(0c)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`, second claim:
`rank_I(dancer_I(p)) = p` for `p < N`. -/
theorem lemma_0c_rank {p : ℕ} (hp : p < 2 ^ #I) : rank I (dancer I p) = p := by
  rw [rank_dancer, Nat.mod_eq_of_lt hp]

/-- **(0d)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`: for `p < N`,
`dancer_I(N − 1 − p) = I ∖ dancer_I(p)`. -/
theorem lemma_0d {p : ℕ} (hp : p < 2 ^ #I) : dancer I (2 ^ #I - 1 - p) = I \ dancer I p := by
  apply rank_injOn (lemma_0a I _) sdiff_subset
  rw [lemma_C1_rank (lemma_0a I p), lemma_0c_rank hp, lemma_0c_rank (by omega)]

/-- Auxiliary for (0e) of Lemma 0, `C7_theorem_F_walk_and_cut.md`. -/
lemma bit_lt_pow {j p : ℕ} (hp : p < 2 ^ j) : Houses.bit j p = 0 := by
  simp [Houses.bit, Nat.div_eq_of_lt hp]

/-- Auxiliary for (0e) of Lemma 0, `C7_theorem_F_walk_and_cut.md`. -/
lemma bit_pow_add_self {n p : ℕ} (hp : p < 2 ^ n) : Houses.bit n (2 ^ n + p) = 1 := by
  unfold Houses.bit
  rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hp]

/-- Auxiliary for (0e) of Lemma 0, `C7_theorem_F_walk_and_cut.md`. -/
lemma bit_pow_add_lt {n j p : ℕ} (hj : j < n) : Houses.bit j (2 ^ n + p) = Houses.bit j p := by
  unfold Houses.bit
  have : 2 ^ n = 2 ^ j * (2 * 2 ^ (n - j - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [this, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
  omega

/-- **(0e)** of Lemma 0, `C7_theorem_F_walk_and_cut.md`: with `c = max I`, `I' = I ∖ {c}` and
`M = 2^{|I'|}`, for `p < M`, `dancer_I(p) = dancer_{I'}(p)` and
`dancer_I(M + p) = dancer_{I'}(p) ∪ {c}`. -/
theorem lemma_0e (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) {p : ℕ}
    (hp : p < 2 ^ #(I.erase c)) :
    dancer I p = dancer (I.erase c) p ∧
      dancer I (2 ^ #(I.erase c) + p) = dancer (I.erase c) p ∪ {c} := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hj : ∀ t ∈ I.erase c, I.filter (· < t) = (I.erase c).filter (· < t) := by
    intro t ht
    ext u
    simp only [mem_filter, mem_erase]
    have := hcmax t (mem_of_mem_erase ht)
    have htc := ne_of_mem_erase ht
    constructor
    · rintro ⟨hu, hut⟩; exact ⟨⟨by omega, hu⟩, hut⟩
    · rintro ⟨⟨-, hu⟩, hut⟩; exact ⟨hu, hut⟩
  have hjc : I.filter (· < c) = I.erase c := by
    ext u
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hu, huc⟩; exact ⟨by omega, hu⟩
    · rintro ⟨huc, hu⟩; exact ⟨hu, lt_of_le_of_ne (hcmax u hu) huc⟩
  have hjlt : ∀ t ∈ I.erase c, #((I.erase c).filter (· < t)) < #(I.erase c) := by
    intro t ht
    apply card_lt_card
    refine ⟨filter_subset _ _, fun h => ?_⟩
    have := h ht
    simp at this
  constructor
  · ext t
    simp only [dancer, mem_filter]
    by_cases htc : t = c
    · subst htc
      rw [hjc, bit_lt_pow hp]
      simp
    · have ht' : t ∈ I ↔ t ∈ I.erase c := by simp [htc]
      constructor
      · rintro ⟨ht, hb⟩
        have hte : t ∈ I.erase c := ht'.1 ht
        rw [hj t hte] at hb
        exact ⟨hte, hb⟩
      · rintro ⟨hte, hb⟩
        rw [← hj t hte] at hb
        exact ⟨ht'.2 hte, hb⟩
  · ext t
    simp only [dancer, mem_filter, mem_union, mem_singleton]
    by_cases htc : t = c
    · subst htc
      rw [hjc, bit_pow_add_self hp]
      simp [hcI]
    · have ht' : t ∈ I ↔ t ∈ I.erase c := by simp [htc]
      simp only [htc, or_false]
      constructor
      · rintro ⟨ht, hb⟩
        have hte : t ∈ I.erase c := ht'.1 ht
        rw [hj t hte, bit_pow_add_lt (hjlt t hte)] at hb
        exact ⟨hte, hb⟩
      · rintro ⟨hte, hb⟩
        rw [hj t hte, bit_pow_add_lt (hjlt t hte)]
        exact ⟨ht'.2 hte, hb⟩

/-- `dancer_I(0) = ∅`. (Used in Lemma 0f of `C7_theorem_F_walk_and_cut.md`.) -/
lemma dancer_zero (I : Finset ℕ) : dancer I 0 = ∅ := by
  ext t; simp [dancer, Houses.bit]

end TheoremF
