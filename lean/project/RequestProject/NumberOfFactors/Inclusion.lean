module

public import Mathlib

/-!
# Inclusion matrices over `ℤ`: full rank and saturation

Auxiliary file for **(D1) Wilson's diagonal form** of `CS5_theorem_D_number_of_factors.md`.

## Encoding

We work with integer vectors `Finset α → ℤ` indexed by all finite subsets of a type `α`, and with a
*ground set* `X : Finset α` (later `X = univ` with `α = Fin m`).  For `s : ℕ` the map
`zeta X s` sends a coefficient vector `c` to `T ↦ [T ⊆ X ∧ |T| = s] · ∑_{S ⊆ T} c S`.  If `c` is
supported on the `i`-subsets, `zeta X s c = ∑_S c S · (row S of W_{i,s})`, the combination of the
rows of the inclusion matrix `W_{i,s}` of `X`.  Hence `Gsub X j s = zeta X s (lowSub j)` is the
`ℤ`-module spanned by the rows of `W_{0,s}, …, W_{j−1,s}`.

## Results

* `zeta_zeta`: `W_{i,k} W_{k,s} = C(s−i, k−i) W_{i,s}`.
* `zeta_inj` (Gottlieb–Kantor over `ℤ`): for `i ≤ s` and `i + s ≤ |X|` the rows of `W_{i,s}` are
  linearly independent.
* `gsub_all`: if `j + s > |X|`, the rows of `W_{i,s}`, `i < j`, span all of level `s`.
* `gsub_sat`: `Gsub X j s` is saturated (`n • f ∈ G → f ∈ G` for `n ≠ 0`).
-/

@[expose] public section

open Finset

namespace ColouredSand.NumberOfFactors

/-- A submodule `N` of a `ℤ`-module is *saturated* if `n • x ∈ N` with `n ≠ 0` implies `x ∈ N`
(equivalently, the quotient is torsion free). -/
def IsSat {M : Type*} [AddCommGroup M] (N : Submodule ℤ M) : Prop :=
  ∀ (n : ℤ) (x : M), n ≠ 0 → n • x ∈ N → x ∈ N

variable {α : Type*} [DecidableEq α]

/-- `zeta X s c = (T ↦ [T ⊆ X ∧ |T| = s] ∑_{S ⊆ T} c S)`: combination of rows of the inclusion
matrices `W_{i,s}` of the ground set `X`, with coefficients `c`. -/
def zeta (X : Finset α) (s : ℕ) : (Finset α → ℤ) →ₗ[ℤ] (Finset α → ℤ) where
  toFun c T := if T ⊆ X ∧ T.card = s then ∑ S ∈ T.powerset, c S else 0
  map_add' c d := by
    ext T; simp only [Pi.add_apply]; split_ifs <;> simp [sum_add_distrib]
  map_smul' a c := by
    ext T; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [mul_sum]

/-- Coefficient vectors supported on sets of size `< j`. -/
def lowSub (j : ℕ) : Submodule ℤ (Finset α → ℤ) where
  carrier := {c | ∀ S, j ≤ S.card → c S = 0}
  add_mem' hc hd S hS := by simp [hc S hS, hd S hS]
  zero_mem' _ _ := rfl
  smul_mem' a c hc S hS := by simp [hc S hS]

/-- `Gsub X j s`: the `ℤ`-span of the rows of `W_{0,s}, …, W_{j−1,s}` (ground set `X`). -/
def Gsub (X : Finset α) (j s : ℕ) : Submodule ℤ (Finset α → ℤ) := (lowSub j).map (zeta X s)

lemma zeta_apply (X : Finset α) (s : ℕ) (c : Finset α → ℤ) (T : Finset α) :
    zeta X s c T = if T ⊆ X ∧ T.card = s then ∑ S ∈ T.powerset, c S else 0 := rfl

omit [DecidableEq α] in
lemma mem_lowSub {j : ℕ} {c : Finset α → ℤ} : c ∈ lowSub j ↔ ∀ S, j ≤ S.card → c S = 0 :=
  Iff.rfl

lemma zeta_congr {X : Finset α} {s : ℕ} {c d : Finset α → ℤ} (h : ∀ S ⊆ X, c S = d S) :
    zeta X s c = zeta X s d := by
  ext T
  simp only [zeta_apply]
  split_ifs with hT
  · exact sum_congr rfl fun S hS => h S ((mem_powerset.mp hS).trans hT.1)
  · rfl

lemma zeta_eq_zero_of_not {X : Finset α} {s : ℕ} (c : Finset α → ℤ) {T : Finset α}
    (hT : ¬ (T ⊆ X ∧ T.card = s)) : zeta X s c T = 0 := by
  simp [zeta_apply, hT]

/-! ### Counting intermediate sets -/

lemma card_between {S T : Finset α} (hST : S ⊆ T) {k : ℕ} (hk : S.card ≤ k) :
    ((T.powerset.filter fun S' => S ⊆ S' ∧ S'.card = k)).card =
      (T.card - S.card).choose (k - S.card) := by
  rw [← card_sdiff_of_subset hST, ← card_powersetCard]
  refine card_bij (fun S' _ => S' \ S) ?_ ?_ ?_
  · intro S' hS'
    simp only [mem_filter, mem_powerset] at hS'
    rw [mem_powersetCard]
    refine ⟨sdiff_subset_sdiff hS'.1 (subset_refl S), ?_⟩
    rw [card_sdiff_of_subset hS'.2.1, hS'.2.2]
  · intro a ha b hb hab
    simp only [mem_filter, mem_powerset] at ha hb
    have hab' : a \ S = b \ S := hab
    rw [← sdiff_union_of_subset ha.2.1, ← sdiff_union_of_subset hb.2.1, hab']
  · intro Y hY
    rw [mem_powersetCard] at hY
    have hdisj : Disjoint Y S := by
      rw [disjoint_left]; intro x hx hxS
      exact (mem_sdiff.mp (hY.1 hx)).2 hxS
    refine ⟨Y ∪ S, ?_, ?_⟩
    · simp only [mem_filter, mem_powerset]
      refine ⟨union_subset (hY.1.trans sdiff_subset) hST, subset_union_right, ?_⟩
      rw [card_union_of_disjoint hdisj, hY.2]; omega
    · exact union_sdiff_cancel_right hdisj

/-- **Composition of inclusion matrices.**  If `c` is supported (on subsets of `X`) on the
`i`-sets and `i ≤ k`, then `zeta X s (zeta X k c) = C(s−i, k−i) • zeta X s c`, i.e.
`W_{i,k} W_{k,s} = C(s−i, k−i) W_{i,s}`. -/
lemma zeta_zeta {X : Finset α} {i k s : ℕ} (hik : i ≤ k) {c : Finset α → ℤ}
    (hc : ∀ S ⊆ X, S.card ≠ i → c S = 0) :
    zeta X s (zeta X k c) = (((s - i).choose (k - i) : ℕ) : ℤ) • zeta X s c := by
  ext T
  simp only [zeta_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hT : T ⊆ X ∧ T.card = s
  · rw [if_pos hT, if_pos hT, mul_sum]
    have h1 : ∀ S' ∈ T.powerset, (if S' ⊆ X ∧ S'.card = k then ∑ S ∈ S'.powerset, c S else 0) =
        if S'.card = k then ∑ S ∈ S'.powerset, c S else 0 := by
      intro S' hS'
      have : S' ⊆ X := (mem_powerset.mp hS').trans hT.1
      simp [this]
    rw [sum_congr rfl h1, ← sum_filter]
    rw [sum_comm' (t' := T.powerset) (s' := fun S => (T.powerset.filter
      fun S' => S ⊆ S' ∧ S'.card = k))]
    · refine sum_congr rfl fun S hS => ?_
      rw [sum_const, nsmul_eq_mul]
      have hSX : S ⊆ X := (mem_powerset.mp hS).trans hT.1
      by_cases hSi : S.card = i
      · rw [card_between (mem_powerset.mp hS) (by omega), hT.2, hSi]
      · rw [hc S hSX hSi]; ring
    · intro S' S
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3, h2⟩, h3.trans h1⟩
      · rintro ⟨⟨h1, h3, h2⟩, -⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · rw [if_neg hT, if_neg hT, mul_zero]

/-! ### Splitting off one element -/

/-- `c ↦ (S ↦ [a ∉ S] c (insert a S))`. -/
def shiftv (a : α) (c : Finset α → ℤ) : Finset α → ℤ := fun S => if a ∈ S then 0 else c (insert a S)

lemma zeta_insert_of_subset {X : Finset α} {a : α} {s : ℕ} (c : Finset α → ℤ) {T : Finset α}
    (hT : T ⊆ X) : zeta (insert a X) s c T = zeta X s c T := by
  simp only [zeta_apply, hT, hT.trans (subset_insert a X), true_and]

lemma zeta_insert_insert {X : Finset α} {a : α} (ha : a ∉ X) {s : ℕ} (c : Finset α → ℤ)
    {T : Finset α} (hT : T ⊆ X) :
    zeta (insert a X) (s + 1) c (insert a T) =
      zeta X s c T + zeta X s (shiftv a c) T := by
  have haT : a ∉ T := fun h => ha (hT h)
  simp only [zeta_apply, hT, true_and, insert_subset_insert a hT, card_insert_of_notMem haT,
    Nat.add_right_cancel_iff]
  split_ifs
  · rw [sum_powerset_insert haT]
    congr 1
    refine sum_congr rfl fun S hS => ?_
    have : a ∉ S := fun h => haT (mem_powerset.mp hS h)
    simp [shiftv, this]
  · simp

lemma zeta_insert_insert_zero {X : Finset α} {a : α} (c : Finset α → ℤ)
    {T : Finset α} : zeta (insert a X) 0 c (insert a T) = 0 := by
  apply zeta_eq_zero_of_not
  rintro ⟨-, h⟩
  simp at h

/-- Values of a function on subsets of `insert a X`. -/
lemma subset_insert_cases {X : Finset α} {a : α} {T : Finset α} (hT : T ⊆ insert a X) :
    T ⊆ X ∨ ∃ T₀ ⊆ X, a ∉ T₀ ∧ T = insert a T₀ := by
  by_cases haT : a ∈ T
  · right
    refine ⟨T.erase a, ?_, notMem_erase a T, (insert_erase haT).symm⟩
    intro x hx
    have hx' := mem_erase.mp hx
    rcases mem_insert.mp (hT hx'.2) with h | h
    · exact absurd h hx'.1
    · exact h
  · left
    intro x hx
    rcases mem_insert.mp (hT hx) with h | h
    · exact absurd (h ▸ hx) haT
    · exact h

/-! ### Level-`i` vectors equal to their own `zeta` -/

lemma zeta_self {X : Finset α} {i : ℕ} {c : Finset α → ℤ} (hc : ∀ S ⊆ X, S.card ≠ i → c S = 0)
    {T : Finset α} (hT : T ⊆ X) (hTi : T.card = i) : zeta X i c T = c T := by
  rw [zeta_apply, if_pos ⟨hT, hTi⟩, sum_eq_single T]
  · intro S hS hne
    have hSX : S ⊆ X := (mem_powerset.mp hS).trans hT
    apply hc S hSX
    intro h
    exact hne (eq_of_subset_of_card_le (mem_powerset.mp hS) (by omega))
  · intro h; exact absurd (mem_powerset_self T) h

/-! ### Gottlieb–Kantor: the rows of `W_{i,s}` are independent for `i ≤ s`, `i + s ≤ |X|` -/

lemma zeta_inj_diag {X : Finset α} {i : ℕ} {c : Finset α → ℤ}
    (hc : ∀ S ⊆ X, S.card ≠ i → c S = 0) (h0 : zeta X i c = 0) : ∀ S ⊆ X, c S = 0 := by
  intro S hS
  by_cases hSi : S.card = i
  · rw [← zeta_self hc hS hSi, h0]; rfl
  · exact hc S hS hSi

/-- **Gottlieb–Kantor over `ℤ`.**  For `i ≤ s` and `i + s ≤ |X|`, if `c` is supported (on subsets
of `X`) on the `i`-sets and `zeta X s c = 0`, then `c` vanishes on all subsets of `X`. -/
theorem zeta_inj (X : Finset α) : ∀ (i s : ℕ), i ≤ s → i + s ≤ X.card → ∀ c : Finset α → ℤ,
    (∀ S ⊆ X, S.card ≠ i → c S = 0) → zeta X s c = 0 → ∀ S ⊆ X, c S = 0 := by
  induction X using Finset.induction_on with
  | empty =>
    intro i s his hs c hc h0
    obtain rfl : i = s := by simp at hs; omega
    exact zeta_inj_diag hc h0
  | @insert a X ha ih =>
    intro i s his hs c hc h0
    rcases eq_or_lt_of_le his with rfl | hlt
    · exact zeta_inj_diag hc h0
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [card_insert_of_notMem ha] at hs
    -- the two halves
    have hA : zeta X (s + 1) c = 0 := by
      ext T
      by_cases hT : T ⊆ X
      · rw [← zeta_insert_of_subset c hT, h0]
      · exact zeta_eq_zero_of_not c (fun h => hT h.1)
    have hB : zeta X s c + zeta X s (shiftv a c) = 0 := by
      ext T
      by_cases hT : T ⊆ X
      · simp only [Pi.add_apply, Pi.zero_apply]
        rw [← zeta_insert_insert ha c hT, h0]; rfl
      · simp only [Pi.add_apply, Pi.zero_apply]
        rw [zeta_eq_zero_of_not c (fun h => hT h.1),
          zeta_eq_zero_of_not _ (fun h => hT h.1), add_zero]
    have hsh : ∀ S ⊆ X, S.card ≠ i - 1 → shiftv a c S = 0 := by
      intro S hS hSi
      have haS : a ∉ S := fun h => ha (hS h)
      simp only [shiftv, haS, if_false]
      apply hc _ (insert_subset_insert a hS)
      rw [card_insert_of_notMem haS]
      omega
    -- `shiftv a c` vanishes on `X`
    have hsh0 : ∀ S ⊆ X, shiftv a c S = 0 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · intro S hS
        have haS : a ∉ S := fun h => ha (hS h)
        simp only [shiftv, haS, if_false]
        apply hc _ (insert_subset_insert a hS)
        rw [card_insert_of_notMem haS]; omega
      · apply ih (i - 1) (s + 1) (by omega) (by omega) _ hsh
        have h2 := congrArg (zeta X (s + 1)) hB
        have hc' : ∀ S ⊆ X, S.card ≠ i → c S = 0 := fun S hS => hc S (hS.trans (subset_insert a X))
        rw [map_add, map_zero, zeta_zeta (by omega) hc', zeta_zeta (by omega) hsh, hA,
          smul_zero, zero_add] at h2
        have hne : (((s + 1 - (i - 1)).choose (s - (i - 1)) : ℕ) : ℤ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (by omega)).ne'
        exact (smul_eq_zero.mp h2).resolve_left hne
    have hc0 : ∀ S ⊆ X, c S = 0 := by
      apply ih i s (by omega) (by omega) c (fun S hS => hc S (hS.trans (subset_insert a X)))
      rw [zeta_congr (d := 0) hsh0, map_zero, add_zero] at hB
      exact hB
    intro S hS
    rcases subset_insert_cases hS with h | ⟨T₀, hT₀, haT₀, rfl⟩
    · exact hc0 S h
    · have := hsh0 T₀ hT₀
      simpa [shiftv, haT₀] using this

/-! ### The case `j + s > |X|`: everything of level `s` -/

lemma sum_neg_one_pow_filter {T' Y₀ : Finset α} :
    ∑ Y ∈ T'.powerset, (if Y ⊆ Y₀ then (-1 : ℤ) ^ Y.card else 0) =
      if T' ∩ Y₀ = ∅ then 1 else 0 := by
  rw [← sum_powerset_neg_one_pow_card, ← sum_filter]
  congr 1
  ext Y
  simp only [mem_filter, mem_powerset, subset_inter_iff]

/-- If `j + s > |X|`, every vector supported on the `s`-subsets of `X` lies in `Gsub X j s`
(inclusion–exclusion: `e_T = ∑_{Y ⊆ X ∖ T} (−1)^{|Y|} (row Y of W_{|Y|,s})`). -/
theorem gsub_all {X : Finset α} {j s : ℕ} (hjs : X.card < j + s) {f : Finset α → ℤ}
    (hf : ∀ T, ¬ (T ⊆ X ∧ T.card = s) → f T = 0) : f ∈ Gsub X j s := by
  let c : Finset α → ℤ := fun Y =>
    ∑ T ∈ X.powerset, f T * (if Y ⊆ X \ T then (-1 : ℤ) ^ Y.card else 0)
  refine ⟨c, ?_, ?_⟩
  · intro Y hY
    refine sum_eq_zero fun T hT => ?_
    by_cases hfT : f T = 0
    · simp [hfT]
    · have hT' : T ⊆ X ∧ T.card = s := by
        by_contra h; exact hfT (hf T h)
      have : ¬ Y ⊆ X \ T := by
        intro hY'
        have := card_le_card hY'
        rw [card_sdiff_of_subset hT'.1] at this
        have := card_le_card hT'.1
        omega
      simp [this]
  · ext T'
    show zeta X s c T' = f T'
    rw [zeta_apply]
    split_ifs with hT'
    · simp only [c]
      rw [sum_comm]
      simp_rw [← mul_sum, sum_neg_one_pow_filter]
      rw [sum_eq_single T']
      · have : T' ∩ (X \ T') = ∅ := by
          ext x; simp
        simp [this]
      · intro T hT hne
        by_cases hfT : f T = 0
        · simp [hfT]
        · have hT2 : T ⊆ X ∧ T.card = s := by
            by_contra h; exact hfT (hf T h)
          have : T' ∩ (X \ T) ≠ ∅ := by
            intro h
            apply hne
            refine (eq_of_subset_of_card_le ?_ (by omega)).symm
            intro x hx
            by_contra hxT
            have : x ∈ T' ∩ (X \ T) := mem_inter.mpr ⟨hx, mem_sdiff.mpr ⟨hT'.1 hx, hxT⟩⟩
            rw [h] at this; simp at this
          simp [this]
      · intro h; exact absurd (mem_powerset.mpr hT'.1) h
    · exact (hf T' hT').symm

/-! ### Saturation -/

lemma gsub_zero (X : Finset α) (s : ℕ) : Gsub X 0 s = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, hc, rfl⟩
  have : c = 0 := funext fun S => hc S (Nat.zero_le _)
  simp [this]

lemma gsub_support {X : Finset α} {j s : ℕ} {f : Finset α → ℤ} (hf : f ∈ Gsub X j s) :
    ∀ T, ¬ (T ⊆ X ∧ T.card = s) → f T = 0 := by
  obtain ⟨c, -, rfl⟩ := hf
  intro T hT
  exact zeta_eq_zero_of_not c hT

lemma isSat_of_all {X : Finset α} {j s : ℕ} (hjs : X.card < j + s) : IsSat (Gsub X j s) := by
  intro n f hn hf
  apply gsub_all hjs
  intro T hT
  have := gsub_support hf T hT
  simpa [hn] using this

/-- The projection of a coefficient vector onto level `i`. -/
def projv (i : ℕ) (c : Finset α → ℤ) : Finset α → ℤ := fun S => if S.card = i then c S else 0

omit [DecidableEq α] in
lemma sum_projv {j : ℕ} {c : Finset α → ℤ} (hc : c ∈ lowSub j) :
    ∑ i ∈ range j, projv i c = c := by
  ext S
  simp only [Finset.sum_apply, projv]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [hc S (by simpa using h)]

omit [DecidableEq α] in
lemma projv_mem_lowSub {i j : ℕ} (hij : i < j) (c : Finset α → ℤ) : projv i c ∈ lowSub j := by
  intro S hS
  simp only [projv]
  split_ifs with h
  · omega
  · rfl

omit [DecidableEq α] in
lemma projv_level (i : ℕ) (c : Finset α → ℤ) {X : Finset α} :
    ∀ S ⊆ X, S.card ≠ i → projv i c S = 0 := by
  intro S _ h; simp [projv, h]

lemma zeta_mem_gsub {X : Finset α} {j s : ℕ} {c : Finset α → ℤ} (hc : c ∈ lowSub j) :
    zeta X s c ∈ Gsub X j s := ⟨c, hc, rfl⟩

/-- **Lifting lower rows to level `k`.**  For `j ≤ k + 1` and `k ≤ s` there is `N ≠ 0` such that for every
`c` supported on sets of size `< j` there is a level-`k` vector `d` with
`zeta X s d = N • zeta X s c` and `zeta X s' d ∈ Gsub X j s'` for all `s'`. -/
lemma lift_lower (X : Finset α) {j k s : ℕ} (hjk : j ≤ k + 1) (hks : k ≤ s) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ c ∈ lowSub j, ∃ d : Finset α → ℤ,
      (∀ S ⊆ X, S.card ≠ k → d S = 0) ∧ zeta X s d = N • zeta X s c ∧
      ∀ s', zeta X s' d ∈ Gsub X j s' := by
  let C : ℕ → ℤ := fun i => (((s - i).choose (k - i) : ℕ) : ℤ)
  have hC : ∀ i ∈ range j, C i ≠ 0 := by
    intro i hi
    have := mem_range.mp hi
    simp only [C, ne_eq, Nat.cast_eq_zero]
    exact (Nat.choose_pos (by omega)).ne'
  refine ⟨∏ i ∈ range j, C i, prod_ne_zero_iff.mpr hC, fun c hc => ?_⟩
  let N' : ℕ → ℤ := fun i => ∏ i' ∈ (range j).erase i, C i'
  refine ⟨∑ i ∈ range j, N' i • zeta X k (projv i c), ?_, ?_, ?_⟩
  · intro S hS hSk
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine sum_eq_zero fun i _ => ?_
    rw [zeta_eq_zero_of_not _ (fun h => hSk h.2), smul_zero]
  · rw [map_sum]
    conv_rhs => rw [← sum_projv hc, map_sum, smul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [map_zsmul, zeta_zeta (by have := mem_range.mp hi; omega) (projv_level i c), smul_smul]
    congr 1
    rw [← mul_prod_erase _ _ hi, mul_comm]
  · intro s'
    rw [map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [map_zsmul, zeta_zeta (by have := mem_range.mp hi; omega) (projv_level i c), smul_smul]
    exact Submodule.smul_mem _ _ (zeta_mem_gsub (projv_mem_lowSub (mem_range.mp hi) c))

/-- The key step of the saturation proof: a relation among rows of level `s` descends to level
`s − 1`. -/
lemma descend {X : Finset α} {j s : ℕ} (hsat : IsSat (Gsub X j s))
    (hjs : j + (s + 1) ≤ X.card) {c : Finset α → ℤ} (hc : c ∈ lowSub (j + 1))
    (h0 : zeta X (s + 1) c = 0) : zeta X s c ∈ Gsub X j s := by
  -- split `c` into its top level `j` and the rest
  let ctop := projv j c
  let clow := c - ctop
  have hclow : clow ∈ lowSub j := by
    intro S hS
    simp only [clow, ctop, projv, Pi.sub_apply]
    split_ifs with h
    · ring
    · rw [hc S (by omega)]; ring
  have hcsplit : c = clow + ctop := by simp [clow]
  rw [hcsplit, map_add]
  refine Submodule.add_mem _ (zeta_mem_gsub hclow) ?_
  by_cases hjs' : s < j
  · -- top level too high to matter
    have : zeta X s ctop = 0 := by
      ext T
      rw [zeta_apply]
      split_ifs with hT
      · refine sum_eq_zero fun S hS => ?_
        have := card_le_card (mem_powerset.mp hS)
        simp only [ctop, projv]
        rw [if_neg (by omega)]
      · rfl
    rw [this]; exact Submodule.zero_mem _
  push_neg at hjs'
  obtain ⟨N, hN, hlift⟩ := lift_lower X (j := j) (k := j) (s := s + 1) (by omega) (by omega)
  obtain ⟨d, hd, hds, hds'⟩ := hlift clow hclow
  -- `N • ctop + d` is of level `j` and killed by `zeta X (s+1)`
  have hlev : ∀ S ⊆ X, S.card ≠ j → (N • ctop + d) S = 0 := by
    intro S hS hSj
    simp [hd S hS hSj, ctop, projv, hSj]
  have hz : zeta X (s + 1) (N • ctop + d) = 0 := by
    rw [map_add, hds, map_zsmul, ← smul_add, ← map_add, add_comm ctop clow, ← hcsplit, h0, smul_zero]
  have hvan := zeta_inj X j (s + 1) (by omega) hjs _ hlev hz
  have h2 : zeta X s (N • ctop) = - zeta X s d := by
    have : zeta X s (N • ctop + d) = 0 := by
      rw [zeta_congr (d := 0) hvan, map_zero]
    rw [map_add] at this
    exact eq_neg_of_add_eq_zero_left this
  apply hsat N _ hN
  rw [← map_zsmul, h2]
  exact Submodule.neg_mem _ (hds' s)

/-- **Saturation.**  For every ground set `X` and all `j, s`, the `ℤ`-span `Gsub X j s` of the rows
of `W_{0,s}, …, W_{j−1,s}` is saturated in `Finset α → ℤ`. -/
theorem gsub_sat (X : Finset α) : ∀ j s : ℕ, IsSat (Gsub X j s) := by
  induction X using Finset.induction_on with
  | empty =>
    intro j s
    rcases Nat.eq_zero_or_pos (j + s) with h | h
    · obtain rfl : j = 0 := by omega
      rw [gsub_zero]; intro n f hn hf
      rw [Submodule.mem_bot] at hf ⊢
      exact (smul_eq_zero.mp hf).resolve_left hn
    · exact isSat_of_all (by simpa using h)
  | @insert a X ha ih =>
    intro j s
    by_cases hbig : (insert a X).card < j + s
    · exact isSat_of_all hbig
    rw [card_insert_of_notMem ha] at hbig
    push_neg at hbig
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [gsub_zero]; intro n f hn hf
      rw [Submodule.mem_bot] at hf ⊢
      exact (smul_eq_zero.mp hf).resolve_left hn
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    intro n f hn hf
    obtain ⟨c, hc, hcf⟩ := hf
    -- Step A: restriction to subsets of `X`
    let f₀ : Finset α → ℤ := fun T => if T ⊆ X then f T else 0
    have hf₀ : n • f₀ = zeta X s c := by
      ext T
      simp only [f₀, Pi.smul_apply, smul_eq_mul]
      split_ifs with hT
      · rw [← zeta_insert_of_subset (a := a) c hT, hcf]; rfl
      · rw [mul_zero, zeta_eq_zero_of_not c (fun h => hT h.1)]
    obtain ⟨c', hc', hc'f⟩ := ih (j + 1) s n f₀ hn (hf₀ ▸ zeta_mem_gsub hc)
    -- Step B
    let h := f - zeta (insert a X) s c'
    have hh0 : ∀ T ⊆ X, h T = 0 := by
      intro T hT
      have := congrFun hc'f T
      simp only [f₀, if_pos hT] at this
      simp only [h, Pi.sub_apply, zeta_insert_of_subset c' hT, this, sub_self]
    let c'' := c - n • c'
    have hc'' : c'' ∈ lowSub (j + 1) := Submodule.sub_mem _ hc (Submodule.smul_mem _ _ hc')
    have hnh : n • h = zeta (insert a X) s c'' := by
      simp only [h, c'', smul_sub, map_sub, map_zsmul, hcf]
    have hz0 : zeta X s c'' = 0 := by
      ext T
      by_cases hT : T ⊆ X
      · rw [← zeta_insert_of_subset (a := a) c'' hT, ← hnh]
        simp [hh0 T hT]
      · exact zeta_eq_zero_of_not c'' (fun h => hT h.1)
    -- Step C: the part of `h` on sets containing `a`
    let h₁ : Finset α → ℤ := fun T₀ => if T₀ ⊆ X then h (insert a T₀) else 0
    rcases Nat.eq_zero_or_pos s with hs | hs
    · -- `s = 0`: `h = 0`
      subst hs
      have : h = 0 := by
        ext T
        by_cases hTX : T ⊆ insert a X
        · rcases subset_insert_cases hTX with hT | ⟨T₀, hT₀, -, rfl⟩
          · exact hh0 T hT
          · have := congrFun hnh (insert a T₀)
            rw [zeta_insert_insert_zero c'', Pi.smul_apply, smul_eq_mul] at this
            exact (mul_eq_zero.mp this).resolve_left hn
        · have := congrFun hnh T
          rw [zeta_eq_zero_of_not c'' (fun h => hTX h.1), Pi.smul_apply, smul_eq_mul] at this
          exact (mul_eq_zero.mp this).resolve_left hn
      have hfe : f = zeta (insert a X) 0 c' := by
        have := congrArg (· + zeta (insert a X) 0 c') this
        simpa [h] using this
      rw [hfe]; exact zeta_mem_gsub hc'
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hshift : shiftv a c'' ∈ lowSub j := by
      intro S hS
      simp only [shiftv]
      split_ifs with haS
      · rfl
      · exact hc'' _ (by rw [card_insert_of_notMem haS]; omega)
    have hnh₁ : n • h₁ = zeta X s c'' + zeta X s (shiftv a c'') := by
      ext T₀
      simp only [h₁, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      split_ifs with hT₀
      · rw [← zeta_insert_insert ha c'' hT₀, ← hnh]; rfl
      · rw [mul_zero, zeta_eq_zero_of_not c'' (fun h => hT₀ h.1),
          zeta_eq_zero_of_not _ (fun h => hT₀ h.1), add_zero]
    have hdesc : zeta X s c'' ∈ Gsub X j s :=
      descend (ih j s) (by omega) hc'' hz0
    obtain ⟨e, he, hef⟩ := ih j s n h₁ hn
      (hnh₁ ▸ Submodule.add_mem _ hdesc (zeta_mem_gsub hshift))
    -- Step D
    let e' : Finset α → ℤ := fun S => if a ∈ S then e (S.erase a) else 0
    have he' : e' ∈ lowSub (j + 1) := by
      intro S hS
      simp only [e']
      split_ifs with haS
      · exact he _ (by rw [card_erase_of_mem haS]; omega)
      · rfl
    have hhe : h = zeta (insert a X) (s + 1) e' := by
      ext T
      by_cases hTX : T ⊆ insert a X
      · rcases subset_insert_cases hTX with hT | ⟨T₀, hT₀, haT₀, rfl⟩
        · rw [hh0 T hT, zeta_insert_of_subset e' hT, zeta_apply]
          split_ifs with hT'
          · refine (sum_eq_zero fun S hS => ?_).symm
            have : a ∉ S := fun h => ha (hT ((mem_powerset.mp hS) h))
            simp [e', this]
          · rfl
        · rw [zeta_insert_insert ha e' hT₀]
          have h1 : zeta X s e' = 0 := by
            rw [zeta_congr (d := 0)]
            · simp
            · intro S hS
              have : a ∉ S := fun h => ha (hS h)
              simp [e', this]
          have h2 : zeta X s (shiftv a e') = zeta X s e := by
            apply zeta_congr
            intro S hS
            have : a ∉ S := fun h => ha (hS h)
            simp [shiftv, e', this, erase_insert this]
          rw [h1, h2, hef]
          simp [h₁, hT₀]
      · have := congrFun hnh T
        rw [zeta_eq_zero_of_not c'' (fun h => hTX h.1), Pi.smul_apply, smul_eq_mul] at this
        rw [(mul_eq_zero.mp this).resolve_left hn, zeta_eq_zero_of_not e' (fun h => hTX h.1)]
    have hfe : f = zeta (insert a X) (s + 1) (c' + e') := by
      rw [map_add, ← hhe]; simp [h]
    rw [hfe]
    exact zeta_mem_gsub (Submodule.add_mem _ hc' he')

end ColouredSand.NumberOfFactors
