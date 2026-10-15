module

public import RequestProject.GoldenMatching.Binary
public import RequestProject.Rulers.Family

/-!
# Part B of `C4_golden_matching.md`: Theorem B (Theorem O for dancers)

Encodings (namespace `GoldenMatching`):

* The family is given by `k : ℕ` and `I : Finset ℕ`, with the hypothesis
  `I ⊆ {0, …, k − 1}` written `hI : ∀ t ∈ I, t < k`.  The dancers are the subsets `D ⊆ I`, i.e.
  the elements of `I.powerset`; there are `N = 2^{|I|}` of them, written `2 ^ #I`.
* `o_D` is `Rulers.oE D` (piece C3).
* `rank I D` is the file's `rank(D) := #{D' ⊆ I : o_{D'} < o_D}`.
* `Lr I r` is `L_r := {D ⊆ I : rank(D) ≥ N − r}` and `Fr I r` is
  `F_r := {D ⊆ I : rank(D) < r}`, both as `Finset (Finset ℕ)`.
* `IsGoldenArrow k I a b` is "the arrow `a → b` is golden": `b ⊆ a` and `γ(a ∖ b) = 0`, with
  `γ = Rulers.gamma k I` (piece C3).
* A bijection `β : L_r → F_r` is an equivalence `β : Lr I r ≃ Fr I r` of the corresponding
  subtypes; "exactly one" is existence plus uniqueness (any two agree on every row).

The proof follows the file: an increasing enumeration `τ` of `I` (`τ(j) = t_{j+1}`) identifies a
dancer `D` with `p(D) = Σ_{j : τ(j) ∈ D} 2^j`; this is a bijection onto `{0, …, N − 1}` which
preserves the order (via the colexicographic order), so `p(D) = rank(D)`, and it sends golden
arrows to golden images.  Theorem B is then Theorem A transported by `p`.
-/

@[expose] public section

namespace GoldenMatching

open Finset Rulers

/-! ### Definitions -/

/-- *Part B, Setting* of `C4_golden_matching.md`: the **rank** of a dancer `D`,
`rank(D) := #{D' ⊆ I : o_{D'} < o_D}`. -/
def rank (I D : Finset ℕ) : ℕ := #(I.powerset.filter (fun D' => oE D' < oE D))

/-- *Part B, Setting* of `C4_golden_matching.md`: `L_r := {D ⊆ I : rank(D) ≥ N − r}` (the last
`r` dancers), with `N = 2^{|I|}`. -/
def Lr (I : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun D => 2 ^ #I - r ≤ rank I D)

/-- *Part B, Setting* of `C4_golden_matching.md`: `F_r := {D ⊆ I : rank(D) < r}` (the first
`r` dancers). -/
def Fr (I : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun D => rank I D < r)

/-- *Part B, Setting* of `C4_golden_matching.md`: the arrow `a → b` is **golden** if `b ⊆ a`
and `γ(a ∖ b) = 0` (`γ = Rulers.gamma k I`, the gold of piece C3). -/
def IsGoldenArrow (k : ℕ) (I a b : Finset ℕ) : Prop := b ⊆ a ∧ gamma k I (a \ b) = 0

/-! ### Binary facts -/

lemma oE_injective : Function.Injective oE := geomSum_injective (le_refl 2)

lemma oE_Ico_add {j s : ℕ} (hjs : j ≤ s) : oE (Ico j s) + 2 ^ j = 2 ^ s := by
  have h1 := oE_range j
  have h2 := oE_range s
  have hu : range s = range j ∪ Ico j s := by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _) hjs]
  have hd : Disjoint (range j) (Ico j s) := by
    rw [disjoint_left]; intro x hx hx'; simp at hx hx'; omega
  rw [hu, oE_union hd] at h2
  omega

lemma oE_mono {A B : Finset ℕ} (h : A ⊆ B) : oE A ≤ oE B :=
  sum_le_sum_of_subset h

lemma le_oE_iff {A : Finset ℕ} {s j : ℕ} (hA : A ⊆ range s) (hjs : j ≤ s) :
    2 ^ s - 2 ^ j ≤ oE A ↔ Ico j s ⊆ A := by
  have hI := oE_Ico_add hjs
  constructor
  · intro h t ht
    by_contra htA
    have hsub : A ⊆ (range s).erase t := fun x hx => mem_erase.2 ⟨by rintro rfl; exact htA hx, hA hx⟩
    have h1 := oE_mono hsub
    have hts : t ∈ range s := by simp at ht ⊢; omega
    have h2 : oE ((range s).erase t) + 2 ^ t = oE (range s) := by
      unfold oE; exact sum_erase_add _ _ hts
    have h3 := oE_range s
    have h4 : 2 ^ j ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 ht).1
    omega
  · intro h
    have := oE_sdiff h
    omega

/-- Golden images in terms of bit sets. -/
lemma goldA_oE_iff {A A' : Finset ℕ} {s : ℕ} (hA : A ⊆ range s) :
    GoldA s (oE A) (oE A') ↔ (A' = A ∨ ∃ j < s, Ico j s ⊆ A ∧ A' = A \ Ico j s) := by
  unfold GoldA
  apply or_congr oE_injective.eq_iff
  apply exists_congr; intro j
  apply and_congr_right; intro hj
  rw [le_oE_iff hA hj.le]
  apply and_congr_right; intro hsub
  have h1 := oE_Ico_add hj.le
  have h2 := oE_sdiff hsub
  rw [← oE_injective.eq_iff]
  omega

/-! ### Transport by an increasing enumeration of `I` -/

/-- The bit positions of a dancer `D`: `{j < s : τ(j) ∈ D}`. -/
def idx (τ : ℕ → ℕ) (s : ℕ) (D : Finset ℕ) : Finset ℕ := (range s).filter (fun j => τ j ∈ D)

lemma idx_subset (τ : ℕ → ℕ) (s : ℕ) (D : Finset ℕ) : idx τ s D ⊆ range s := filter_subset _ _

lemma image_idx {I : Finset ℕ} {τ : ℕ → ℕ} (hτI : (range #I).image τ = I) {D : Finset ℕ}
    (hD : D ⊆ I) : (idx τ #I D).image τ = D := by
  ext t
  simp only [idx, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨j, ⟨_, hj⟩, rfl⟩; exact hj
  · intro ht
    have : t ∈ (range #I).image τ := by rw [hτI]; exact hD ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 this
    exact ⟨j, ⟨mem_range.1 hj, ht⟩, rfl⟩

lemma idx_image {τ : ℕ → ℕ} (hτ : StrictMono τ) {s : ℕ} {A : Finset ℕ} (hA : A ⊆ range s) :
    idx τ s (A.image τ) = A := by
  ext j
  simp only [idx, mem_filter, mem_range, mem_image, hτ.injective.eq_iff, exists_eq_right]
  exact ⟨fun h => h.2, fun h => ⟨mem_range.1 (hA h), h⟩⟩

lemma image_subset_range {I : Finset ℕ} {τ : ℕ → ℕ} (hτI : (range #I).image τ = I)
    {A : Finset ℕ} (hA : A ⊆ range #I) : A.image τ ⊆ I := by
  rw [← hτI]; exact image_subset_image hA

lemma exists_enum (I : Finset ℕ) : ∃ τ : ℕ → ℕ, StrictMono τ ∧ (range #I).image τ = I := by
  let e := I.orderEmbOfFin rfl
  let τ : ℕ → ℕ := fun j => if h : j < #I then e ⟨j, h⟩ else I.sup id + 1 + j
  have hle : ∀ t ∈ I, t ≤ I.sup id := fun t ht => le_sup (f := id) ht
  refine ⟨τ, strictMono_nat_of_lt_succ fun j => ?_, ?_⟩
  · by_cases h1 : j + 1 < #I
    · have h0 : j < #I := by omega
      simp only [τ, h1, h0, dif_pos]
      exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
    · by_cases h0 : j < #I
      · simp only [τ, h1, h0, dif_pos, dif_neg, not_false_eq_true]
        have := hle _ (show e ⟨j, h0⟩ ∈ I from I.orderEmbOfFin_mem rfl _)
        omega
      · simp only [τ, h1, h0, dif_neg, not_false_eq_true]; omega
  · ext t
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [τ, hj, dif_pos]
      exact I.orderEmbOfFin_mem rfl _
    · intro ht
      have : t ∈ Set.range e := by rw [range_orderEmbOfFin]; exact ht
      obtain ⟨⟨j, hj⟩, rfl⟩ := this
      exact ⟨j, hj, by simp [τ, hj]⟩

section Transport

variable {I : Finset ℕ} {τ : ℕ → ℕ}

lemma oE_lt_iff_idx (hτ : StrictMono τ) (hτI : (range #I).image τ = I) {D D' : Finset ℕ}
    (hD : D ⊆ I) (hD' : D' ⊆ I) :
    oE D < oE D' ↔ oE (idx τ #I D) < oE (idx τ #I D') := by
  conv_lhs => rw [← image_idx hτI hD, ← image_idx hτI hD']
  unfold oE
  rw [geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl, Colex.toColex_image_lt_toColex_image hτ]

lemma pos_lt (D : Finset ℕ) : oE (idx τ #I D) < 2 ^ #I :=
  oE_lt _ _ fun _ ht => mem_range.1 (idx_subset _ _ _ ht)

lemma pos_injOn (hτI : (range #I).image τ = I) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I)
    (h : oE (idx τ #I D) = oE (idx τ #I D')) : D = D' := by
  rw [← image_idx hτI hD, oE_injective h, image_idx hτI hD']

lemma pos_surj (hτI : (range #I).image τ = I) {m : ℕ} (hm : m < 2 ^ #I) :
    ∃ D ⊆ I, oE (idx τ #I D) = m := by
  obtain ⟨D, hD, h⟩ := surj_on_of_inj_on_of_card_le (s := I.powerset) (t := range (2 ^ #I))
    (fun D _ => oE (idx τ #I D)) (fun D _ => mem_range.2 (pos_lt D))
    (fun D D' hD hD' h => pos_injOn hτI (mem_powerset.1 hD) (mem_powerset.1 hD') h)
    (by simp) m (mem_range.2 hm)
  exact ⟨D, mem_powerset.1 hD, h.symm⟩

/-- `p(D) = rank(D)`. -/
lemma rank_eq_pos (hτ : StrictMono τ) (hτI : (range #I).image τ = I) {D : Finset ℕ}
    (hD : D ⊆ I) : rank I D = oE (idx τ #I D) := by
  unfold rank
  rw [filter_congr (q := fun D' => oE (idx τ #I D') < oE (idx τ #I D))
    (fun D' hD' => oE_lt_iff_idx hτ hτI (mem_powerset.1 hD') hD)]
  conv_rhs => rw [← card_range (oE (idx τ #I D))]
  refine card_bij (fun D' _ => oE (idx τ #I D')) (fun D' hD' => ?_) (fun D₁ h₁ D₂ h₂ h => ?_)
    (fun m hm => ?_)
  · exact mem_range.2 (mem_filter.1 hD').2
  · exact pos_injOn hτI (mem_powerset.1 (mem_filter.1 h₁).1) (mem_powerset.1 (mem_filter.1 h₂).1) h
  · have hm' := mem_range.1 hm
    obtain ⟨D', hD', h⟩ := pos_surj hτI (lt_trans hm' (pos_lt D))
    exact ⟨D', mem_filter.2 ⟨mem_powerset.2 hD', h ▸ hm'⟩, h⟩

lemma filter_tail (hτ : StrictMono τ) (hτI : (range #I).image τ = I) (j : ℕ) :
    I.filter (fun t => τ j ≤ t) = (Ico j #I).image τ := by
  ext t
  constructor
  · intro ht
    rw [mem_filter] at ht
    have : t ∈ (range #I).image τ := by rw [hτI]; exact ht.1
    obtain ⟨i, hi, rfl⟩ := mem_image.1 this
    exact mem_image.2 ⟨i, mem_Ico.2 ⟨hτ.le_iff_le.1 ht.2, mem_range.1 hi⟩, rfl⟩
  · intro ht
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ht
    rw [mem_Ico] at hi
    refine mem_filter.2 ⟨?_, hτ.monotone hi.1⟩
    rw [← hτI]; exact mem_image.2 ⟨i, mem_range.2 hi.2, rfl⟩

/-- Golden arrows are golden images, through `p`. -/
lemma isGoldenArrow_iff (hI : ∀ t ∈ I, t < k) (hτ : StrictMono τ)
    (hτI : (range #I).image τ = I) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I) :
    IsGoldenArrow k I D D' ↔ GoldA #I (oE (idx τ #I D)) (oE (idx τ #I D')) := by
  rw [goldA_oE_iff (idx_subset _ _ _)]
  set A := idx τ #I D with hAdef
  set A' := idx τ #I D' with hA'def
  have hA : A ⊆ range #I := idx_subset _ _ _
  have hA' : A' ⊆ range #I := idx_subset _ _ _
  have eD : A.image τ = D := image_idx hτI hD
  have eD' : A'.image τ = D' := image_idx hτI hD'
  rw [← eD, ← eD']
  unfold IsGoldenArrow
  rw [image_subset_image_iff hτ.injective, ← image_sdiff _ _ hτ.injective]
  have hΔ : (A \ A').image τ ⊆ I := image_subset_range hτI (sdiff_subset.trans hA)
  rw [lemma_5_1_b hI hΔ]
  constructor
  · rintro ⟨hsub, h⟩
    by_cases hemp : A \ A' = ∅
    · left; rw [sdiff_eq_empty_iff_subset] at hemp; exact subset_antisymm hsub hemp
    · right
      rcases h with h | h
      · exact absurd (image_eq_empty.1 h) hemp
      have hne : ((A \ A').image τ).Nonempty := (nonempty_iff_ne_empty.2 hemp).image τ
      obtain ⟨j, hj, hjm⟩ := mem_image.1 (minOr_mem (k := k) hne)
      have hjs : j < #I := mem_range.1 (hA (mem_sdiff.1 hj).1)
      rw [← hjm, filter_tail hτ hτI j] at h
      have heq : A \ A' = Ico j #I := image_injective hτ.injective h
      refine ⟨j, hjs, heq ▸ sdiff_subset, ?_⟩
      rw [← heq, Finset.sdiff_sdiff_eq_self hsub]
  · rintro (h | ⟨j, hj, hsub, h⟩) <;> rw [h]
    · exact ⟨subset_rfl, Or.inl (by simp)⟩
    · refine ⟨sdiff_subset, Or.inr ?_⟩
      rw [Finset.sdiff_sdiff_eq_self hsub]
      have hmin : minOr k ((Ico j #I).image τ) = τ j :=
        minOr_eq_of_mem (mem_image_of_mem τ (by simp [hj])) (fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_image.1 hx; exact hτ.monotone (mem_Ico.1 hi).1)
      rw [hmin, filter_tail hτ hτI j]

end Transport

/-- **Theorem B** (Theorem O for dancers, Theorem 6.2 of the source) of
`C4_golden_matching.md`: for every `k`, every `I ⊆ {0, …, k − 1}` and every `0 ≤ r ≤ N = 2^{|I|}`
there is exactly one bijection `β : L_r → F_r` all of whose arrows `D → β(D)` are golden.
"Exactly one" is stated as existence plus uniqueness (any two such bijections agree on every
row). -/
theorem theorem_B (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (r : ℕ) (hr : r ≤ 2 ^ #I) :
    (∃ β : Lr I r ≃ Fr I r, ∀ D : Lr I r, IsGoldenArrow k I D (β D)) ∧
      ∀ β β' : Lr I r ≃ Fr I r, (∀ D : Lr I r, IsGoldenArrow k I D (β D)) →
        (∀ D : Lr I r, IsGoldenArrow k I D (β' D)) → ∀ D, β D = β' D := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  have memL : ∀ D, D ∈ Lr I r ↔ D ⊆ I ∧ 2 ^ #I - r ≤ oE (idx τ #I D) := by
    intro D; unfold Lr; rw [mem_filter, mem_powerset]
    exact and_congr_right fun hD => by rw [rank_eq_pos hτ hτI hD]
  have memF : ∀ D, D ∈ Fr I r ↔ D ⊆ I ∧ oE (idx τ #I D) < r := by
    intro D; unfold Fr; rw [mem_filter, mem_powerset]
    exact and_congr_right fun hD => by rw [rank_eq_pos hτ hτI hD]
  let eL : Lr I r ≃ (Ico (2 ^ #I - r) (2 ^ #I) : Finset ℕ) := Equiv.ofBijective
    (fun D => ⟨oE (idx τ #I D), mem_Ico.2 ⟨((memL D).1 D.2).2, pos_lt _⟩⟩)
    ⟨fun D D' h => Subtype.ext (pos_injOn hτI ((memL D).1 D.2).1 ((memL D').1 D'.2).1
        (congrArg Subtype.val h)),
      fun p => by
        obtain ⟨D, hD, h⟩ := pos_surj hτI (mem_Ico.1 p.2).2
        exact ⟨⟨D, (memL D).2 ⟨hD, h ▸ (mem_Ico.1 p.2).1⟩⟩, Subtype.ext h⟩⟩
  let eF : Fr I r ≃ (range r : Finset ℕ) := Equiv.ofBijective
    (fun D => ⟨oE (idx τ #I D), mem_range.2 ((memF D).1 D.2).2⟩)
    ⟨fun D D' h => Subtype.ext (pos_injOn hτI ((memF D).1 D.2).1 ((memF D').1 D'.2).1
        (congrArg Subtype.val h)),
      fun p => by
        obtain ⟨D, hD, h⟩ := pos_surj hτI (lt_of_lt_of_le (mem_range.1 p.2) hr)
        exact ⟨⟨D, (memF D).2 ⟨hD, h ▸ mem_range.1 p.2⟩⟩, Subtype.ext h⟩⟩
  have hgold : ∀ (D : Lr I r) (E : Fr I r),
      IsGoldenArrow k I D E ↔ IsGoldenImage #I (eL D) (eF E) := by
    intro D E
    change _ ↔ IsGoldenImage #I (oE (idx τ #I D)) (oE (idx τ #I E))
    rw [isGoldenImage_iff_goldA (pos_lt _)]
    exact isGoldenArrow_iff hI hτ hτI ((memL D).1 D.2).1 ((memF E).1 E.2).1
  obtain ⟨⟨β₀, hβ₀⟩, huniq⟩ := theorem_A #I r hr
  refine ⟨⟨eL.trans (β₀.trans eF.symm), fun D => ?_⟩, fun β β' hβ hβ' D => ?_⟩
  · rw [hgold]; simpa using hβ₀ (eL D)
  · have key : ∀ γ : Lr I r ≃ Fr I r, (∀ D : Lr I r, IsGoldenArrow k I D (γ D)) →
        ∀ p : (Ico (2 ^ #I - r) (2 ^ #I) : Finset ℕ),
          IsGoldenImage #I p ((eL.symm.trans (γ.trans eF)) p) := by
      intro γ hγ p
      have := (hgold (eL.symm p) (γ (eL.symm p))).1 (hγ _)
      simpa using this
    have := huniq _ _ (key β hβ) (key β' hβ') (eL D)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at this
    exact eF.injective this

end GoldenMatching
