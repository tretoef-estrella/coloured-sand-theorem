module

public import RequestProject.GoldenMatching.Dancers

/-!
# Part C of `C4_golden_matching.md`: Lemma C1 (the complement) and Lemma C2 (the cost of a
bijection)

Encodings (namespace `GoldenMatching`), in the setting of Part B (see `Dancers.lean`):

* The complement `D ↦ I ∖ D` is `fun D => I \ D`; "a bijection from `L_r` onto `F_r`" is
  `Set.BijOn (fun D => I \ D) (Lr I r) (Fr I r)`.
* `o_{I∖D} = o_I − o_D` is stated in `ℕ`; the subtraction does not truncate because `D ⊆ I`
  (a companion statement `o_{I∖D} + o_D = o_I` is also given).
* `rank(I ∖ D) = N − 1 − rank(D)` is stated in `ℕ` with `N = 2 ^ #I`; it does not truncate since
  `rank(D) ≤ N − 1` (`rank_lt`).
* The rulers are `R_μ := Rulers.ruler k I α μ` (piece C3), with an integer `α` and `μ : ℕ`
  (so `μ ≥ 0` is automatic), and `K = 2^k` is written `2 ^ k`.
* `cHat k I α μ a b` is the **normalized cost** `ĉ(a, b) := R_μ(a) − R_{μ+K}(b) + γ(a ∖ b)`.
* `xVal k I α μ D` is `x_D := R_μ(D) − R_{μ+K}(I ∖ D)`.
* `U k I α μ r` is `U(r) := Σ_{D∈L_r} x_D`.
* A bijection `β : L_r → F_r` is an equivalence `β : Lr I r ≃ Fr I r`; sums over `D ∈ L_r` are
  sums over the subtype `Lr I r` (or, equivalently, over the `Finset` `Lr I r`).
-/

@[expose] public section

namespace GoldenMatching

open Finset Rulers

/-! ### Lemma C1 -/

/-- Auxiliary: the bit positions of `I ∖ D` are the complement of those of `D`. -/
lemma idx_compl {I : Finset ℕ} {τ : ℕ → ℕ} (hτI : (range #I).image τ = I) (D : Finset ℕ) :
    idx τ #I (I \ D) = range #I \ idx τ #I D := by
  ext j
  simp only [idx, mem_filter, mem_sdiff, mem_range]
  constructor
  · rintro ⟨hj, -, hD⟩; exact ⟨hj, fun h => hD h.2⟩
  · rintro ⟨hj, h⟩
    refine ⟨hj, ?_, fun hD => h ⟨hj, hD⟩⟩
    rw [← hτI]; exact mem_image_of_mem τ (mem_range.2 hj)

/-- Auxiliary: `rank(D) ≤ N − 1`. -/
lemma rank_lt {I D : Finset ℕ} (hD : D ⊆ I) : rank I D < 2 ^ #I := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  rw [rank_eq_pos hτ hτI hD]; exact pos_lt D

/-- **Lemma C1** of `C4_golden_matching.md`, first claim: for a dancer `D`,
`o_{I∖D} = o_I − o_D` (in `ℕ`; no truncation since `D ⊆ I`). -/
theorem lemma_C1_oE {I D : Finset ℕ} (hD : D ⊆ I) : oE (I \ D) = oE I - oE D := by
  have := oE_sdiff hD; omega

/-- **Lemma C1** of `C4_golden_matching.md`, first claim in additive form:
`o_{I∖D} + o_D = o_I`. -/
theorem lemma_C1_oE_add {I D : Finset ℕ} (hD : D ⊆ I) : oE (I \ D) + oE D = oE I :=
  oE_sdiff hD

/-- **Lemma C1** of `C4_golden_matching.md`, second claim: for dancers `D, D'`,
`o_D < o_{D'}` if and only if `o_{I∖D'} < o_{I∖D}`. -/
theorem lemma_C1_lt {I D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I) :
    oE D < oE D' ↔ oE (I \ D') < oE (I \ D) := by
  have h1 := oE_sdiff hD
  have h2 := oE_sdiff hD'
  omega

/-- **Lemma C1** of `C4_golden_matching.md`, third claim: for a dancer `D`,
`rank(I ∖ D) = N − 1 − rank(D)` with `N = 2^{|I|}`. -/
theorem lemma_C1_rank {I D : Finset ℕ} (hD : D ⊆ I) : rank I (I \ D) = 2 ^ #I - 1 - rank I D := by
  obtain ⟨τ, hτ, hτI⟩ := exists_enum I
  rw [rank_eq_pos hτ hτI hD, rank_eq_pos hτ hτI sdiff_subset, idx_compl hτI]
  have h1 := oE_sdiff (idx_subset τ #I D)
  have h2 := oE_range #I
  omega

/-- **Lemma C1** of `C4_golden_matching.md`, fourth claim: `D ↦ I ∖ D` is a bijection from
`L_r` onto `F_r` (for every `r`). -/
theorem lemma_C1_bijOn (I : Finset ℕ) (r : ℕ) :
    Set.BijOn (fun D => I \ D) (Lr I r : Set (Finset ℕ)) (Fr I r : Set (Finset ℕ)) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' h => ?_, fun E hE => ?_⟩
  · simp only [Lr, coe_filter, mem_powerset, Set.mem_setOf_eq] at hD
    simp only [Fr, coe_filter, mem_powerset, Set.mem_setOf_eq]
    have := rank_lt hD.1
    refine ⟨sdiff_subset, ?_⟩
    rw [lemma_C1_rank hD.1]; omega
  · simp only [Lr, coe_filter, mem_powerset, Set.mem_setOf_eq] at hD hD'
    have := congrArg (fun E => I \ E) h
    simpa [Finset.sdiff_sdiff_eq_self hD.1, Finset.sdiff_sdiff_eq_self hD'.1] using this
  · simp only [Fr, coe_filter, mem_powerset, Set.mem_setOf_eq] at hE
    refine ⟨I \ E, ?_, Finset.sdiff_sdiff_eq_self hE.1⟩
    simp only [Lr, coe_filter, mem_powerset, Set.mem_setOf_eq]
    refine ⟨sdiff_subset, ?_⟩
    have := rank_lt hE.1
    rw [lemma_C1_rank hE.1]; omega

/-! ### Lemma C2 -/

/-- *Lemma C2* of `C4_golden_matching.md`: the **normalized cost**
`ĉ(a, b) := R_μ(a) − R_{μ+K}(b) + γ(a ∖ b)`, with `R_μ = Rulers.ruler k I α μ`, `K = 2^k` and
`γ = Rulers.gamma k I`. -/
def cHat (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (a b : Finset ℕ) : ℤ :=
  ruler k I α μ a - ruler k I α (μ + 2 ^ k) b + gamma k I (a \ b)

/-- *Lemma C2* of `C4_golden_matching.md`: `x_D := R_μ(D) − R_{μ+K}(I ∖ D)`. -/
def xVal (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (D : Finset ℕ) : ℤ :=
  ruler k I α μ D - ruler k I α (μ + 2 ^ k) (I \ D)

/-- *Part D* of `C4_golden_matching.md`: `U(r) := Σ_{D∈L_r} x_D`. -/
def U (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (r : ℕ) : ℤ :=
  ∑ D ∈ Lr I r, xVal k I α μ D

/-- **Lemma C2** (cost of a bijection) of `C4_golden_matching.md`: for every integer `α`, every
`μ ≥ 0` and every bijection `β : L_r → F_r` (no support condition),
`Σ_{D∈L_r} ĉ(D, β(D)) = Σ_{D∈L_r} x_D + Σ_{D∈L_r} γ(D ∖ β(D))`. -/
theorem lemma_C2 (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (r : ℕ) (β : Lr I r ≃ Fr I r) :
    ∑ D : Lr I r, cHat k I α μ D (β D) =
      ∑ D ∈ Lr I r, xVal k I α μ D + ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) := by
  have hcols : ∑ D : Lr I r, ruler k I α (μ + 2 ^ k) (β D) =
      ∑ D ∈ Lr I r, ruler k I α (μ + 2 ^ k) (I \ D) := by
    rw [Equiv.sum_comp β (fun E : Fr I r => ruler k I α (μ + 2 ^ k) E),
      sum_coe_sort (Fr I r) (fun E => ruler k I α (μ + 2 ^ k) E)]
    have hb := lemma_C1_bijOn I r
    exact (sum_nbij (fun D => I \ D) (fun D hD => hb.mapsTo hD) hb.injOn hb.surjOn
      (fun _ _ => rfl)).symm
  simp only [cHat, xVal, sum_add_distrib, sum_sub_distrib]
  rw [hcols, sum_coe_sort (Lr I r) (fun D => ruler k I α μ D)]

end GoldenMatching
