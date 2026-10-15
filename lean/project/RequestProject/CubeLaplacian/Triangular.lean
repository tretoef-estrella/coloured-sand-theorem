module

public import RequestProject.CubeLaplacian.Laplacian

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part C, (C1) and (C2)

Coefficients in the basis `(s_S)` of (A4) are read through `(sBasis n).repr`.
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open Finset

lemma repr_sS (n : ℕ) (S U : Finset (Fin n)) :
    (sBasis n).repr (sS n S) U = if S = U then 1 else 0 := by
  rw [← sBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]

lemma repr_sigma_sS (n : ℕ) (S U : Finset (Fin n)) :
    (sBasis n).repr (sigma n * sS n S) U =
      ∑ j ∈ Sᶜ, (if S ∪ {j} = U then 1 else 0) + if S = U then 2 * (S.card : ℤ) else 0 := by
  rw [A3, map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.finset_sum_apply,
    Finsupp.smul_apply]
  simp only [repr_sS, smul_eq_mul, mul_ite, mul_one, mul_zero]

lemma union_singleton_ne_of_card_le {n : ℕ} {S U : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (hU : U.card ≤ S.card) : S ∪ {j} ≠ U := by
  rintro rfl
  have hsub : S ⊆ S ∪ {j} := Finset.subset_union_left
  have := Finset.eq_of_subset_of_card_le hsub hU
  exact hj (this ▸ Finset.mem_union_right S (Finset.mem_singleton_self j))

/-- The image `σ · s_S` has nonzero `s_U`-coefficient only for `U = S` or `|S| < |U|`. -/
lemma repr_sigma_sS_ne_zero (n : ℕ) {S U : Finset (Fin n)}
    (h : (sBasis n).repr (sigma n * sS n S) U ≠ 0) : U = S ∨ S.card < U.card := by
  by_contra hc
  push_neg at hc
  apply h
  rw [repr_sigma_sS, if_neg (Ne.symm hc.1), add_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg (union_singleton_ne_of_card_le (Finset.mem_compl.1 hj) hc.2)]

lemma repr_sigma_sS_self (n : ℕ) (S : Finset (Fin n)) :
    (sBasis n).repr (sigma n * sS n S) S = 2 * (S.card : ℤ) := by
  rw [repr_sigma_sS, if_pos rfl]
  rw [Finset.sum_eq_zero fun j hj => if_neg
    (union_singleton_ne_of_card_le (Finset.mem_compl.1 hj) le_rfl), zero_add]

lemma repr_sigma_mul (n : ℕ) (f : R n) (U : Finset (Fin n)) :
    (sBasis n).repr (sigma n * f) U =
      ∑ T, (sBasis n).repr f T * (sBasis n).repr (sigma n * sS n T) U := by
  conv_lhs => rw [← (sBasis n).sum_repr f]
  rw [Finset.mul_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [mul_smul_comm, map_zsmul, Finsupp.smul_apply, smul_eq_mul, sBasis_apply]

/-- Part C, (C1): the coefficient of `s_∅` in `σ · f` is `0` for every `f ∈ R` (in the basis of
(A4)). -/
theorem C1 (n : ℕ) (f : R n) : (sBasis n).repr (sigma n * f) ∅ = 0 := by
  rw [repr_sigma_mul]
  refine Finset.sum_eq_zero fun T _ => ?_
  by_cases h : (sBasis n).repr (sigma n * sS n T) ∅ = 0
  · rw [h, mul_zero]
  · rcases repr_sigma_sS_ne_zero n h with h' | h'
    · subst h'
      rw [repr_sigma_sS_self]; simp
    · simp at h'

lemma mem_Rplus_iff (n : ℕ) (f : R n) : f ∈ Rplus n ↔ (sBasis n).repr f ∅ = 0 := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨S, hS, rfl⟩ := hy
      rw [repr_sS, if_neg hS]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, Finsupp.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [map_zsmul, Finsupp.smul_apply, ha, smul_zero]
  · intro hf
    rw [← (sBasis n).sum_repr f]
    refine Submodule.sum_mem _ fun T _ => ?_
    by_cases hT : T = ∅
    · subst hT; rw [hf, zero_smul]; exact Submodule.zero_mem _
    · rw [sBasis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, hT, rfl⟩)

/-- Part C, (C1), second form: `range (σ · −) ⊆ R_+`. -/
theorem C1_range (n : ℕ) : LinearMap.range (mulSigma n) ≤ Rplus n := by
  rintro _ ⟨f, rfl⟩
  exact (mem_Rplus_iff n _).2 (C1 n f)

lemma sS_mem_Rplus (n : ℕ) {S : Finset (Fin n)} (hS : S ≠ ∅) : sS n S ∈ Rplus n :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Part C, (C2): `σ · −` maps `R_+` to `R_+` (indeed it maps all of `R` into `R_+`, by (C1)). -/
theorem C2_maps (n : ℕ) : (Rplus n).map (mulSigma n) ≤ Rplus n :=
  le_trans LinearMap.map_le_range (C1_range n)

lemma sigma_mul_mem_Rplus (n : ℕ) (f : R n) : sigma n * f ∈ Rplus n :=
  C1_range n ⟨f, rfl⟩

/-- Part C, (C2): the restriction `σ_+ : R_+ → R_+` of `σ · −` to `R_+`. -/
def sigmaPlus (n : ℕ) : Rplus n →ₗ[ℤ] Rplus n :=
  (mulSigma n).restrict fun f _ => sigma_mul_mem_Rplus n f

/-- Part C, (C2): in the basis `(s_S)` ordered by `|S|`, the matrix of `σ · −` is lower triangular:
the `s_U`-coefficient of `σ · s_S` vanishes unless `U = S` or `|S| < |U|`. (Stated for all `S`, in
particular for the basis `{s_S : S ≠ ∅}` of `R_+`.) -/
theorem C2_triangular (n : ℕ) (S U : Finset (Fin n))
    (h : (sBasis n).repr (sigma n * sS n S) U ≠ 0) : U = S ∨ S.card < U.card :=
  repr_sigma_sS_ne_zero n h

/-- Part C, (C2): the diagonal entries are `2|S|`, nonzero for `S ≠ ∅`. -/
theorem C2_diagonal (n : ℕ) (S : Finset (Fin n)) :
    (sBasis n).repr (sigma n * sS n S) S = 2 * (S.card : ℤ) ∧
      (S ≠ ∅ → 2 * (S.card : ℤ) ≠ 0) := by
  refine ⟨repr_sigma_sS_self n S, fun hS => ?_⟩
  have : S.card ≠ 0 := by simpa using hS
  positivity

lemma eq_zero_of_mem_Rplus_of_sigma_mul_eq_zero (n : ℕ) {f : R n} (hf : f ∈ Rplus n)
    (h0 : sigma n * f = 0) : f = 0 := by
  by_contra hne
  set c := (sBasis n).repr f with hc
  have hc0 : c ≠ 0 := fun h => hne ((sBasis n).repr.map_eq_zero_iff.1 h)
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image c.support Finset.card
    (Finsupp.support_nonempty_iff.2 hc0)
  have hcS : c S ≠ 0 := Finsupp.mem_support_iff.1 hS
  have hSne : S ≠ ∅ := by
    rintro rfl; exact hcS ((mem_Rplus_iff n f).1 hf)
  have key : (sBasis n).repr (sigma n * f) S = c S * (2 * (S.card : ℤ)) := by
    rw [repr_sigma_mul, ← repr_sigma_sS_self n S]
    refine Finset.sum_eq_single S (fun T _ hTS => ?_) (by simp)
    by_cases hcT : c T = 0
    · rw [hcT, zero_mul]
    · by_cases hr : (sBasis n).repr (sigma n * sS n T) S = 0
      · rw [hr, mul_zero]
      · rcases repr_sigma_sS_ne_zero n hr with h' | h'
        · exact absurd h'.symm hTS
        · have := hmin T (Finsupp.mem_support_iff.2 hcT)
          omega
  rw [h0, map_zero, Finsupp.zero_apply] at key
  exact mul_ne_zero hcS ((C2_diagonal n S).2 hSne) key.symm

/-- Part C, (C2): `σ · −` is injective on `R_+`. -/
theorem C2_injective (n : ℕ) : Function.Injective (sigmaPlus n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  exact eq_zero_of_mem_Rplus_of_sigma_mul_eq_zero n f.2 (congrArg Subtype.val hf)

lemma Rplus_fg (n : ℕ) : Module.Finite ℤ (Rplus n) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.toFinite _))

/-- A submodule `W` of `R_+` containing every `σ · s_S` (`S ≠ ∅`) has finite index. -/
lemma finite_quotient_of_sigma_mem (n : ℕ) (W : Submodule ℤ (Rplus n))
    (hW : ∀ S, S ≠ ∅ → (⟨sigma n * sS n S, sigma_mul_mem_Rplus n _⟩ : Rplus n) ∈ W) :
    Finite (Rplus n ⧸ W) := by
  haveI := Rplus_fg n
  set tors := Submodule.torsion ℤ (Rplus n ⧸ W)
  have smul_mem : ∀ (c : ℤ) (z : Rplus n ⧸ W), c ≠ 0 → c • z ∈ tors → z ∈ tors := by
    intro c z hc hz
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hz
    refine (Submodule.mem_torsion_iff _).2 ⟨⟨(a : ℤ) * c, mem_nonZeroDivisors_of_ne_zero
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero a) hc)⟩, ?_⟩
    rw [Submonoid.mk_smul, mul_smul]; exact ha
  have hgen : ∀ k S (hS : S ≠ ∅), n - S.card = k →
      W.mkQ ⟨sS n S, sS_mem_Rplus n hS⟩ ∈ tors := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro S hS hk
      have hsum : (⟨sigma n * sS n S, sigma_mul_mem_Rplus n _⟩ : Rplus n) =
          ∑ j ∈ Sᶜ.attach, (⟨sS n (S ∪ {j.1}), sS_mem_Rplus n (by simp)⟩ : Rplus n) +
            (2 * (S.card : ℤ)) • ⟨sS n S, sS_mem_Rplus n hS⟩ := by
        apply Subtype.ext
        simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, A3]
        rw [Finset.sum_attach Sᶜ (fun j => sS n (S ∪ {j}))]
      have h0 : W.mkQ ⟨sigma n * sS n S, sigma_mul_mem_Rplus n _⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (hW S hS)
      rw [hsum, map_add, map_sum, map_zsmul, add_eq_zero_iff_neg_eq] at h0
      refine smul_mem _ _ ((C2_diagonal n S).2 hS) ?_
      rw [← h0]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_)
      have hj := Finset.mem_compl.1 j.2
      have hcard : (S ∪ {j.1}).card = S.card + 1 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hj),
          Finset.card_singleton]
      have hle : (S ∪ {j.1}).card ≤ n := by
        simpa using Finset.card_le_univ (S ∪ {j.1})
      exact ih _ (by omega) _ (by simp) rfl
  have hall : ∀ y : Rplus n, W.mkQ y ∈ tors := by
    intro y
    have hle : Rplus n ≤ (tors.comap W.mkQ).map (Rplus n).subtype := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨S, hS, rfl⟩
      exact ⟨⟨sS n S, sS_mem_Rplus n hS⟩, hgen _ S hS rfl, rfl⟩
    obtain ⟨y', hy', hyy⟩ := hle y.2
    have : y' = y := Subtype.ext hyy
    rw [← this]; exact hy'
  refine Module.finite_of_fg_torsion _ fun z => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W z
  exact (Submodule.mem_torsion_iff _).1 (hall y)

/-- Part C, (C2): `range (σ · −) ⊇ σ · R_+`, and `σ · R_+` has finite index in `R_+`. -/
theorem C2_finiteIndex (n : ℕ) :
    LinearMap.range (sigmaPlus n) ≤ (LinearMap.range (mulSigma n)).comap (Rplus n).subtype ∧
      Finite (Rplus n ⧸ LinearMap.range (sigmaPlus n)) := by
  refine ⟨?_, finite_quotient_of_sigma_mem n _ fun S hS => ⟨⟨sS n S, sS_mem_Rplus n hS⟩, rfl⟩⟩
  rintro _ ⟨f, rfl⟩
  exact ⟨f.1, rfl⟩

end CubeLaplacian
