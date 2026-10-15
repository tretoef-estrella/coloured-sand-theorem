module

public import RequestProject.CubeLaplacian.Basic

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part A — Lemma 2.1

The products `s_S` in `R = ℤ[G]`: (A1)–(A3), and the basis (A4).
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open Finset

lemma e_add_self (n : ℕ) (i : Fin n) : e n i + e n i = 0 := by
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  funext k
  exact h2 _

lemma x_mul_self (n : ℕ) (j : Fin n) : x n j * x n j = 1 := by
  rw [x, AddMonoidAlgebra.single_mul_single, e_add_self, one_mul]
  rfl

/-- Part A, (A1): `s_j · s_j = 2 s_j`. -/
theorem A1 (n : ℕ) (j : Fin n) : s n j * s n j = 2 * s n j := by
  simp only [s]
  have := x_mul_self n j
  linear_combination this

/-- Part A, (A2) (Lemma 2.1): `s_j · s_S = s_{S ∪ {j}}` if `j ∉ S`, and `s_j · s_S = 2 s_S` if
`j ∈ S`. -/
theorem A2 (n : ℕ) (j : Fin n) (S : Finset (Fin n)) :
    (j ∉ S → s n j * sS n S = sS n (S ∪ {j})) ∧ (j ∈ S → s n j * sS n S = 2 * sS n S) := by
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · rw [Finset.union_comm, ← Finset.insert_eq, sS, sS, Finset.prod_insert hj]
  · rw [sS, ← Finset.mul_prod_erase S _ hj, ← mul_assoc, A1, mul_assoc]

lemma A2_not_mem (n : ℕ) {j : Fin n} {S : Finset (Fin n)} (hj : j ∉ S) :
    s n j * sS n S = sS n (S ∪ {j}) := (A2 n j S).1 hj

lemma A2_mem (n : ℕ) {j : Fin n} {S : Finset (Fin n)} (hj : j ∈ S) :
    s n j * sS n S = 2 * sS n S := (A2 n j S).2 hj

lemma two_mul_eq_zsmul {n : ℕ} (y : R n) : 2 * y = (2 : ℤ) • y := by
  rw [zsmul_eq_mul]; norm_num

/-- Part A, (A3): `σ · s_S = Σ_{j ∉ S} s_{S ∪ {j}} + 2|S| · s_S` (that is, `σ = U + 2D` on the
elements `s_S`). -/
theorem A3 (n : ℕ) (S : Finset (Fin n)) :
    sigma n * sS n S = ∑ j ∈ Sᶜ, sS n (S ∪ {j}) + (2 * (S.card : ℤ)) • sS n S := by
  rw [sigma, Finset.sum_mul, ← Finset.sum_compl_add_sum S]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => A2_not_mem n (Finset.mem_compl.1 hj)
  · rw [Finset.sum_congr rfl fun j hj => A2_mem n hj, Finset.sum_const, two_mul_eq_zsmul,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, mul_comm]

/-- The `ℤ`-span of the family `(s_S)`. -/
abbrev spanS (n : ℕ) : Submodule ℤ (R n) := Submodule.span ℤ (Set.range (sS n))

lemma sS_mem_spanS (n : ℕ) (S : Finset (Fin n)) : sS n S ∈ spanS n :=
  Submodule.subset_span ⟨S, rfl⟩

lemma s_mul_mem_spanS (n : ℕ) (j : Fin n) {p : R n} (hp : p ∈ spanS n) :
    s n j * p ∈ spanS n := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    by_cases hj : j ∈ S
    · rw [A2_mem n hj, two_mul_eq_zsmul]
      exact Submodule.smul_mem _ _ (sS_mem_spanS n S)
    · rw [A2_not_mem n hj]
      exact sS_mem_spanS n _
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

lemma single_one_mem_spanS (n : ℕ) (g : G n) :
    AddMonoidAlgebra.single g (1 : ℤ) ∈ spanS n := by
  have key : ∀ (h : G n) (i : Fin n), AddMonoidAlgebra.single h (1 : ℤ) ∈ spanS n →
      AddMonoidAlgebra.single (e n i + h) (1 : ℤ) ∈ spanS n := by
    intro h i hh
    have : AddMonoidAlgebra.single (e n i + h) (1 : ℤ) =
        AddMonoidAlgebra.single h 1 - s n i * AddMonoidAlgebra.single h 1 := by
      rw [s, x, sub_mul, one_mul, AddMonoidAlgebra.single_mul_single, one_mul, sub_sub_cancel]
    rw [this]
    exact Submodule.sub_mem _ hh (s_mul_mem_spanS n i hh)
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hs : ∀ t : Finset (Fin n),
      AddMonoidAlgebra.single (∑ i ∈ t, Pi.single i (g i)) (1 : ℤ) ∈ spanS n := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have : sS n ∅ = AddMonoidAlgebra.single (∑ i ∈ (∅ : Finset (Fin n)), Pi.single i (g i)) 1 := by
        simp [sS]; rfl
      rw [← this]; exact sS_mem_spanS n ∅
    | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      rcases h01 (g a) with h | h
      · rw [h, Pi.single_zero, zero_add]; exact ih
      · rw [h]; exact key _ a ih
  have := hs Finset.univ
  rwa [Finset.univ_sum_single] at this

lemma spanS_eq_top (n : ℕ) : spanS n = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun f => ?_
  induction f using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single g c =>
    have : (Finsupp.single g c : R n) = c • AddMonoidAlgebra.single g (1 : ℤ) := by
      rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ c (single_one_mem_spanS n g)

lemma card_G (n : ℕ) : Fintype.card (G n) = Fintype.card (Finset (Fin n)) := by
  simp [Fintype.card_finset, ZMod.card]

lemma linearIndependent_sS (n : ℕ) : LinearIndependent ℤ (sS n) := by
  set φ : (Finset (Fin n) →₀ ℤ) →ₗ[ℤ] R n := Finsupp.linearCombination ℤ (sS n)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact spanS_eq_top n
  let ε : R n ≃ₗ[ℤ] (Finset (Fin n) →₀ ℤ) :=
    (toFun n).trans ((LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivOfCardEq (card_G n)).symm).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Finset (Fin n))).symm)
  have hinj : Function.Injective (ε.toLinearMap ∘ₗ φ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (ε.surjective.comp hsurj)
  intro a b hab
  apply hinj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [show φ a = φ b from hab]

/-- Part A, (A4): the basis `(s_S)_{S ⊆ Fin n}` of `R` over `ℤ`. -/
def sBasis (n : ℕ) : Module.Basis (Finset (Fin n)) ℤ (R n) :=
  Module.Basis.mk (linearIndependent_sS n) (spanS_eq_top n).ge

@[simp] lemma sBasis_apply (n : ℕ) (S : Finset (Fin n)) : sBasis n S = sS n S := by
  simp [sBasis]

/-- Part A, (A4): the family `(s_S)_{S ⊆ Fin n}` is a `ℤ`-basis of `R`: there is a
`Basis (Finset (Fin n)) ℤ R` whose `S`-th vector is `s_S`. -/
theorem A4 (n : ℕ) : ∃ b : Module.Basis (Finset (Fin n)) ℤ (R n), ∀ S, b S = sS n S :=
  ⟨sBasis n, sBasis_apply n⟩

end CubeLaplacian
