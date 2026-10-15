module

public import Mathlib

/-!
# The Cauchy–Binet formula (used in Lemma A1 of `C5_divisors_theorem_65.md`)

Mathlib does not contain the Cauchy–Binet formula, so it is proved here.

## Encoding

* An `r`-element subset `S ⊆ {0, …, n − 1}` is a `Finset (Fin n)` with `S.card = r`; its
  elements in increasing order are `S.orderEmbOfFin h : Fin r ↪o Fin n`.
* For `A : r × n` and `B : n × r`, `A.submatrix id e_S` is the `r × r` matrix `A[·, S]` (columns
  of `S` in increasing order) and `B.submatrix e_S id` is `B[S, ·]`.
-/

@[expose] public section

namespace Divisors

open Finset Matrix Equiv

variable {R : Type*} [CommRing R]

/-- An injective map `f : Fin r → Fin n` is the increasing enumeration of its image composed
with a permutation of `Fin r`. (Auxiliary for Part A of `C5_divisors_theorem_65.md`.) -/
theorem exists_perm_of_injective {r n : ℕ} {f : Fin r → Fin n} (hf : Function.Injective f)
    (hS : (univ.image f).card = r) :
    ∃ σ : Perm (Fin r), ∀ i, (univ.image f).orderEmbOfFin hS (σ i) = f i := by
  set S := univ.image f
  let g : Fin r → Fin r := fun i =>
    (S.orderIsoOfFin hS).symm ⟨f i, mem_image_of_mem f (mem_univ i)⟩
  have hg : ∀ i, S.orderEmbOfFin hS (g i) = f i := by
    intro i
    rw [← coe_orderIsoOfFin_apply]
    simp [g]
  have ginj : Function.Injective g := by
    intro i j h
    apply hf
    rw [← hg i, ← hg j, h]
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), hg⟩

/-- The image of an injective `f : Fin r → Fin n` has `r` elements. (Auxiliary for Part A of
`C5_divisors_theorem_65.md`.) -/
theorem card_image_of_injective_fin {r n : ℕ} {f : Fin r → Fin n}
    (hf : Function.Injective f) : (univ.image f).card = r := by
  rw [card_image_of_injective _ hf]; simp

/-- Step 1 of Cauchy–Binet: expansion of `det (A * B)` over all maps `p : Fin r → Fin n`.
(Auxiliary for Lemma A1 of `C5_divisors_theorem_65.md`.) -/
theorem det_mul_eq_sum_fun {r n : ℕ} (A : Matrix (Fin r) (Fin n) R)
    (B : Matrix (Fin n) (Fin r) R) :
    det (A * B) = ∑ p : Fin r → Fin n, det (A.submatrix id p) * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun σ _ => ?_
  simp [prod_mul_distrib, mul_assoc]

/-- **Cauchy–Binet formula** (used in the proof of Lemma A1 of `C5_divisors_theorem_65.md`):
for `A : r × n` and `B : n × r`,
`det (A B) = Σ_{|S| = r} det A[·, S] · det B[S, ·]`. -/
theorem cauchy_binet {r n : ℕ} (A : Matrix (Fin r) (Fin n) R) (B : Matrix (Fin n) (Fin r) R) :
    det (A * B) = ∑ S : {S : Finset (Fin n) // S.card = r},
      det (A.submatrix id (S.1.orderEmbOfFin S.2)) *
        det (B.submatrix (S.1.orderEmbOfFin S.2) id) := by
  rw [det_mul_eq_sum_fun]
  set F : (Fin r → Fin n) → R := fun p => det (A.submatrix id p) * ∏ i, B (p i) i with hF
  -- only injective maps contribute
  have hzero : ∀ p : Fin r → Fin n, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    simp only [Function.Injective, not_forall] at hp
    obtain ⟨i, j, hij, hne⟩ := hp
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun k => by simp [hij]), zero_mul]
  rw [← sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hzero p hp))]
  -- rewrite the right-hand side as a sum over pairs `(S, σ)`
  have hrhs : ∀ S : {S : Finset (Fin n) // S.card = r},
      det (A.submatrix id (S.1.orderEmbOfFin S.2)) * det (B.submatrix (S.1.orderEmbOfFin S.2) id)
        = ∑ σ : Perm (Fin r), F (fun i => S.1.orderEmbOfFin S.2 (σ i)) := by
    intro S
    rw [det_apply' (B.submatrix _ id), mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    simp only [hF]
    have : A.submatrix id (fun i => S.1.orderEmbOfFin S.2 (σ i))
        = (A.submatrix id (S.1.orderEmbOfFin S.2)).submatrix id σ := by
      ext i j; simp
    rw [this, det_permute']
    simp only [submatrix_apply, id]
    ring
  simp_rw [hrhs]
  rw [← Fintype.sum_prod_type']
  symm
  refine sum_bij (fun x _ => fun i => x.1.1.orderEmbOfFin x.1.2 (x.2 i)) ?_ ?_ ?_ ?_
  · intro x _
    simp only [mem_filter, mem_univ, true_and]
    intro i j h
    exact x.2.injective ((x.1.1.orderEmbOfFin x.1.2).injective h)
  · intro x _ y _ h
    have himg : ∀ z : {S : Finset (Fin n) // S.card = r} × Perm (Fin r),
        univ.image (fun i => z.1.1.orderEmbOfFin z.1.2 (z.2 i)) = z.1.1 := by
      intro z
      rw [show (fun i => z.1.1.orderEmbOfFin z.1.2 (z.2 i))
          = (z.1.1.orderEmbOfFin z.1.2) ∘ z.2 from rfl, ← image_image, image_univ_equiv,
        image_orderEmbOfFin_univ]
    have hS : x.1 = y.1 := by
      apply Subtype.ext
      rw [← himg x, ← himg y]
      simp only at h
      rw [h]
    obtain ⟨⟨S, hS'⟩, σ⟩ := x
    obtain ⟨⟨T, hT⟩, τ⟩ := y
    simp only [Subtype.mk.injEq] at hS
    subst hS
    simp only at h
    have : σ = τ := by
      ext i
      have := congrFun h i
      exact congrArg Fin.val ((S.orderEmbOfFin hS').injective this)
    rw [this]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hS := card_image_of_injective_fin hp
    obtain ⟨σ, hσ⟩ := exists_perm_of_injective hp hS
    exact ⟨(⟨univ.image p, hS⟩, σ), mem_univ _, funext hσ⟩
  · intro x _
    rfl

end Divisors
