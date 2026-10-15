module

public import Mathlib

/-!
# Part A of `C2_smith_bounds.md`: Lemma A (tropical bound)

## Encoding

* The matrix is `M : Matrix n n R` over a commutative ring `R`, indexed by a type `n`
  (the file asks for a finite type; finiteness is not needed, so this is slightly more
  general).  The support is a relation `supp : n → n → Prop` with
  `M a b = 0` whenever `¬ supp a b`, and the costs are `c : n → n → ℕ` with
  `π ^ c a b ∣ M a b`.
* The finite sets of indices are `A B : Finset n`.  The minor `M[A, B]` is the `r × r` matrix
  `minor M e f = M.submatrix (fun i => (e i : n)) (fun j => (f j : n))`, where
  `e : Fin r ≃ A` and `f : Fin r ≃ B` are arbitrary bijections (the "fixed orders" of the
  rows `A` and of the columns `B`; their existence is equivalent to `|A| = |B| = r`).
  All statements hold for *every* choice of `e` and `f`.
* An `A → B` matching is an equivalence `β : A ≃ B` (a bijection between the subtypes) with
  `supp a (β a)` for every `a ∈ A` (`IsMatching supp β`); its cost is
  `cost c β = Σ_{a ∈ A} c(a, β a)`.
-/

@[expose] public section

namespace SmithBounds

open Finset Matrix

variable {n R : Type*} [CommRing R]

/-- *Part A, Setting* of `C2_smith_bounds.md`: the minor `M[A, B]`, i.e. the `r × r`
submatrix with rows `A` and columns `B`, listed in the orders `e : Fin r ≃ A` and
`f : Fin r ≃ B`. -/
def minor (M : Matrix n n R) {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B) :
    Matrix (Fin r) (Fin r) R :=
  M.submatrix (fun i => ((e i : A) : n)) (fun j => ((f j : B) : n))

/-- *Part A, Setting* of `C2_smith_bounds.md`: an `A → B` matching is a bijection
`β : A → B` with `supp a (β a)` for every `a ∈ A`. -/
def IsMatching (supp : n → n → Prop) {A B : Finset n} (β : A ≃ B) : Prop :=
  ∀ a : A, supp a (β a)

/-- *Part A, Setting* of `C2_smith_bounds.md`: the cost `Σ_{a∈A} c(a, β a)` of a bijection
`β : A → B`. -/
def cost (c : n → n → ℕ) {A B : Finset n} (β : A ≃ B) : ℕ :=
  ∑ a : A, c a (β a)

/-- The bijection `A → B` associated with a permutation `σ` of the row indices of the minor:
`a ↦ f (σ⁻¹ (e⁻¹ a))`.  (Auxiliary for Part A / Corollary B′ of `C2_smith_bounds.md`.) -/
def permToBij {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B)
    (σ : Equiv.Perm (Fin r)) : A ≃ B :=
  (σ.trans e).symm.trans f

lemma permToBij_injective {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B) :
    Function.Injective (permToBij e f) := by
  intro σ τ h
  have h1 : (σ.trans e).symm = (τ.trans e).symm := by
    have := congrArg (fun β : A ≃ B => β.trans f.symm) h
    simpa [permToBij, Equiv.trans_assoc] using this
  have h2 : σ.trans e = τ.trans e := by simpa using congrArg Equiv.symm h1
  ext i
  have := congrArg (fun g : Fin r ≃ A => e.symm (g i)) h2
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at this
  rw [this]

lemma permToBij_surjective {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B) :
    Function.Surjective (permToBij e f) := by
  intro β
  refine ⟨(e.trans (β.trans f.symm)).symm, ?_⟩
  ext a
  simp [permToBij]

/-- The product of the term of `det M[A, B]` indexed by `σ` is `Π_{a∈A} M a (β a)` for the
associated bijection `β`. (Auxiliary for Part A of `C2_smith_bounds.md`.) -/
lemma prod_minor_eq {M : Matrix n n R} {A B : Finset n} {r : ℕ} (e : Fin r ≃ A)
    (f : Fin r ≃ B) (σ : Equiv.Perm (Fin r)) :
    ∏ i, minor M e f (σ i) i = ∏ a : A, M a (permToBij e f σ a) := by
  rw [← Equiv.prod_comp (σ.trans e)]
  refine prod_congr rfl fun i _ => ?_
  simp [minor, permToBij]

/-- The cost of the bijection associated with `σ`, as a sum over the row indices of the minor.
(Auxiliary for Part A of `C2_smith_bounds.md`.) -/
lemma cost_permToBij (c : n → n → ℕ) {A B : Finset n} {r : ℕ} (e : Fin r ≃ A)
    (f : Fin r ≃ B) (σ : Equiv.Perm (Fin r)) :
    cost c (permToBij e f σ) = ∑ i, c (e (σ i)) (f i) := by
  rw [cost, ← Equiv.sum_comp (σ.trans e)]
  refine sum_congr rfl fun i _ => ?_
  simp [permToBij]

/-- The Leibniz expansion of the minor as a signed sum over the bijections `A → B`
(indexed by permutations). (Auxiliary for Part A of `C2_smith_bounds.md`.) -/
lemma det_minor_eq (M : Matrix n n R) {A B : Finset n} {r : ℕ} (e : Fin r ≃ A)
    (f : Fin r ≃ B) :
    (minor M e f).det =
      ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) • ∏ a : A, M a (permToBij e f σ a) := by
  rw [Matrix.det_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [prod_minor_eq, Units.smul_def]

/-- A term of the expansion whose bijection leaves the support vanishes.
(Auxiliary for Part A of `C2_smith_bounds.md`.) -/
lemma prod_eq_zero_of_not_matching {M : Matrix n n R} {supp : n → n → Prop}
    (hsupp : ∀ a b, ¬ supp a b → M a b = 0) {A B : Finset n} {β : A ≃ B}
    (hβ : ¬ IsMatching supp β) : ∏ a : A, M a (β a) = 0 := by
  unfold IsMatching at hβ
  push_neg at hβ
  obtain ⟨a, ha⟩ := hβ
  exact prod_eq_zero (mem_univ a) (hsupp _ _ ha)

/-- The product along any bijection `β` is divisible by `π ^ cost(β)`.
(Auxiliary for Part A of `C2_smith_bounds.md`.) -/
lemma pow_cost_dvd_prod {M : Matrix n n R} {π : R} {c : n → n → ℕ}
    (hc : ∀ a b, π ^ c a b ∣ M a b) {A B : Finset n} (β : A ≃ B) :
    π ^ cost c β ∣ ∏ a : A, M a (β a) := by
  rw [cost, ← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun a _ => hc _ _

/-- **Lemma A (A1)** (tropical bound) of `C2_smith_bounds.md`: if `T ≤ cost(β)` for every
`A → B` matching `β`, then `π^T ∣ det M[A, B]`.  (Stated for every choice of the orders
`e`, `f` of the rows and columns of the minor.) -/
theorem lemma_A1 (M : Matrix n n R) (π : R) (supp : n → n → Prop)
    (hsupp : ∀ a b, ¬ supp a b → M a b = 0) (c : n → n → ℕ) (hc : ∀ a b, π ^ c a b ∣ M a b)
    {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B) (T : ℕ)
    (hT : ∀ β : A ≃ B, IsMatching supp β → T ≤ cost c β) :
    π ^ T ∣ (minor M e f).det := by
  rw [det_minor_eq]
  refine dvd_sum fun σ _ => ?_
  rw [zsmul_eq_mul]
  refine Dvd.dvd.mul_left ?_ _
  by_cases hβ : IsMatching supp (permToBij e f σ)
  · exact (pow_dvd_pow π (hT _ hβ)).trans (pow_cost_dvd_prod hc _)
  · rw [prod_eq_zero_of_not_matching hsupp hβ]
    exact dvd_zero _

/-- **Lemma A (A2)** of `C2_smith_bounds.md`: if there is no `A → B` matching, then
`det M[A, B] = 0`.  (Stated for every choice of the orders `e`, `f`.) -/
theorem lemma_A2 (M : Matrix n n R) (supp : n → n → Prop)
    (hsupp : ∀ a b, ¬ supp a b → M a b = 0)
    {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B)
    (hno : ∀ β : A ≃ B, ¬ IsMatching supp β) :
    (minor M e f).det = 0 := by
  rw [det_minor_eq]
  refine sum_eq_zero fun σ _ => ?_
  rw [prod_eq_zero_of_not_matching hsupp (hno _), smul_zero]

end SmithBounds
