module

public import RequestProject.SmithBounds.TropicalBound

/-!
# Part B of `C2_smith_bounds.md`: the unique least term

* **Lemma B** (`lemma_B`): the finite set `s` is a `Finset ι` of an arbitrary index type `ι`
  and the family `t : s → ℤ` is a function `t : ι → ℤ` of which only the values on `s` are
  used (a faithful encoding of a function on `s`).
* **Corollary B′** (`corollary_B'`): in the setting of Part A (see
  `RequestProject/SmithBounds/TropicalBound.lean` for the encoding of the minor `M[A, B]`, of
  matchings and of their costs) with `R = ℤ` and `π = p ≥ 2`.  "There is exactly one matching
  `β₀` of least cost `T`" is encoded as: `β₀` is a matching, `cost β₀ = T`, and every matching
  `β ≠ β₀` has cost `> T`.
-/

@[expose] public section

namespace SmithBounds

open Finset Matrix

/-- **Lemma B** (unique least term) of `C2_smith_bounds.md`: let `p ≥ 2` be an integer, `s` a
finite set, `t : s → ℤ`, `i₀ ∈ s`, `v ∈ ℕ`, with `p^v ∣ t(i₀)`, `p^{v+1} ∤ t(i₀)` and
`p^{v+1} ∣ t(i)` for every `i ∈ s`, `i ≠ i₀`.  Then `p^v ∣ Σ_{i∈s} t(i)` and
`p^{v+1} ∤ Σ_{i∈s} t(i)`.  (The hypothesis `p ≥ 2` of the file is kept, although the proof
does not use it.) -/
theorem lemma_B {ι : Type*} (p : ℤ) (_hp : 2 ≤ p) (s : Finset ι) (t : ι → ℤ) (i₀ : ι)
    (hi₀ : i₀ ∈ s) (v : ℕ) (h1 : p ^ v ∣ t i₀) (h2 : ¬ p ^ (v + 1) ∣ t i₀)
    (h3 : ∀ i ∈ s, i ≠ i₀ → p ^ (v + 1) ∣ t i) :
    p ^ v ∣ ∑ i ∈ s, t i ∧ ¬ p ^ (v + 1) ∣ ∑ i ∈ s, t i := by
  classical
  rw [← add_sum_erase s t hi₀]
  have hrest : p ^ (v + 1) ∣ ∑ i ∈ s.erase i₀, t i :=
    dvd_sum fun i hi => h3 i (mem_of_mem_erase hi) (ne_of_mem_erase hi)
  refine ⟨dvd_add h1 ((pow_dvd_pow p (Nat.le_succ v)).trans hrest), ?_⟩
  rwa [dvd_add_left hrest]

variable {n : Type*}

/-- **Corollary B′** (the natural minor) of `C2_smith_bounds.md`: in the setting of Part A with
`R = ℤ` and `π = p ≥ 2`, suppose that for every `A → B` matching `β` the product
`Π_a M a (β a)` has exact `p`-adic valuation `cost(β)`, and that there is exactly one matching
`β₀` of least cost `T`.  Then `p^T ∣ det M[A, B]` and `p^{T+1} ∤ det M[A, B]`.
(Stated for every choice of the orders `e`, `f` of the rows and columns of the minor.  The
hypotheses `p ≥ 2` and `p^{c(a,b)} ∣ M a b` of the setting are kept, although the proof does
not use them.) -/
theorem corollary_B' (M : Matrix n n ℤ) (p : ℤ) (hp : 2 ≤ p) (supp : n → n → Prop)
    (hsupp : ∀ a b, ¬ supp a b → M a b = 0) (c : n → n → ℕ) (_hc : ∀ a b, p ^ c a b ∣ M a b)
    {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B)
    (hval : ∀ β : A ≃ B, IsMatching supp β →
      p ^ cost c β ∣ ∏ a : A, M a (β a) ∧ ¬ p ^ (cost c β + 1) ∣ ∏ a : A, M a (β a))
    (β₀ : A ≃ B) (T : ℕ) (hβ₀ : IsMatching supp β₀) (hT : cost c β₀ = T)
    (huniq : ∀ β : A ≃ B, IsMatching supp β → β ≠ β₀ → T < cost c β) :
    p ^ T ∣ (minor M e f).det ∧ ¬ p ^ (T + 1) ∣ (minor M e f).det := by
  rw [det_minor_eq]
  obtain ⟨σ₀, hσ₀⟩ := permToBij_surjective e f β₀
  refine lemma_B p hp univ _ σ₀ (mem_univ _) T ?_ ?_ ?_
  · rw [zsmul_eq_mul, hσ₀, ← hT]
    exact Dvd.dvd.mul_left (hval β₀ hβ₀).1 _
  · rw [zsmul_eq_mul, hσ₀, Int.cast_id, Units.dvd_mul_left, ← hT]
    exact (hval β₀ hβ₀).2
  · intro σ _ hσ
    rw [zsmul_eq_mul]
    refine Dvd.dvd.mul_left ?_ _
    have hne : permToBij e f σ ≠ β₀ := by
      rw [← hσ₀]
      exact fun h => hσ (permToBij_injective e f h)
    by_cases hβ : IsMatching supp (permToBij e f σ)
    · exact (pow_dvd_pow p (huniq _ hβ hne)).trans (hval _ hβ).1
    · rw [prod_eq_zero_of_not_matching hsupp hβ]
      exact dvd_zero _

end SmithBounds
