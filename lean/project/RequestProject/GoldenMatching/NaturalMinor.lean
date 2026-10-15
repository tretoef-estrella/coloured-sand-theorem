module

public import RequestProject.GoldenMatching.Complement
public import RequestProject.SmithBounds.LeastTerm

/-!
# Part D of `C4_golden_matching.md`: Corollary D (Corollary 6.3, the natural minor)

Encodings (namespace `GoldenMatching`), in the setting of Parts B and C (see `Dancers.lean` and
`Complement.lean` for `L_r`, `F_r`, `ĉ = cHat`, `x_D = xVal` and `U(r) = U`):

* The matrix is `M : Finset ℕ → Finset ℕ → ℤ`, a function from pairs of finite sets to `ℤ`; only
  its values at pairs of dancers (subsets of `I`) are used.
* (S) is `∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0`.
* (H) is `∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + ĉ(a, b) ∧ 2^n ∣ M a b ∧
  ¬ 2^{n+1} ∣ M a b`.
* `M[L_r, F_r]` is the `r × r` matrix `Matrix.of fun i j => M (e i) (f j)` for arbitrary orders
  `e : Fin r ≃ L_r` and `f : Fin r ≃ F_r`; the corollary holds for every such choice.

The proof is the one of the file: the golden bijection of Theorem B is the unique matching of
least cost `r·C + U(r)` (Lemma C2), and Corollary B′ of piece C2 (`SmithBounds.corollary_B'`)
concludes.
-/

@[expose] public section

namespace GoldenMatching

open Finset Rulers

/-- Exact `2`-adic valuations add along products (auxiliary). -/
lemma exact_pow_two_dvd_prod {ι : Type*} (s : Finset ι) (g : ι → ℤ) (n : ι → ℕ)
    (h : ∀ i ∈ s, 2 ^ n i ∣ g i ∧ ¬ (2 : ℤ) ^ (n i + 1) ∣ g i) :
    2 ^ (∑ i ∈ s, n i) ∣ ∏ i ∈ s, g i ∧ ¬ (2 : ℤ) ^ (∑ i ∈ s, n i + 1) ∣ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    obtain ⟨h1, h2⟩ := h a (mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := ih1
    have hxo : ¬ (2 : ℤ) ∣ x := by
      rintro ⟨z, rfl⟩; exact h2 ⟨z, by rw [hx]; ring⟩
    have hyo : ¬ (2 : ℤ) ∣ y := by
      rintro ⟨z, rfl⟩; exact ih2 ⟨z, by rw [hy]; ring⟩
    rw [hx, hy]
    refine ⟨⟨x * y, by ring⟩, ?_⟩
    rintro ⟨z, hz⟩
    have hxy : (2 : ℤ) ∣ x * y := by
      refine ⟨z, ?_⟩
      have hpos : (2 : ℤ) ^ (n a + ∑ i ∈ s, n i) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      calc (2 : ℤ) ^ (n a + ∑ i ∈ s, n i) * (x * y) = 2 ^ n a * x * (2 ^ (∑ i ∈ s, n i) * y) := by
            ring
        _ = _ := hz
        _ = _ := by ring
    rcases Int.prime_two.dvd_mul.1 hxy with h | h
    · exact hxo h
    · exact hyo h

/-- **Corollary D** (Corollary 6.3 of the source) of `C4_golden_matching.md`: in the setting of
Parts B and C, with an integer `α`, `μ ≥ 0`, `K = 2^k` and an integer `C`, let `M` be an integer
matrix indexed by the dancers satisfying (S) `M(a, b) = 0` unless `b ⊆ a`, and (H) for every
`b ⊆ a ⊆ I` there is `n ∈ ℕ` with `n = C + ĉ(a, b)`, `2^n ∣ M(a, b)` and `2^{n+1} ∤ M(a, b)`.
Then for every `0 ≤ r ≤ N` and all orders `e : Fin r ≃ L_r`, `f : Fin r ≃ F_r` of the rows and
columns, there is `n ∈ ℕ` with `n = r·C + U(r)`, `2^n ∣ det M[L_r, F_r]` and
`2^{n+1} ∤ det M[L_r, F_r]`; in particular `det M[L_r, F_r] ≠ 0`. -/
theorem corollary_D (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) (μ : ℕ) (C : ℤ)
    (M : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I →
      ∃ n : ℕ, (n : ℤ) = C + cHat k I α μ a b ∧ 2 ^ n ∣ M a b ∧ ¬ 2 ^ (n + 1) ∣ M a b)
    (r : ℕ) (hr : r ≤ 2 ^ #I) (e : Fin r ≃ Lr I r) (f : Fin r ≃ Fr I r) :
    ∃ n : ℕ, (n : ℤ) = r * C + U k I α μ r ∧
      2 ^ n ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      ¬ 2 ^ (n + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      (Matrix.of fun i j => M (e i) (f j)).det ≠ 0 := by
  classical
  -- support and costs for Corollary B′
  let supp : Finset ℕ → Finset ℕ → Prop := fun a b => ¬ (a ⊆ I ∧ b ⊆ I) ∨ b ⊆ a
  let c : Finset ℕ → Finset ℕ → ℕ := fun a b =>
    if b ⊆ a ∧ a ⊆ I then (C + cHat k I α μ a b).toNat else 0
  have hsupp : ∀ a b, ¬ supp a b → M a b = 0 := by
    intro a b h
    simp only [supp, not_or, not_not] at h
    exact hS a b h.1.1 h.1.2 h.2
  have hcval : ∀ a b, b ⊆ a → a ⊆ I →
      ((c a b : ℕ) : ℤ) = C + cHat k I α μ a b ∧ 2 ^ c a b ∣ M a b ∧ ¬ 2 ^ (c a b + 1) ∣ M a b := by
    intro a b hba ha
    obtain ⟨n, hn, h1, h2⟩ := hH a b hba ha
    have hc : c a b = n := by simp only [c, hba, ha, and_self, if_true]; omega
    rw [hc]; exact ⟨hn, h1, h2⟩
  have hc : ∀ a b, (2 : ℤ) ^ c a b ∣ M a b := by
    intro a b
    by_cases h : b ⊆ a ∧ a ⊆ I
    · exact (hcval a b h.1 h.2).2.1
    · simp only [c, h, if_false, pow_zero, one_dvd]
  have hLI : ∀ D : Lr I r, (D : Finset ℕ) ⊆ I := fun D => mem_powerset.1 (mem_filter.1 D.2).1
  have hFI : ∀ D : Fr I r, (D : Finset ℕ) ⊆ I := fun D => mem_powerset.1 (mem_filter.1 D.2).1
  have hmatch : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β →
      ∀ D : Lr I r, ((β D : Fr I r) : Finset ℕ) ⊆ D := by
    intro β hβ D
    rcases hβ D with h | h
    · exact absurd ⟨hLI D, hFI (β D)⟩ h
    · exact h
  have hcard : (Fintype.card (Lr I r) : ℤ) = r := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  -- the cost of a matching (Lemma C2)
  have hcost : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β →
      (SmithBounds.cost c β : ℤ) =
        r * C + U k I α μ r + ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) := by
    intro β hβ
    unfold SmithBounds.cost
    push_cast
    rw [sum_congr rfl fun (D : Lr I r) _ => (hcval D (β D) (hmatch β hβ D) (hLI D)).1, sum_add_distrib,
      lemma_C2, sum_const, card_univ, nsmul_eq_mul, hcard, U]
    ring
  obtain ⟨⟨β₀, hβ₀⟩, huniqB⟩ := theorem_B k hI r hr
  have hβ₀m : SmithBounds.IsMatching supp β₀ := fun D => Or.inr (hβ₀ D).1
  have hT : (SmithBounds.cost c β₀ : ℤ) = r * C + U k I α μ r := by
    rw [hcost β₀ hβ₀m]
    simp [fun D => (hβ₀ D).2]
  have hval : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β →
      (2 : ℤ) ^ SmithBounds.cost c β ∣ ∏ a : Lr I r, M a (β a) ∧
        ¬ (2 : ℤ) ^ (SmithBounds.cost c β + 1) ∣ ∏ a : Lr I r, M a (β a) := by
    intro β hβ
    exact exact_pow_two_dvd_prod univ (fun a : Lr I r => M a (β a)) (fun a => c a (β a))
      (fun a _ => (hcval a (β a) (hmatch β hβ a) (hLI a)).2)
  have huniq : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β → β ≠ β₀ →
      SmithBounds.cost c β₀ < SmithBounds.cost c β := by
    intro β hβ hne
    have h1 := hcost β hβ
    rw [← hT] at h1
    have hpos : 0 < ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) := by
      rcases (sum_nonneg fun D _ => by positivity :
          0 ≤ ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ)).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hne
        have hz := (sum_eq_zero_iff_of_nonneg fun D _ => by positivity).1 h.symm
        have hgold : ∀ D : Lr I r, IsGoldenArrow k I D (β D) := fun D =>
          ⟨hmatch β hβ D, by exact_mod_cast hz D (mem_univ D)⟩
        exact Equiv.ext (huniqB β β₀ hgold hβ₀)
    omega
  obtain ⟨h1, h2⟩ := SmithBounds.corollary_B' (Matrix.of M) 2 le_rfl supp hsupp c hc e f hval β₀
    (SmithBounds.cost c β₀) hβ₀m rfl huniq
  refine ⟨SmithBounds.cost c β₀, hT, h1, h2, fun h0 => h2 ?_⟩
  change (Matrix.of fun i j => M (e i) (f j)).det = 0 at h0
  change (2 : ℤ) ^ (SmithBounds.cost c β₀ + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det
  rw [h0]; exact dvd_zero _

end GoldenMatching
