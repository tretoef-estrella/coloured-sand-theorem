module

public import RequestProject.OddCeiling.Order

/-!
# Parts B and C of `CSI14_the_ceiling_at_p.md`: the cost of a bijection (abstract form) and
Corollary 6.3 at the prime p (the natural minor)

## Encoding

* The family is `k : ℕ`, `I : Finset ℕ` (with `hI : ∀ t ∈ I, t < k` where Theorem O is used);
  `γ = Rulers.gamma k I` (natural-valued, cast to `ℤ`).
* The two abstract rulers are `R₁ R₂ : Finset ℕ → ℤ`.
* `ĉ(a, b) = R₁ a − R₂ b + γ(a ∖ b)` is `cHatP k I R₁ R₂ a b`, `x_D = R₁ D − R₂ (I ∖ D)` is
  `xP I R₁ R₂ D`, and `U(r) = Σ_{D ∈ Lr I r} x_D` is `UP I R₁ R₂ r` (C4's `GoldenMatching.Lr`).
* A bijection `β : Lr I r ≃ Fr I r` is an equivalence of the subtypes (as in C4).
* The matrix of Part C is `M : Finset ℕ → Finset ℕ → ℤ`; (S) is
  `∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0`; (H) is
  `∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + ĉ(a, b) ∧ p^n ∣ M a b ∧ ¬ p^{n+1} ∣ M a b`.
* The prime is `p : ℕ` with `hp : p.Prime`; powers are taken in `ℤ` as `(p : ℤ) ^ n`.
* `M[e, f] = Matrix.of fun i j => M (e i) (f j)` for arbitrary orders `e : Fin r ≃ Lr I r`,
  `f : Fin r ≃ Fr I r`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Rulers GoldenMatching

/-- *Part B* of `CSI14_the_ceiling_at_p.md`: `ĉ(a, b) := R₁ a − R₂ b + γ(a ∖ b)` with
`γ = Rulers.gamma k I`. -/
def cHatP (k : ℕ) (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (a b : Finset ℕ) : ℤ :=
  R₁ a - R₂ b + gamma k I (a \ b)

/-- *Part B* of `CSI14_the_ceiling_at_p.md`: `x_D := R₁ D − R₂ (I ∖ D)`. -/
def xP (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (D : Finset ℕ) : ℤ :=
  R₁ D - R₂ (I \ D)

/-- *Part B* of `CSI14_the_ceiling_at_p.md`: `U(r) := Σ_{D ∈ Lr I r} x_D`. -/
def UP (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ D ∈ Lr I r, xP I R₁ R₂ D

/-- **(B1)** of `CSI14_the_ceiling_at_p.md`: for every bijection `β : Lr I r ≃ Fr I r`,
`Σ_{D ∈ Lr I r} ĉ(D, β D) = U(r) + Σ_{D ∈ Lr I r} γ(D ∖ β D)`. (No hypothesis on `I`, `R₁`,
`R₂` is needed.) -/
theorem B1_cost (k : ℕ) (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (r : ℕ)
    (β : Lr I r ≃ Fr I r) :
    ∑ D : Lr I r, cHatP k I R₁ R₂ D (β D) =
      UP I R₁ R₂ r + ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) := by
  have hcols : ∑ D : Lr I r, R₂ (β D) = ∑ D ∈ Lr I r, R₂ (I \ D) := by
    rw [Equiv.sum_comp β (fun E : Fr I r => R₂ E), sum_coe_sort (Fr I r) (fun E => R₂ E)]
    have hb := lemma_C1_bijOn I r
    exact (sum_nbij (fun D => I \ D) (fun D hD => hb.mapsTo hD) hb.injOn hb.surjOn
      (fun _ _ => rfl)).symm
  simp only [cHatP, UP, xP, sum_add_distrib, sum_sub_distrib]
  rw [hcols, sum_coe_sort (Lr I r) (fun D => R₁ D)]

/-- Exact `p`-adic valuations add along products, for `p` prime. (Auxiliary for (C1) of
`CSI14_the_ceiling_at_p.md`: "exact valuations add because `p` is prime".) -/
theorem exact_pow_dvd_prod {ι : Type*} {p : ℤ} (hp : Prime p) (s : Finset ι) (g : ι → ℤ)
    (n : ι → ℕ) (h : ∀ i ∈ s, p ^ n i ∣ g i ∧ ¬ p ^ (n i + 1) ∣ g i) :
    p ^ (∑ i ∈ s, n i) ∣ ∏ i ∈ s, g i ∧ ¬ p ^ (∑ i ∈ s, n i + 1) ∣ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_unit ∘ isUnit_of_dvd_one
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    obtain ⟨h1, h2⟩ := h a (mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := ih1
    have hp0 : p ≠ 0 := hp.ne_zero
    have hxo : ¬ p ∣ x := by
      rintro ⟨z, rfl⟩; exact h2 ⟨z, by rw [hx]; ring⟩
    have hyo : ¬ p ∣ y := by
      rintro ⟨z, rfl⟩; exact ih2 ⟨z, by rw [hy]; ring⟩
    rw [hx, hy]
    refine ⟨⟨x * y, by ring⟩, ?_⟩
    rintro ⟨z, hz⟩
    have hxy : p ∣ x * y := by
      refine ⟨z, ?_⟩
      have hpos : p ^ (n a + ∑ i ∈ s, n i) ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hpos
      calc p ^ (n a + ∑ i ∈ s, n i) * (x * y) = p ^ n a * x * (p ^ (∑ i ∈ s, n i) * y) := by
            ring
        _ = _ := hz
        _ = _ := by ring
    rcases hp.dvd_or_dvd hxy with h | h
    · exact hxo h
    · exact hyo h

/-- **(C1)** (Corollary 6.3 at the prime `p`, the natural minor) of
`CSI14_the_ceiling_at_p.md`: let `I ⊆ {0, …, k−1}`, `R₁, R₂ : Finset ℕ → ℤ`, `p` prime,
`C ∈ ℤ`, and `M : Finset ℕ → Finset ℕ → ℤ` with (S) `M a b = 0` for `a, b ⊆ I`, `b ⊄ a`, and
(H) for every `b ⊆ a ⊆ I` some `n ∈ ℕ` with `n = C + ĉ(a, b)`, `p^n ∣ M a b`,
`p^{n+1} ∤ M a b`.  Then for every `r ≤ 2^{|I|}` and all orders `e : Fin r ≃ Lr I r`,
`f : Fin r ≃ Fr I r` there is `n ∈ ℕ` with `n = r·C + U(r)`, `p^n ∣ det M[e, f]`,
`p^{n+1} ∤ det M[e, f]` and `det M[e, f] ≠ 0`. -/
theorem C1_natural_minor (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (R₁ R₂ : Finset ℕ → ℤ) {p : ℕ} (hp : p.Prime) (C : ℤ) (M : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + cHatP k I R₁ R₂ a b ∧
      (p : ℤ) ^ n ∣ M a b ∧ ¬ (p : ℤ) ^ (n + 1) ∣ M a b)
    (r : ℕ) (hr : r ≤ 2 ^ #I) (e : Fin r ≃ Lr I r) (f : Fin r ≃ Fr I r) :
    ∃ n : ℕ, (n : ℤ) = r * C + UP I R₁ R₂ r ∧
      (p : ℤ) ^ n ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      ¬ (p : ℤ) ^ (n + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      (Matrix.of fun i j => M (e i) (f j)).det ≠ 0 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  let supp : Finset ℕ → Finset ℕ → Prop := fun a b => ¬ (a ⊆ I ∧ b ⊆ I) ∨ b ⊆ a
  let c : Finset ℕ → Finset ℕ → ℕ := fun a b =>
    if b ⊆ a ∧ a ⊆ I then (C + cHatP k I R₁ R₂ a b).toNat else 0
  have hsupp : ∀ a b, ¬ supp a b → M a b = 0 := by
    intro a b h
    simp only [supp, not_or, not_not] at h
    exact hS a b h.1.1 h.1.2 h.2
  have hcval : ∀ a b, b ⊆ a → a ⊆ I →
      ((c a b : ℕ) : ℤ) = C + cHatP k I R₁ R₂ a b ∧ (p : ℤ) ^ c a b ∣ M a b ∧
        ¬ (p : ℤ) ^ (c a b + 1) ∣ M a b := by
    intro a b hba ha
    obtain ⟨n, hn, h1, h2⟩ := hH a b hba ha
    have hc : c a b = n := by simp only [c, hba, ha, and_self, if_true]; omega
    rw [hc]; exact ⟨hn, h1, h2⟩
  have hc : ∀ a b, (p : ℤ) ^ c a b ∣ M a b := by
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
  -- the cost of a matching, by (B1)
  have hcost : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β →
      (SmithBounds.cost c β : ℤ) =
        r * C + UP I R₁ R₂ r + ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) := by
    intro β hβ
    unfold SmithBounds.cost
    push_cast
    rw [sum_congr rfl fun (D : Lr I r) _ => (hcval D (β D) (hmatch β hβ D) (hLI D)).1,
      sum_add_distrib, B1_cost, sum_const, card_univ, nsmul_eq_mul, hcard]
    ring
  obtain ⟨⟨β₀, hβ₀⟩, huniqB⟩ := theorem_B k hI r hr
  have hβ₀m : SmithBounds.IsMatching supp β₀ := fun D => Or.inr (hβ₀ D).1
  have hT : (SmithBounds.cost c β₀ : ℤ) = r * C + UP I R₁ R₂ r := by
    rw [hcost β₀ hβ₀m]
    simp [fun D => (hβ₀ D).2]
  have hval : ∀ β : Lr I r ≃ Fr I r, SmithBounds.IsMatching supp β →
      (p : ℤ) ^ SmithBounds.cost c β ∣ ∏ a : Lr I r, M a (β a) ∧
        ¬ (p : ℤ) ^ (SmithBounds.cost c β + 1) ∣ ∏ a : Lr I r, M a (β a) := by
    intro β hβ
    exact exact_pow_dvd_prod hpZ univ (fun a : Lr I r => M a (β a)) (fun a => c a (β a))
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
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨h1, h2⟩ := SmithBounds.corollary_B' (Matrix.of M) (p : ℤ) hp2 supp hsupp c hc e f
    hval β₀ (SmithBounds.cost c β₀) hβ₀m rfl huniq
  refine ⟨SmithBounds.cost c β₀, hT, h1, h2, fun h0 => h2 ?_⟩
  change (Matrix.of fun i j => M (e i) (f j)).det = 0 at h0
  change (p : ℤ) ^ (SmithBounds.cost c β₀ + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det
  rw [h0]; exact dvd_zero _

end ColouredSand.OddTwist
