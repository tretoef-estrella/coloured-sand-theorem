module

public import RequestProject.Potential.Flat

/-!
# Part 3 of `C8_theorem_F_potential.md`: Theorem F (Theorem 7.8, the floor) and Corollary F′

Encodings as in `RequestProject/Potential/Basic.lean`.  In Corollary F′, subsets of `I` are
`Finset ℕ`s with `D ⊆ I`, `rank_I = GoldenMatching.rank I` (C4) and `o = Rulers.oE` (C3).
-/

@[expose] public section

namespace Potential

open Finset AntitonicFit TheoremF

/-- Base of the induction of Theorem F (`C8_theorem_F_potential.md`): for `I = ∅`, `V := 0` is a
potential (one position, `ŷ_H = 0`, no arrows).  (No house condition is needed.) -/
lemma potential_empty (k ℓ : ℕ) (α : ℤ) : IsPotential ∅ k ℓ α (fun _ => 0) := by
  refine ⟨fun p hp => ?_, fun _ _ _ _ => le_rfl, fun p q harr => ?_⟩
  · simp only [card_empty, pow_zero] at hp
    obtain rfl : p = 0 := by omega
    have h1 := A2 (lemma_0f_antisymm (∅ : Finset ℕ) k ℓ α) 0 (by simp)
    simp only [card_empty, pow_zero] at h1
    simp only [yhat, card_empty, pow_zero, sub_self]
    simp at h1; omega
  · exfalso
    obtain ⟨-, -, hss⟩ := harr
    have h := lemma_0a (∅ : Finset ℕ) p
    rw [subset_empty] at h
    rw [h] at hss
    exact not_ssubset_empty _ hss

/-- Induction step of Theorem F (`C8_theorem_F_potential.md`): from a potential `V'` for `H'`,
Lemma N (if `X_1(M − 1) > 0`) or Lemma F with `c_F := lo` (if `X_1(M − 1) ≤ 0`) gives a
potential for `H`. -/
lemma potential_step {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) {V' : ℕ → ℤ}
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') : ∃ V, IsPotential I k ℓ α V := by
  by_cases hX : 0 < X1 I k ℓ α c (2 ^ #(I.erase c) - 1)
  · exact ⟨_, lemma_N hI hℓ hα hne hc hV' hX⟩
  · push_neg at hX
    obtain ⟨f, hf⟩ := exists_flat_start hX
    exact ⟨_, lemma_F4 hI hℓ hα hne hc hV' hf _ le_rfl (lemma_F3 hne hc hV' hf)⟩

/-- Theorem F by induction on `n = |I|` (`C8_theorem_F_potential.md`). -/
lemma potential_exists_aux : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ), #I = n →
    (∀ t ∈ I, t < k) → ℓ < 2 ^ k → 1 ≤ α → ∃ V, IsPotential I k ℓ α V := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ α hn _ _ _
    rw [card_eq_zero.1 hn]
    exact ⟨_, potential_empty k ℓ α⟩
  | succ n ih =>
    intro I k ℓ α hn hI hℓ hα
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hn' : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    obtain ⟨V', hV'⟩ := ih (I.erase c) c (ℓ % 2 ^ c) α hn' hI' (Nat.mod_lt _ (by positivity)) hα
    exact potential_step hI hℓ hα hne hc hV'

/-- **Theorem F** (Theorem 7.8, the floor; Part 3 of `C8_theorem_F_potential.md`): for every
house `H = (I, k, ℓ, α)` (`I ⊆ {0, …, k − 1}`, `ℓ < 2^k`, `1 ≤ α`) there is a potential `V`
for `H`, i.e. (E), (M), (G) hold. -/
theorem theorem_F {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) : ∃ V : ℕ → ℤ, IsPotential I k ℓ α V :=
  potential_exists_aux _ I k ℓ α rfl hI hℓ hα

/-- `dancer_I(rank_I(D)) = D` for `D ⊆ I` (Lemma 0c of C7; used in Corollary F′ of
`C8_theorem_F_potential.md`). -/
lemma dancer_rank {I D : Finset ℕ} (hD : D ⊆ I) : dancer I (GoldenMatching.rank I D) = D := by
  obtain ⟨p, ⟨hp, rfl⟩, -⟩ := lemma_0c_existsUnique hD
  rw [lemma_0c_rank hp]

/-- **Corollary F′** (the paper's form, on subsets; Part 3 of `C8_theorem_F_potential.md`): for
every house there is `W : Finset ℕ → ℤ` with, for `D, E, F, a, b ⊆ I`:
(E) `W(D) − W(I ∖ D) = ŷ_H(rank_I(D))`; (M) `o_E ≤ o_F ⟹ W(F) ≤ W(E)`;
(G) `b ⊊ a ⟹ W(a) − W(b) ≤ ĉ_H(a, b)` (`Houses.cHatH`).  Here `W(D) := V(rank_I(D))`. -/
theorem corollary_F' {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) : ∃ W : Finset ℕ → ℤ,
      (∀ D, D ⊆ I → W D - W (I \ D) = yhat I k ℓ α (GoldenMatching.rank I D)) ∧
      (∀ E F, E ⊆ I → F ⊆ I → Rulers.oE E ≤ Rulers.oE F → W F ≤ W E) ∧
      (∀ a b, a ⊆ I → b ⊆ I → b ⊂ a → W a - W b ≤ Houses.cHatH I k ℓ α a b) := by
  obtain ⟨V, hV⟩ := theorem_F hI hℓ hα
  refine ⟨fun D => V (GoldenMatching.rank I D), fun D hD => ?_, fun E F hE hF hEF => ?_,
    fun a b ha hb hab => ?_⟩
  · simp only
    rw [GoldenMatching.lemma_C1_rank hD]
    exact hV.E _ (GoldenMatching.rank_lt hD)
  · simp only
    apply hV.M _ _ _ (GoldenMatching.rank_lt hF)
    by_contra hlt
    push_neg at hlt
    have := lemma_0b hlt (GoldenMatching.rank_lt hE)
    rw [dancer_rank hE, dancer_rank hF] at this
    omega
  · have harr : IsArrow I (GoldenMatching.rank I a) (GoldenMatching.rank I b) :=
      ⟨GoldenMatching.rank_lt ha, GoldenMatching.rank_lt hb, by
        rw [dancer_rank ha, dancer_rank hb]; exact hab⟩
    have := hV.G _ _ harr
    simp only [cHat, dancer_rank ha, dancer_rank hb] at this
    exact this

end Potential
