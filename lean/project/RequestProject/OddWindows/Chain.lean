module

public import RequestProject.OddWindows.Basic

/-!
# `CSI12_the_odd_windows.md` — the chain argument of the *Proof* of Theorem 4.1

Namespace `ColouredSand.OddTwist`.  The proof of (W1)/(W2) multiplies matrices in *window form*
over consecutive floors.

* `WinF π w L g lo hi M`: the matrix `M` (indexed by slots with labels `L`) has the entries
  `M x y = [L y ⊆ L x] · g(L x ∖ L y) · ∏_{d ∈ [lo + o(L x), hi + o(L y))} π(d)`, with
  `o(E) = Σ_{t ∈ E} w t`.  Windows are `Finset.Ico`.
* `WinF_mul`: the product of two window-form matrices with adjacent windows is in window form,
  with coefficient `g ⋆ g'` (the sum over chains `D ⊇ T ⊇ D'` of the *Proof*).
* `WinF_prodList`: the product `G(φ₀) ⋯ G(φ₀ + s − 1)` over `s` consecutive floors has the
  coefficient `g^{⋆s}` and the concatenated window.
* Auxiliary facts: `starPow` commutes with ring homomorphisms (`map_starPow`) and keeps supports
  (`starPow_supp`); `o` of a subset of `I ∩ [0, h)` is `< p^h` (`oW_lt`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

section Window

variable {K : Type*} [CommRing K] {S : Type*} [Fintype S] [DecidableEq S]

/-- **Window form** of a matrix (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`):
`M x y = [L y ⊆ L x] · g(L x ∖ L y) · ∏_{d ∈ [lo + o(L x), hi + o(L y))} π(d)` with
`o(E) = Σ_{t ∈ E} w t`. -/
def WinF (π : ℕ → K) (w : ℕ → ℕ) (L : S → Finset ℕ) (g : Finset ℕ → K) (lo hi : ℕ)
    (M : Matrix S S K) : Prop :=
  ∀ x y, M x y = if L y ⊆ L x then
    g (L x \ L y) * ∏ d ∈ Ico (lo + ∑ t ∈ L x, w t) (hi + ∑ t ∈ L y, w t), π d else 0

variable {π : ℕ → K} {w : ℕ → ℕ} {L : S → Finset ℕ} {J : Finset ℕ}

omit [DecidableEq S] in
/-- **The chain step** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`): the entry
`(D, D')` of a product is a sum over `D ⊇ T ⊇ D'`; the windows are adjacent, so every chain gives
the same monomial in `π`, and the coefficients add up to `(g ⋆ g')(D ∖ D')`. -/
lemma WinF_mul {g g' : Finset ℕ → K} {l m r : ℕ} {X Y : Matrix S S K} (hL : LabP J L)
    (hlm : l + ∑ t ∈ J, w t ≤ m) (hmr : m + ∑ t ∈ J, w t ≤ r)
    (hX : WinF π w L g l m X) (hY : WinF π w L g' m r Y) :
    WinF π w L (Deficit.starMul g g') l r (X * Y) := by
  unfold WinF at hX hY
  intro x y
  rw [Matrix.mul_apply]
  simp_rw [hX, hY]
  set W := ∏ d ∈ Ico (l + ∑ t ∈ L x, w t) (r + ∑ t ∈ L y, w t), π d with hW
  have key : ∀ z, (if L z ⊆ L x then g (L x \ L z) *
      ∏ d ∈ Ico (l + ∑ t ∈ L x, w t) (m + ∑ t ∈ L z, w t), π d else 0) *
      (if L y ⊆ L z then g' (L z \ L y) *
      ∏ d ∈ Ico (m + ∑ t ∈ L z, w t) (r + ∑ t ∈ L y, w t), π d else 0) =
      if L z ⊆ L x ∧ L y ⊆ L z then g (L x \ L z) * g' (L z \ L y) * W else 0 := by
    intro z
    by_cases h1 : L z ⊆ L x
    · by_cases h2 : L y ⊆ L z
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, hW]
        have e1 := sum_sdiff (f := w) h1
        have e2 := sum_sdiff (f := w) h2
        have b1 : ∑ t ∈ L x \ L z, w t ≤ ∑ t ∈ J, w t :=
          sum_le_sum_of_subset (sdiff_subset.trans (hL.sub x))
        have b2 : ∑ t ∈ L z \ L y, w t ≤ ∑ t ∈ J, w t :=
          sum_le_sum_of_subset (sdiff_subset.trans (hL.sub z))
        rw [← prod_Ico_consecutive _ (show l + ∑ t ∈ L x, w t ≤ m + ∑ t ∈ L z, w t by omega)
          (show m + ∑ t ∈ L z, w t ≤ r + ∑ t ∈ L y, w t by omega)]
        ring
      · simp [h2]
    · simp [h1]
  rw [sum_congr rfl (fun z _ => key z), ← sum_filter]
  split_ifs with hxy
  · unfold Deficit.starMul
    rw [sum_mul]
    apply sum_bij (fun z _ => L x \ L z)
    · intro z hz
      rw [mem_filter] at hz
      rw [mem_powerset]
      intro t ht
      rw [mem_sdiff] at ht ⊢
      exact ⟨ht.1, fun h => ht.2 (hz.2.2 h)⟩
    · intro z₁ hz₁ z₂ hz₂ he
      rw [mem_filter] at hz₁ hz₂
      apply hL.inj
      rw [← Finset.sdiff_sdiff_eq_self hz₁.2.1, ← Finset.sdiff_sdiff_eq_self hz₂.2.1, he]
    · intro Δ hΔ
      rw [mem_powerset] at hΔ
      obtain ⟨z, hz⟩ := hL.surj (L x \ Δ) (sdiff_subset.trans (hL.sub x))
      have hΔx : Δ ⊆ L x := hΔ.trans sdiff_subset
      refine ⟨z, ?_, ?_⟩
      · rw [mem_filter, hz]
        refine ⟨mem_univ _, sdiff_subset, fun t ht => ?_⟩
        rw [mem_sdiff]
        refine ⟨hxy ht, fun h => ?_⟩
        have := hΔ h
        rw [mem_sdiff] at this
        exact this.2 ht
      · simp only [hz]
        exact Finset.sdiff_sdiff_eq_self hΔx
    · intro z hz
      rw [mem_filter] at hz
      have : (L x \ L y) \ (L x \ L z) = L z \ L y := by
        ext t
        simp only [mem_sdiff]
        have := @hz.2.1 t
        tauto
      rw [this]
  · apply sum_eq_zero
    intro z hz
    rw [mem_filter] at hz
    exact absurd (hz.2.2.trans hz.2.1) hxy

omit [Fintype S] in
/-- The identity matrix is in window form with coefficient `g^{⋆0} = [Δ = ∅]` and the empty
window (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`, `s = 0`). -/
lemma WinF_one (hL : Function.Injective L) (g : Finset ℕ → K) (lo : ℕ) :
    WinF π w L (starPow g 0) lo lo (1 : Matrix S S K) := by
  intro x y
  rw [Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp [starPow]
  · have hL' : L x ≠ L y := fun h => hxy (hL h)
    rw [if_neg hxy]
    split_ifs with h
    · have : L x \ L y ≠ ∅ := by
        intro he
        exact hL' (le_antisymm (sdiff_eq_empty_iff_subset.1 he) h)
      simp [starPow, this]
    · rfl

omit [Fintype S] [DecidableEq S] in
/-- Scaling a window-form matrix scales its coefficient. -/
lemma WinF_smul {g : Finset ℕ → K} {lo hi : ℕ} {M : Matrix S S K} (c : K)
    (hM : WinF π w L g lo hi M) : WinF π w L (fun Δ => c * g Δ) lo hi (c • M) := by
  intro x y
  rw [Matrix.smul_apply, hM, smul_eq_mul]
  split_ifs <;> ring

omit [Fintype S] [DecidableEq S] in
/-- The coefficient only matters on the subsets of `J`. -/
lemma WinF_congr {g g' : Finset ℕ → K} {lo hi : ℕ} {M : Matrix S S K}
    (hsub : ∀ x, L x ⊆ J) (hg : ∀ Δ ⊆ J, g Δ = g' Δ) (hM : WinF π w L g lo hi M) :
    WinF π w L g' lo hi M := by
  intro x y
  rw [hM]
  split_ifs
  · rw [hg _ (sdiff_subset.trans (hsub x))]
  · rfl

/-- `f ⋆ [Δ = ∅] = f`. -/
lemma starMul_unit_right' (g : Finset ℕ → K) :
    Deficit.starMul g (fun Δ => if Δ = ∅ then 1 else 0) = g := by
  funext Δ
  unfold Deficit.starMul
  rw [sum_eq_single Δ]
  · simp
  · intro Δ₁ h1 h2
    have : Δ \ Δ₁ ≠ ∅ := by
      intro he
      exact h2 (le_antisymm (mem_powerset.1 h1) (sdiff_eq_empty_iff_subset.1 he))
    simp [this]
  · intro h; exact absurd (mem_powerset.2 subset_rfl) h

/-- `g^{⋆1} = g`. -/
lemma starPow_one' (g : Finset ℕ → K) : starPow g 1 = g := by
  change Deficit.starMul g (starPow g 0) = g
  exact starMul_unit_right' g

/-- **Products over consecutive floors** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`):
if every `G φ` is in window form with coefficient `g` and window `[Mφ, M(φ+1))`, and
`o(J) ≤ M`, then `G(φ₀) ⋯ G(φ₀ + s − 1)` is in window form with coefficient `g^{⋆s}` and window
`[Mφ₀, M(φ₀ + s))`. -/
lemma WinF_prodList {g : Finset ℕ → K} (hL : LabP J L) (M : ℕ) (hJ : ∑ t ∈ J, w t ≤ M)
    (G : ℕ → Matrix S S K) (hG : ∀ φ, WinF π w L g (M * φ) (M * (φ + 1)) (G φ)) :
    ∀ s φ₀, WinF π w L (starPow g s) (M * φ₀) (M * (φ₀ + s))
      (((List.range s).map (fun j => G (φ₀ + j))).prod) := by
  intro s
  induction s with
  | zero =>
    intro φ₀
    simpa using WinF_one hL.inj g (M * φ₀)
  | succ s ih =>
    intro φ₀
    rcases s with _ | s
    · simpa [starPow_one'] using hG φ₀
    · rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      have hl : List.map ((fun j => G (φ₀ + j)) ∘ Nat.succ) (List.range (s + 1)) =
          List.map (fun j => G (φ₀ + 1 + j)) (List.range (s + 1)) :=
        List.map_congr_left (fun j _ => by simp only [Function.comp]; congr 1; omega)
      rw [hl]
      have h1 := hG φ₀
      have h2 := ih (φ₀ + 1)
      have hM1 : M ≤ M * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have := WinF_mul (l := M * φ₀) (m := M * (φ₀ + 1)) (r := M * (φ₀ + 1 + (s + 1))) hL
        (by rw [mul_add, mul_one]; omega) (by rw [mul_add M (φ₀ + 1)]; omega) h1 h2
      rw [show φ₀ + 1 + (s + 1) = φ₀ + (s + 1 + 1) by omega] at this
      simpa using this

end Window

section Coeff

variable {R K : Type*} [CommRing R] [CommRing K]

/-- Ring homomorphisms commute with `starMul`. -/
lemma map_starMul (ψ : R →+* K) (f g : Finset ℕ → R) (Δ : Finset ℕ) :
    ψ (Deficit.starMul f g Δ) = Deficit.starMul (fun Γ => ψ (f Γ)) (fun Γ => ψ (g Γ)) Δ := by
  unfold Deficit.starMul
  simp [map_sum, map_mul]

/-- Ring homomorphisms commute with `starPow`. -/
lemma map_starPow (ψ : R →+* K) (f : Finset ℕ → R) (n : ℕ) (Δ : Finset ℕ) :
    ψ (starPow f n Δ) = starPow (fun Γ => ψ (f Γ)) n Δ := by
  induction n generalizing Δ with
  | zero => simp only [starPow]; split_ifs <;> simp
  | succ n ih =>
    change ψ (Deficit.starMul f (starPow f n) Δ) =
      Deficit.starMul (fun Γ => ψ (f Γ)) (starPow (fun Γ => ψ (f Γ)) n) Δ
    rw [map_starMul]
    simp only [ih]

/-- Powers keep supports: if `f` vanishes off the subsets of `T`, so does `f^{⋆n}`. -/
lemma starPow_supp {T : Finset ℕ} {f : Finset ℕ → R} (hf : ∀ Γ, ¬ Γ ⊆ T → f Γ = 0) (n : ℕ) :
    ∀ Γ, ¬ Γ ⊆ T → starPow f n Γ = 0 := by
  induction n with
  | zero =>
    intro Γ hΓ
    have : Γ ≠ ∅ := by rintro rfl; exact hΓ (empty_subset _)
    simp [starPow, this]
  | succ n ih =>
    intro Γ hΓ
    change Deficit.starMul f (starPow f n) Γ = 0
    unfold Deficit.starMul
    apply sum_eq_zero
    intro Δ₁ hΔ₁
    by_cases h1 : Δ₁ ⊆ T
    · have h2 : ¬ Γ \ Δ₁ ⊆ T := by
        intro h2; apply hΓ
        intro t ht
        by_cases htΔ : t ∈ Δ₁
        · exact h1 htΔ
        · exact h2 (mem_sdiff.2 ⟨ht, htΔ⟩)
      rw [ih _ h2, mul_zero]
    · rw [hf _ h1, zero_mul]

end Coeff

/-- `Σ_{t < h} (p − 1) p^t + 1 = p^h`. -/
lemma sum_digits_max (p : ℕ) (hp : 1 ≤ p) (h : ℕ) :
    ∑ t ∈ range h, (p - 1) * p ^ t + 1 = p ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ, pow_succ]
    have : (p - 1) * p ^ h + p ^ h = p ^ h * p := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp, mul_comm]
    omega

/-- **The window fits** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`): for
`J ⊆ [0, h)` and digits `< p`, `o(J) < p^h`. -/
lemma oW_lt {p : ℕ} (hp : 1 ≤ p) {dg : ℕ → ℕ} {h : ℕ} (hdg : ∀ t < h, dg t < p) {J : Finset ℕ}
    (hJ : ∀ t ∈ J, t < h) : oW p dg J + 1 ≤ p ^ h := by
  have h1 : oW p dg J ≤ ∑ t ∈ range h, (p - 1) * p ^ t := by
    unfold oW
    calc ∑ t ∈ J, dg t * p ^ t ≤ ∑ t ∈ J, (p - 1) * p ^ t := by
          apply sum_le_sum
          intro t ht
          exact Nat.mul_le_mul_right _ (by have := hdg t (hJ t ht); omega)
      _ ≤ ∑ t ∈ range h, (p - 1) * p ^ t :=
          sum_le_sum_of_subset (fun t ht => mem_range.2 (hJ t ht))
  have := sum_digits_max p hp h
  omega

end ColouredSand.OddTwist
