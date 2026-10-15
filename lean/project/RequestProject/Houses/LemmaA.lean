module

public import RequestProject.Houses.Basic

/-!
# Part A of `C6_houses_windows_penalties.md`: the house and its penalties (Lemma 7.5)

**Lemma A0**, **Lemma A** (Lemma 7.5) with the «exactly one is zero» claim, and **Lemma A′**.
Encodings as in `RequestProject/Houses/Basic.lean`: the house `H = (I, k, ℓ, α)` is given by
its components, `R_H = RH I k ℓ α`, `J_H = JH k ℓ`, `x_H = xH I k ℓ α`, `ĉ_H = cHatH I k ℓ α`,
`r_k(μ) = r k μ`, `K = 2 ^ k`.  In Lemma A and Lemma A′ the residue `ℓ` is `μ % 2 ^ k`
(resp. `m % 2 ^ k`), so `ℓ < 2^k` holds automatically.
-/

@[expose] public section

namespace Houses

open Finset Rulers

variable {I : Finset ℕ} {k : ℕ}

/-- **Lemma A0**, antisymmetry, of `C6_houses_windows_penalties.md`: for `D ⊆ I`,
`x_H(I ∖ D) = −x_H(D)`.  (More general than the file: neither `I ⊆ {0, …, k − 1}` nor
`ℓ < 2^k` is needed.) -/
theorem lemma_A0_antisymm (ℓ : ℕ) (α : ℤ) {D : Finset ℕ} (hD : D ⊆ I) :
    xH I k ℓ α (I \ D) = -xH I k ℓ α D := by
  unfold xH; rw [sdiff_sdiff_eq_self hD]; ring

/-- **Lemma A0**, up-set, of `C6_houses_windows_penalties.md`: for `E, F` with `o_E ≤ o_F`,
`J_H(E) ≤ J_H(F)`.  (More general than the file: `E, F ⊆ I` and the house conditions are not
needed.) -/
theorem lemma_A0_upset (ℓ : ℕ) {E F : Finset ℕ} (hEF : oE E ≤ oE F) : JH k ℓ E ≤ JH k ℓ F := by
  unfold JH; split_ifs <;> omega

/-- **Lemma A (Lemma 7.5)** of `C6_houses_windows_penalties.md`: for every `μ ≥ 0`, with
`ℓ := μ mod 2^k` and `H = (I, k, ℓ, α)`, and every `E ⊆ I`,
`R_μ(E) = R_H(E) − r_k(μ) · J_H(E)` (here `R_μ = Rulers.ruler k I α μ`). -/
theorem lemma_A (hI : ∀ t ∈ I, t < k) (α : ℤ) (μ : ℕ) {E : Finset ℕ} (hE : E ⊆ I) :
    ruler k I α μ E = RH I k (μ % 2 ^ k) α E - (r k μ : ℤ) * JH k (μ % 2 ^ k) E := by
  have hx := oE_lt E k (fun t ht => hI t (hE ht))
  unfold RH JH ruler r
  rw [kappa_split k μ (oE E) hx]
  ring

/-- **Lemma A (Lemma 7.5)**, last claim, of `C6_houses_windows_penalties.md`: for every `m ≥ 0`,
exactly one of `r_k(m)` and `r_k(m + K)` is `0`. -/
theorem lemma_A_exactly_one_zero (k m : ℕ) : Xor' (r k m = 0) (r k (m + 2 ^ k) = 0) := by
  unfold r
  rw [Nat.add_div_right _ (Nat.two_pow_pos k)]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h
  · left
    refine ⟨v2_succ_of_even h, ?_⟩
    rw [v2_succ_of_odd (by omega)]; omega
  · right
    refine ⟨v2_succ_of_even (by omega), ?_⟩
    rw [v2_succ_of_odd h]; omega

/-- **Lemma A′** (the cell is a penalty cell), costs, of `C6_houses_windows_penalties.md`: for
`m ≥ 0`, `ℓ := m mod 2^k`, `H = (I, k, ℓ, α)`, `P_r := r_k(m)`, `P_c := r_k(m + K)` and
`a, b ⊆ I`: `ĉ(a, b) = ĉ_H(a, b) − P_r J_H(a) + P_c J_H(b)`, where
`ĉ = GoldenMatching.cHat k I α m`. -/
theorem lemma_A'_cost (hI : ∀ t ∈ I, t < k) (α : ℤ) (m : ℕ) {a b : Finset ℕ} (ha : a ⊆ I)
    (hb : b ⊆ I) :
    GoldenMatching.cHat k I α m a b = cHatH I k (m % 2 ^ k) α a b
      - (r k m : ℤ) * JH k (m % 2 ^ k) a + (r k (m + 2 ^ k) : ℤ) * JH k (m % 2 ^ k) b := by
  have h1 := lemma_A hI α m ha
  have h2 := lemma_A hI α (m + 2 ^ k) hb
  rw [Nat.add_mod_right] at h2
  unfold GoldenMatching.cHat cHatH
  rw [h1, h2]
  ring

/-- **Lemma A′** (the cell is a penalty cell), clocks, of `C6_houses_windows_penalties.md`: for
`m ≥ 0`, `ℓ := m mod 2^k`, `H = (I, k, ℓ, α)`, `P_r := r_k(m)`, `P_c := r_k(m + K)` and `D ⊆ I`:
`R_m(D) − R_{m+K}(I ∖ D) = x_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)`. -/
theorem lemma_A'_clock (hI : ∀ t ∈ I, t < k) (α : ℤ) (m : ℕ) {D : Finset ℕ} (hD : D ⊆ I) :
    ruler k I α m D - ruler k I α (m + 2 ^ k) (I \ D) = xH I k (m % 2 ^ k) α D
      - (r k m : ℤ) * JH k (m % 2 ^ k) D + (r k (m + 2 ^ k) : ℤ) * JH k (m % 2 ^ k) (I \ D) := by
  have h1 := lemma_A hI α m hD
  have h2 := lemma_A hI α (m + 2 ^ k) (sdiff_subset (s := I) (t := D))
  rw [Nat.add_mod_right] at h2
  unfold xH
  rw [h1, h2]
  ring

end Houses
