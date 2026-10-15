module

public import RequestProject.OddHouses.Basic

/-!
# `CSI15_houses_at_p.md` — **Part A**: the house and its penalties (Lemma 7.5_p)

Namespace `ColouredSand.OddTwist`; encodings as in `RequestProject/OddHouses/Basic.lean`: the
house `H = (I, k, ℓ, e, d)` is given by its components, `R_H = RHP p k I dg ℓ e`,
`J_H = JHP p k dg ℓ`, `x_H = xHP p k I dg ℓ e`, `ĉ_H = cHatHP p k I dg ℓ e`, `r_k(μ) = rP p k μ`.
The ruler `R_μ` (with `e ∈ ℤ`) is `RHP p k I dg μ e` (for `e ∈ ℕ` it is CSI13's `rulerP`,
`RHP_eq_rulerP`); the top digit is `dk` and `K = d_k p^k` is `dk * p ^ k`.  In (A1) and (A3) the
residue `ℓ` is `μ % p ^ k` (resp. `m % p ^ k`), so `ℓ < p^k` holds automatically.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

variable {p : ℕ} {I : Finset ℕ} {k : ℕ} {dg : ℕ → ℕ}

/-- **(A0)**, antisymmetry, of `CSI15_houses_at_p.md` (Part A): for `D ⊆ I`,
`x_H(I ∖ D) = −x_H(D)`.  (More general than the file: no hypothesis on `p`, `ℓ`, the digits or
`I ⊆ {0, …, k − 1}` is needed.) -/
theorem houseP_A0_antisymm (ℓ : ℕ) (e : ℤ) {D : Finset ℕ} (hD : D ⊆ I) :
    xHP p k I dg ℓ e (I \ D) = -xHP p k I dg ℓ e D := by
  unfold xHP; rw [sdiff_sdiff_eq_self hD]; ring

/-- **(A0)**, up-set, of `CSI15_houses_at_p.md` (Part A): `o_E ≤ o_F ⟹ J_H(E) ≤ J_H(F)`.
(More general than the file: no hypothesis is needed.) -/
theorem houseP_A0_upset (ℓ : ℕ) {E F : Finset ℕ} (hEF : oW p dg E ≤ oW p dg F) :
    JHP p k dg ℓ E ≤ JHP p k dg ℓ F := by
  unfold JHP; split_ifs <;> omega

/-- **(A2)**, first claim, of `CSI15_houses_at_p.md` (Part A): `m + K` has the same residue
`ℓ = m mod p^k` as `m`, for `K = d_k p^k`.  (No hypothesis is needed.) -/
theorem houseP_A2_residue (p k dk m : ℕ) : (m + dk * p ^ k) % p ^ k = m % p ^ k :=
  Nat.add_mul_mod_self_right m dk (p ^ k)

section prime

variable [hp : Fact p.Prime]

/-- **(A1)** of `CSI15_houses_at_p.md` (Part A, Lemma 7.5_p): for every `μ ≥ 0`, with
`ℓ := μ mod p^k` and every `E ⊆ I`, `R_μ(E) = R_H(E) − r_k(μ)·J_H(E)`. -/
theorem houseP_A1 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ)
    (μ : ℕ) {E : Finset ℕ} (hE : E ⊆ I) :
    RHP p k I dg μ e E =
      RHP p k I dg (μ % p ^ k) e E - (rP p k μ : ℤ) * JHP p k dg (μ % p ^ k) E := by
  have hx : oW p dg E < p ^ k := oW_lt_pow oddHou_two_le_p dg E (fun t ht => hI t (hE ht))
    (fun t ht => by have := hd t (hE ht); have := oddHou_two_le_p (p := p); omega)
  unfold RHP JHP rP
  rw [kappaP_split k μ _ hx]
  ring

/-- **(A1)** of `CSI15_houses_at_p.md` (Part A, Lemma 7.5_p), stated with CSI13's ruler
`rulerP` (for `e` a natural number): `R_μ(E) = R_H(E) − r_k(μ)·J_H(E)` with `ℓ = μ mod p^k`. -/
theorem houseP_A1_rulerP (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℕ)
    (μ : ℕ) {E : Finset ℕ} (hE : E ⊆ I) :
    rulerP p e k I dg μ E =
      RHP p k I dg (μ % p ^ k) e E - (rP p k μ : ℤ) * JHP p k dg (μ % p ^ k) E :=
  houseP_A1 hI hd e μ hE

/-- **(A2)**, second claim, of `CSI15_houses_at_p.md` (Part A, Lemma 7.5_p): with
`K = d_k p^k`, `1 ≤ d_k ≤ p − 1` and `m ≥ 0`, at most one of `r_k(m)`, `r_k(m + K)` is
non-zero. -/
theorem houseP_A2_at_most_one (k dk m : ℕ) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1) :
    rP p k m = 0 ∨ rP p k (m + dk * p ^ k) = 0 := by
  have h2 := oddHou_two_le_p (p := p)
  unfold rP
  rw [Nat.add_mul_div_right _ _ (pow_pos (by omega) k)]
  set q := m / p ^ k
  by_cases hq : q % p = p - 1
  · right
    apply vP_succ_of_ne
    have hd := Nat.mod_add_div q p
    rw [show q + dk = (dk - 1) + p * (q / p + 1) by rw [Nat.mul_add]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · left; exact vP_succ_of_ne hq

end prime

/-- **(A2)**, remark, of `CSI15_houses_at_p.md` (Part A): for odd `p` both `r_k(m)` and
`r_k(m + K)` can be `0` (here `m = 0`, `d_k = 1`, for every `p ≥ 3` and every `k`; primality
is not needed). -/
theorem houseP_A2_both_zero (hp3 : 3 ≤ p) (k : ℕ) :
    rP p k 0 = 0 ∧ rP p k (0 + 1 * p ^ k) = 0 := by
  have hpk : 0 < p ^ k := pow_pos (by omega) k
  unfold rP
  rw [Nat.zero_div, zero_add, zero_add, one_mul, Nat.div_self hpk]
  refine ⟨by simp, padicValNat.eq_zero_of_not_dvd ?_⟩
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

/-- **(A2)**, remark, of `CSI15_houses_at_p.md` (Part A): for `p = 2` (so `d_k = 1`, `K = 2^k`)
**exactly one** of `r_k(m)`, `r_k(m + K)` is `0` (this is C6's `Houses.lemma_A_exactly_one_zero`;
`rP 2` is C6's `Houses.r`). -/
theorem houseP_A2_two (k m : ℕ) : Xor' (rP 2 k m = 0) (rP 2 k (m + 1 * 2 ^ k) = 0) := by
  rw [one_mul]; exact Houses.lemma_A_exactly_one_zero k m

section prime

variable [hp : Fact p.Prime]

/-- **(A3) The penalty cell**, costs, of `CSI15_houses_at_p.md` (Part A, Lemma 7.5_p): for `m ≥ 0`,
`ℓ = m mod p^k`, `P_r := r_k(m)`, `P_c := r_k(m + K)` (`K = d_k p^k`) and `a, b ⊆ I`:
`R_m(a) − R_{m+K}(b) + γ(a ∖ b) = ĉ_H(a, b) − P_r J_H(a) + P_c J_H(b)`.
(More general than the file: no condition on `d_k` is needed.) -/
theorem houseP_A3_cost (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ)
    (dk m : ℕ) {a b : Finset ℕ} (ha : a ⊆ I) (hb : b ⊆ I) :
    RHP p k I dg m e a - RHP p k I dg (m + dk * p ^ k) e b + Rulers.gamma k I (a \ b) =
      cHatHP p k I dg (m % p ^ k) e a b - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) a
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) b := by
  have h1 := houseP_A1 hI hd e m ha
  have h2 := houseP_A1 hI hd e (m + dk * p ^ k) hb
  rw [houseP_A2_residue] at h2
  unfold cHatHP
  rw [h1, h2]
  ring

/-- **(A3) The penalty cell**, clocks, of `CSI15_houses_at_p.md` (Part A, Lemma 7.5_p): for
`m ≥ 0`, `ℓ = m mod p^k`, `P_r := r_k(m)`, `P_c := r_k(m + K)` and `D ⊆ I`:
`R_m(D) − R_{m+K}(I ∖ D) = x_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)`.
(More general than the file: no condition on `d_k` is needed.) -/
theorem houseP_A3_clock (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ)
    (dk m : ℕ) {D : Finset ℕ} (hD : D ⊆ I) :
    RHP p k I dg m e D - RHP p k I dg (m + dk * p ^ k) e (I \ D) =
      xHP p k I dg (m % p ^ k) e D - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) D
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) (I \ D) := by
  have h1 := houseP_A1 hI hd e m hD
  have h2 := houseP_A1 hI hd e (m + dk * p ^ k) (sdiff_subset (s := I) (t := D))
  rw [houseP_A2_residue] at h2
  unfold xHP
  rw [h1, h2]
  ring

end prime

end ColouredSand.OddTwist
