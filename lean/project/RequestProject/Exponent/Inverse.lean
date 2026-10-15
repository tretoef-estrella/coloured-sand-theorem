module

public import RequestProject.Strings.StringCoker

/-!
# (C1) Lemma 4: the inverse of `M = q (c + H) + U`

This file corresponds to **(C1) Lemma 4, the inverse** of `CS4_theorem_C_exponent.md`.

## Encoding

* `B_m(K) = Finset (Fin m) → K` and `M = q (c + H) + U` is `ColouredSand.Strings.opM m K q c`
  (from `RequestProject/Strings/`), i.e. `M e_S = q (c + |S|) e_S + U e_S`.
* The matrix of `M` is `LinearMap.toMatrix' (opM m K q c)`, a matrix indexed by
  `Finset (Fin m) × Finset (Fin m)` whose `(T, S)` entry is the coefficient of `e_T` in `M e_S`.
  `(M^{−1})_{T,S}` is the `(T, S)` entry of the inverse matrix.
* `invCoeff q c s k = (−1)^k k! ∏_{i=0}^{k} 1/(q (c + s + i))`, and
  `invEntry q c T S = invCoeff q c |S| (|T| − |S|)` if `S ⊆ T`, and `0` otherwise.

## Results

* `opM_invVec` (general field): the vector `w_S = ∑_T invEntry q c T S e_T` satisfies
  `M w_S = e_S` as soon as `q (c + t) ≠ 0` for `|S| ≤ t ≤ m`.  This is the computation behind
  Lemma 4 (it is also used, for `c = 0` and `S ≠ ∅`, in the proof of Theorem C).
* `inverse_formula` (general field, more general than the file): if `q (c + t) ≠ 0` for all
  `t ≤ m`, the matrix of `M` is invertible and its inverse has entries `invEntry`.
* `lemma4`: the statement of the file, over `ℚ` with integers `q ≥ 1`, `c ≥ 1`.
-/

@[expose] public section

open Finset ColouredSand.Strings

open scoped Nat

namespace ColouredSand.Exponent

variable {m : ℕ} {K : Type*} [Field K]

/-- `(−1)^k k! ∏_{i=0}^{k} 1/(q (c + s + i))`: the value of `(M^{−1})_{T,S}` for `S ⊆ T`,
`|S| = s`, `|T| = s + k` (Lemma 4). -/
def invCoeff (q c : K) (s k : ℕ) : K :=
  (-1) ^ k * (k ! : K) * ∏ i ∈ range (k + 1), (q * (c + ((s + i : ℕ) : K)))⁻¹

/-- The entry `(M^{−1})_{T,S}` of Lemma 4: `invCoeff q c |S| (|T| − |S|)` if `S ⊆ T`, else `0`. -/
def invEntry (q c : K) (T S : Finset (Fin m)) : K :=
  if S ⊆ T then invCoeff q c S.card (T.card - S.card) else 0

/-- The column `w_S = ∑_T (M^{−1})_{T,S} e_T`. -/
def invVec (q c : K) (S : Finset (Fin m)) : B m K := fun T => invEntry q c T S

lemma opM_apply' {R : Type*} [CommRing R] (q c : R) (f : B m R) (T : Finset (Fin m)) :
    opM m R q c f T = q * (c + T.card) * f T + ∑ x ∈ T, f (T.erase x) := by
  simp [opM]
  ring

lemma invCoeff_zero (q c : K) (s : ℕ) : invCoeff q c s 0 = (q * (c + s))⁻¹ := by
  simp [invCoeff]

lemma invCoeff_succ (q c : K) (s k : ℕ) (h : q * (c + ((s + (k + 1) : ℕ) : K)) ≠ 0) :
    q * (c + ((s + (k + 1) : ℕ) : K)) * invCoeff q c s (k + 1) =
      -(((k + 1 : ℕ) : K) * invCoeff q c s k) := by
  unfold invCoeff
  rw [prod_range_succ _ (k + 1), Nat.factorial_succ]
  set P := ∏ i ∈ range (k + 1), (q * (c + ((s + i : ℕ) : K)))⁻¹
  have h1 := mul_inv_cancel₀ h
  push_cast at h1 ⊢
  linear_combination ((-1) ^ (k + 1) * (((k : K) + 1) * (k ! : K)) * P) * h1

/-- **The computation behind Lemma 4.**  If `q (c + t) ≠ 0` for every `t` with `|S| ≤ t ≤ m`,
then `M w_S = e_S`, where `w_S = invVec q c S` has coefficients `invEntry q c T S`. -/
theorem opM_invVec (q c : K) (S : Finset (Fin m))
    (h : ∀ t : ℕ, S.card ≤ t → t ≤ m → q * (c + (t : K)) ≠ 0) :
    opM m K q c (invVec q c S) = Pi.single S 1 := by
  funext T
  rw [opM_apply']
  simp only [invVec, invEntry]
  by_cases hST : S ⊆ T
  · by_cases hTS : T = S
    · subst hTS
      have hz : ∀ x ∈ T, (if T ⊆ T.erase x then invCoeff q c T.card ((T.erase x).card - T.card)
          else 0) = 0 := by
        intro x hx
        rw [if_neg]
        intro hsub
        exact (Finset.notMem_erase x T) (hsub hx)
      rw [sum_congr rfl hz, sum_const_zero, if_pos subset_rfl, Nat.sub_self, invCoeff_zero]
      have := h T.card le_rfl (by simpa using card_le_univ T)
      rw [mul_inv_cancel₀ this]
      simp
    · rw [Pi.single_eq_of_ne hTS, if_pos hST]
      have hlt : S.card < T.card := card_lt_card (ssubset_of_subset_of_ne hST (Ne.symm hTS))
      obtain ⟨k, hk⟩ : ∃ k, T.card = S.card + (k + 1) := ⟨T.card - S.card - 1, by omega⟩
      have hterm : ∀ x ∈ T, (if S ⊆ T.erase x then
          invCoeff q c S.card ((T.erase x).card - S.card) else 0) =
          if x ∈ T \ S then invCoeff q c S.card k else 0 := by
        intro x hx
        have hcard : (T.erase x).card - S.card = k := by
          rw [card_erase_of_mem hx]; omega
        by_cases hxS : x ∈ S
        · rw [if_neg, if_neg]
          · simp [hxS]
          · intro hsub; exact (Finset.notMem_erase x T) (hsub hxS)
        · rw [if_pos, if_pos, hcard]
          · simp [hx, hxS]
          · intro y hy
            exact mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hST hy⟩
      rw [sum_congr rfl hterm, sum_ite_mem, inter_eq_right.mpr sdiff_subset, sum_const,
        card_sdiff_of_subset hST, nsmul_eq_mul]
      have hTk : T.card - S.card = k + 1 := by omega
      rw [hTk]
      have hne := h (S.card + (k + 1)) (by omega) (by rw [← hk]; simpa using card_le_univ T)
      have key := invCoeff_succ q c S.card k (by exact_mod_cast hne)
      rw [hk]
      push_cast at key ⊢
      rw [key]
      ring
  · rw [if_neg hST, Pi.single_eq_of_ne (by rintro rfl; exact hST subset_rfl)]
    have hz : ∀ x ∈ T, (if S ⊆ T.erase x then
        invCoeff q c S.card ((T.erase x).card - S.card) else 0) = 0 := by
      intro x _
      rw [if_neg]
      intro hsub
      exact hST (hsub.trans (erase_subset x T))
    rw [sum_congr rfl hz]
    simp

/-- **Lemma 4, over a general field** (more general than the file).  If `q (c + t) ≠ 0` for all
`t ≤ m`, then the matrix of `M = q (c + H) + U` is invertible and
`(M^{−1})_{T,S} = invEntry q c T S`, i.e. `(−1)^k k! ∏_{i=0}^{k} 1/(q (c + s + i))` when `S ⊆ T`,
`|S| = s`, `|T| = s + k`, and `0` when `S ⊄ T`. -/
theorem inverse_formula (q c : K) (h : ∀ t : ℕ, t ≤ m → q * (c + (t : K)) ≠ 0) :
    IsUnit (LinearMap.toMatrix' (opM m K q c)) ∧
      ∀ T S : Finset (Fin m), (LinearMap.toMatrix' (opM m K q c))⁻¹ T S = invEntry q c T S := by
  set A := LinearMap.toMatrix' (opM m K q c)
  have hAN : A * Matrix.of (fun T S => invEntry q c T S) = 1 := by
    ext T S
    have hS := opM_invVec q c S (fun t _ ht => h t ht)
    have := congrFun hS T
    rw [← LinearMap.toMatrix'_mulVec] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, invVec, Pi.single_apply, eq_comm] using this
  refine ⟨IsUnit.of_mul_eq_one _ hAN, fun T S => ?_⟩
  rw [Matrix.inv_eq_right_inv hAN]
  rfl

/-- **(C1) Lemma 4.**  Let `q ≥ 1`, `c ≥ 1` and `M = q (c + H) + U` on `B_m(ℚ)`.  Then `M` is
invertible, and for subsets `S, T` of `[m]`:
* if `S ⊆ T` with `|S| = s` and `|T| = s + k`, then
  `(M^{−1})_{T,S} = (−1)^k k! ∏_{i=0}^{k} 1/(q (c + s + i))`;
* `(M^{−1})_{T,S} = 0` if `S ⊄ T`.

Encoding: `M` is `opM m ℚ q c`; its matrix is `LinearMap.toMatrix'` of it (the `(T, S)` entry is
the coefficient of `e_T` in `M e_S`), and `M^{−1}` is the inverse matrix. -/
theorem lemma4 (m q c : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c) :
    IsUnit (LinearMap.toMatrix' (opM m ℚ (q : ℚ) (c : ℚ))) ∧
      ∀ S T : Finset (Fin m),
        (S ⊆ T → ∀ s k : ℕ, S.card = s → T.card = s + k →
          (LinearMap.toMatrix' (opM m ℚ (q : ℚ) (c : ℚ)))⁻¹ T S =
            (-1) ^ k * (k ! : ℚ) * ∏ i ∈ range (k + 1), 1 / ((q : ℚ) * (c + s + i))) ∧
        (¬ S ⊆ T → (LinearMap.toMatrix' (opM m ℚ (q : ℚ) (c : ℚ)))⁻¹ T S = 0) := by
  have h : ∀ t : ℕ, t ≤ m → (q : ℚ) * ((c : ℚ) + (t : ℚ)) ≠ 0 := by
    intro t _
    have : (0 : ℚ) < (q : ℚ) * ((c : ℚ) + (t : ℚ)) := by
      have : (1 : ℚ) ≤ q := by exact_mod_cast hq
      have : (1 : ℚ) ≤ c := by exact_mod_cast hc
      positivity
    exact this.ne'
  obtain ⟨hU, hinv⟩ := inverse_formula (m := m) (q : ℚ) (c : ℚ) h
  refine ⟨hU, fun S T => ⟨fun hST s k hs ht => ?_, fun hST => ?_⟩⟩
  · rw [hinv, invEntry, if_pos hST, invCoeff, ht, hs, Nat.add_sub_cancel_left]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    push_cast
    rw [one_div, add_assoc]
  · rw [hinv, invEntry, if_neg hST]

end ColouredSand.Exponent
