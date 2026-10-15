module

public import RequestProject.Divisors.Invariance

/-!
# Lemma A2 and Corollary A3 of `C5_divisors_theorem_65.md`

## Encoding

* The exponents `e_0 ≤ ⋯ ≤ e_{n−1}` are `e : Fin n → ℕ` with `Monotone e`, the odd units are
  `u : Fin n → ℤ` with `∀ i, Odd (u i)`, and
  `D = diag(u_0 2^{e_0}, …, u_{n−1} 2^{e_{n−1}})` is `diagonal fun i => u i * 2 ^ e i`.
* The sum `e_0 + ⋯ + e_{r−1}` of the first `r` exponents is
  `∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i`.
* `dd M r = dd_r(M)` and `minor M r A B = det M[A, B]` as in `Basic.lean`.  The identity
  `e_r = dd_{r+1}(M) − dd_r(M)` and the convexity are stated in `ℤ`.
-/

@[expose] public section

namespace Divisors

open Finset Matrix

variable {n : ℕ}

/-- The sum `e_0 + ⋯ + e_{r−1}` of the first `r` exponents. (Notation of Lemma A2 of
`C5_divisors_theorem_65.md`.) -/
def firstSum (e : Fin n → ℕ) (r : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i

/-- A minor `det D[A, B]` of a diagonal matrix vanishes unless `A = B`. (Proof of Lemma A2 of
`C5_divisors_theorem_65.md`.) -/
theorem minor_diagonal_of_ne (d : Fin n → ℤ) {r : ℕ} {A B : Finset (Fin n)}
    (hA : A.card = r) (hB : B.card = r) (hAB : A ≠ B) : minor (diagonal d) r A B = 0 := by
  have hnot : ¬ A ⊆ B := fun hsub => hAB (eq_of_subset_of_card_le hsub (by omega))
  obtain ⟨a, haA, haB⟩ := not_subset.1 hnot
  rw [minor_of_card _ hA hB]
  have hk : a ∈ Set.range (A.orderEmbOfFin hA) := by simpa using haA
  obtain ⟨k, hk⟩ := hk
  refine det_eq_zero_of_row_eq_zero k fun j => ?_
  have hj : B.orderEmbOfFin hB j ∈ B := orderEmbOfFin_mem _ _ _
  simp only [submatrix_apply, hk]
  exact diagonal_apply_ne _ (fun h => haB (h ▸ hj))

/-- The principal minor `det D[A, A]` of a diagonal matrix is `Π_{i ∈ A} d_i`. (Proof of
Lemma A2 of `C5_divisors_theorem_65.md`.) -/
theorem minor_diagonal_self (d : Fin n → ℤ) {r : ℕ} {A : Finset (Fin n)} (hA : A.card = r) :
    minor (diagonal d) r A A = ∏ i ∈ A, d i := by
  rw [minor_of_card _ hA hA, submatrix_diagonal _ _ (A.orderEmbOfFin hA).injective, det_diagonal]
  conv_rhs => rw [← image_orderEmbOfFin_univ A hA]
  rw [prod_image (fun x _ y _ h => (A.orderEmbOfFin hA).injective h)]
  rfl

/-- `Π_{i ∈ A} u_i 2^{e_i}` is non-zero of 2-adic valuation `Σ_{i ∈ A} e_i`. (Proof of
Lemma A2 of `C5_divisors_theorem_65.md`.) -/
theorem padicValInt_prod_diag (e : Fin n → ℕ) {u : Fin n → ℤ} (hu : ∀ i, Odd (u i))
    (A : Finset (Fin n)) :
    ∏ i ∈ A, u i * 2 ^ e i ≠ 0 ∧ padicValInt 2 (∏ i ∈ A, u i * 2 ^ e i) = ∑ i ∈ A, e i := by
  rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  have hodd : Odd (∏ i ∈ A, u i) :=
    prod_induction _ Odd (fun _ _ => Odd.mul) odd_one (fun i _ => hu i)
  have h0 : ∏ i ∈ A, u i ≠ 0 := by intro h; rw [h] at hodd; simp at hodd
  have h2 : (2 : ℤ) ^ ∑ i ∈ A, e i ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨mul_ne_zero h0 h2, ?_⟩
  rw [padicValInt_odd_mul hodd h2]
  have : ((2 : ℤ) ^ ∑ i ∈ A, e i) = ((2 ^ ∑ i ∈ A, e i : ℕ) : ℤ) := by push_cast; rfl
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- The `k`-th element of an `r`-subset of `{0, …, n−1}` in increasing order is at least `k`.
(Proof of Lemma A2 of `C5_divisors_theorem_65.md`.) -/
theorem le_orderEmbOfFin {r : ℕ} {A : Finset (Fin n)} (hA : A.card = r) :
    ∀ (k : ℕ) (hk : k < r), k ≤ (A.orderEmbOfFin hA ⟨k, hk⟩ : ℕ) := by
  intro k
  induction k with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : A.orderEmbOfFin hA ⟨k, by omega⟩ < A.orderEmbOfFin hA ⟨k + 1, hk⟩ :=
      (A.orderEmbOfFin hA).strictMono (by simp [Fin.lt_def])
    rw [Fin.lt_def] at h2
    omega

/-- The set `{0, …, r − 1}` inside `Fin n`, for `r ≤ n`. -/
theorem filter_lt_eq_map {r : ℕ} (hr : r ≤ n) :
    univ.filter (fun i : Fin n => (i : ℕ) < r) = univ.map (Fin.castLEEmb hr) := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
  constructor
  · intro h; exact ⟨⟨i, h⟩, rfl⟩
  · rintro ⟨k, rfl⟩; simp

/-- For `e` non-decreasing, the `r` smallest exponents are `e_0, …, e_{r−1}`: every `r`-subset
`A` has `Σ_{i ∈ A} e_i ≥ e_0 + ⋯ + e_{r−1}`. (Proof of Lemma A2 of
`C5_divisors_theorem_65.md`.) -/
theorem firstSum_le_sum {e : Fin n → ℕ} (he : Monotone e) {r : ℕ} (hr : r ≤ n)
    {A : Finset (Fin n)} (hA : A.card = r) : firstSum e r ≤ ∑ i ∈ A, e i := by
  rw [firstSum, filter_lt_eq_map hr, sum_map]
  conv_rhs => rw [← image_orderEmbOfFin_univ A hA]
  rw [sum_image (fun x _ y _ h => (A.orderEmbOfFin hA).injective h)]
  refine sum_le_sum fun k _ => he ?_
  rw [Fin.le_def]
  simpa using le_orderEmbOfFin hA k.1 k.2

theorem card_filter_lt {r : ℕ} (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by
  rw [filter_lt_eq_map hr, card_map, card_univ, Fintype.card_fin]

/-- **Lemma A2** (diagonal matrices) of `C5_divisors_theorem_65.md`: for natural numbers
`e_0 ≤ ⋯ ≤ e_{n−1}` and odd integers `u_0, …, u_{n−1}`, the matrix
`D = diag(u_0 2^{e_0}, …, u_{n−1} 2^{e_{n−1}})` satisfies `dd_r(D) = e_0 + ⋯ + e_{r−1}` for
every `0 ≤ r ≤ n`. -/
theorem lemma_A2 (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ) (hu : ∀ i, Odd (u i))
    {r : ℕ} (hr : r ≤ n) :
    dd (diagonal fun i => u i * 2 ^ e i) r =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i := by
  set A₀ := univ.filter (fun i : Fin n => (i : ℕ) < r)
  have hA₀ : A₀.card = r := card_filter_lt hr
  have hm₀ := padicValInt_prod_diag e hu A₀
  rw [← minor_diagonal_self _ hA₀] at hm₀
  apply le_antisymm
  · exact (dd_le _ hA₀ hA₀ hm₀.1).trans hm₀.2.le
  · refine le_csInf ⟨_, A₀, A₀, hA₀, hA₀, hm₀.1, rfl⟩ ?_
    rintro v ⟨A, B, hA, hB, h0, rfl⟩
    have hAB : A = B := by
      by_contra hne; exact h0 (minor_diagonal_of_ne _ hA hB hne)
    subst hAB
    have hm := padicValInt_prod_diag e hu A
    rw [← minor_diagonal_self _ hA] at hm
    rw [hm.2]
    exact firstSum_le_sum he hr hA

/-- **Corollary A3** (first part) of `C5_divisors_theorem_65.md`: if `P M Q = D` with `det P`,
`det Q` odd and `D = diag(u_0 2^{e_0}, …, u_{n−1} 2^{e_{n−1}})` as in Lemma A2, then
`dd_r(M) = e_0 + ⋯ + e_{r−1}` for every `0 ≤ r ≤ n`.  (The hypothesis `det M ≠ 0` of the
setting is not needed.) -/
theorem corollary_A3_sum (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P))
    (hQ : Odd (det Q)) (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ)
    (hu : ∀ i, Odd (u i)) (hD : P * M * Q = diagonal fun i => u i * 2 ^ e i) {r : ℕ}
    (hr : r ≤ n) :
    dd M r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i := by
  rw [← lemma_A1 M P Q hP hQ r, hD, lemma_A2 e he u hu hr]

/-- `e_0 + ⋯ + e_r = (e_0 + ⋯ + e_{r−1}) + e_r`. -/
theorem firstSum_succ (e : Fin n → ℕ) (i : Fin n) :
    firstSum e (i + 1) = firstSum e i + e i := by
  rw [firstSum, firstSum, show univ.filter (fun j : Fin n => (j : ℕ) < i + 1)
      = insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) by
        ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega,
    sum_insert (by simp), add_comm]

/-- **Corollary A3** (second part) of `C5_divisors_theorem_65.md`: under the hypotheses of
Corollary A3, the exponents are the increments: `e_r = dd_{r+1}(M) − dd_r(M)` for
`0 ≤ r < n`. -/
theorem corollary_A3_increment (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P))
    (hQ : Odd (det Q)) (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ)
    (hu : ∀ i, Odd (u i)) (hD : P * M * Q = diagonal fun i => u i * 2 ^ e i) (r : Fin n) :
    (e r : ℤ) = (dd M (r + 1) : ℤ) - dd M r := by
  rw [corollary_A3_sum M P Q hP hQ e he u hu hD r.2,
    corollary_A3_sum M P Q hP hQ e he u hu hD r.2.le]
  have := firstSum_succ e r
  simp only [firstSum] at this
  rw [this]; push_cast; ring

/-- **Corollary A3** (convexity) of `C5_divisors_theorem_65.md`: under the hypotheses of
Corollary A3, `r ↦ dd_r(M)` is convex: `dd_{r+1} − dd_r ≤ dd_{r+2} − dd_{r+1}` whenever
`r + 2 ≤ n`. -/
theorem corollary_A3_convex (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P))
    (hQ : Odd (det Q)) (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ)
    (hu : ∀ i, Odd (u i)) (hD : P * M * Q = diagonal fun i => u i * 2 ^ e i) (r : ℕ)
    (hr : r + 2 ≤ n) :
    (dd M (r + 1) : ℤ) - dd M r ≤ (dd M (r + 2) : ℤ) - dd M (r + 1) := by
  have h1 := corollary_A3_increment M P Q hP hQ e he u hu hD ⟨r, by omega⟩
  have h2 := corollary_A3_increment M P Q hP hQ e he u hu hD ⟨r + 1, by omega⟩
  simp only at h1 h2
  rw [← h1, ← h2]
  have : e ⟨r, by omega⟩ ≤ e ⟨r + 1, by omega⟩ := he (by simp [Fin.le_def])
  exact_mod_cast this

end Divisors
