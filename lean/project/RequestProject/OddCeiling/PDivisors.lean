module

public import RequestProject.Divisors.All

/-!
# Part D of `CSI14_the_ceiling_at_p.md`: p-adic determinantal divisors

## Encoding

* Square integer matrices are `M : Matrix (Fin n) (Fin n) ℤ`; minors are C5's
  `Divisors.minor M r A B` (`det M[A, B]` for `|A| = |B| = r`, else `0`).
* The prime is `p : ℕ` with `hp : p.Prime`; the `p`-adic valuation is `padicValInt p`, and
  "`p ∤ x`" is `¬ (p : ℤ) ∣ x`.
* `minorValsP p M r = {v | ∃ A B, |A| = |B| = r ∧ minor M r A B ≠ 0 ∧ v_p(minor M r A B) = v}`
  and `ddP p M r = sInf (minorValsP p M r)` (the minimum when the set is non-empty, `0`
  otherwise, as for C5's `Divisors.dd`).
* `Σ_{i<r} e i` for `e : Fin n → ℕ` is `∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i`
  (C5's `Divisors.firstSum e r`, by definition); the identity `e r = ddP(r+1) − ddP(r)` and the
  convexity are stated in `ℤ`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Matrix Divisors

/-- *Part D* of `CSI14_the_ceiling_at_p.md`: the set of `p`-adic valuations of the non-zero
`r × r` minors of `M`. -/
def minorValsP (p : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : Set ℕ :=
  {v | ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧ minor M r A B ≠ 0 ∧
    padicValInt p (minor M r A B) = v}

/-- *Part D* of `CSI14_the_ceiling_at_p.md`: the **`p`-adic determinantal divisor**
`ddP p M r = min {v_p(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0}`. -/
noncomputable def ddP (p : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : ℕ :=
  sInf (minorValsP p M r)

/-- **(D0)** of `CSI14_the_ceiling_at_p.md`: for `p = 2`, `minorValsP` is C5's
`Divisors.minorVals`. -/
theorem D0_minorVals {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    minorValsP 2 M r = Divisors.minorVals M r := rfl

/-- **(D0)** of `CSI14_the_ceiling_at_p.md`: `ddP 2 M r = Divisors.dd M r`. -/
theorem D0_two {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    ddP 2 M r = Divisors.dd M r := rfl

section

variable {p : ℕ}

/-- Every `r × r` minor of `M` is divisible by `p^{ddP_r(M)}`. (Part D of
`CSI14_the_ceiling_at_p.md`.) -/
theorem pow_ddP_dvd_minor [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ)
    (A B : Finset (Fin n)) : (p : ℤ) ^ ddP p M r ∣ minor M r A B := by
  by_cases h : A.card = r ∧ B.card = r
  · by_cases h0 : minor M r A B = 0
    · rw [h0]; exact dvd_zero _
    · have hle : ddP p M r ≤ padicValInt p (minor M r A B) :=
        Nat.sInf_le ⟨A, B, h.1, h.2, h0, rfl⟩
      exact (pow_dvd_pow _ hle).trans (by exact_mod_cast padicValInt_dvd (p := p) _)
  · rw [minor_of_not_card _ h]; exact dvd_zero _

/-- If `p^k` divides every `r × r` minor and some such minor is non-zero, then
`k ≤ ddP_r(M)`. (Part D of `CSI14_the_ceiling_at_p.md`.) -/
theorem le_ddP_of_dvd [Fact p.Prime] {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {r k : ℕ}
    (hne : (minorValsP p M r).Nonempty)
    (h : ∀ A B : Finset (Fin n), A.card = r → B.card = r → (p : ℤ) ^ k ∣ minor M r A B) :
    k ≤ ddP p M r := by
  refine le_csInf hne ?_
  rintro v ⟨A, B, hA, hB, h0, rfl⟩
  have := (padicValInt_dvd_iff (p := p) k (minor M r A B)).1 (by exact_mod_cast h A B hA hB)
  tauto

/-- `ddP_r(M) ≤ v_p(det M[A, B])` for every non-zero `r × r` minor. (Part D of
`CSI14_the_ceiling_at_p.md`.) -/
theorem ddP_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) {r : ℕ} {A B : Finset (Fin n)}
    (hA : A.card = r) (hB : B.card = r) (h0 : minor M r A B ≠ 0) :
    ddP p M r ≤ padicValInt p (minor M r A B) :=
  Nat.sInf_le ⟨A, B, hA, hB, h0, rfl⟩

/-- `v_p(c · a) = v_p(a)` for `p ∤ c`. -/
theorem padicValInt_mul_of_not_dvd [Fact p.Prime] {c a : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (ha : a ≠ 0) : padicValInt p (c * a) = padicValInt p a := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  rw [padicValInt.mul hc0 ha, padicValInt.eq_zero_of_not_dvd hc, zero_add]

/-- `p ∤ c^r` when `p ∤ c` (`p` prime). -/
theorem not_dvd_pow_of_not_dvd (hp : p.Prime) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (r : ℕ) :
    ¬ (p : ℤ) ∣ c ^ r := fun h => hc ((Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow h)

/-- Multiplying a matrix by an integer prime to `p` does not change the valuations of its
non-zero minors. (Proof of (D1) of `CSI14_the_ceiling_at_p.md`.) -/
theorem minorValsP_smul [hp : Fact p.Prime] {n : ℕ} {c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : minorValsP p (c • M) r = minorValsP p M r := by
  have hcr : ¬ (p : ℤ) ∣ c ^ r := not_dvd_pow_of_not_dvd hp.out hc r
  have hcr0 : c ^ r ≠ 0 := by intro h; rw [h] at hcr; exact hcr (dvd_zero _)
  ext v
  simp only [minorValsP, Set.mem_setOf_eq, minor_smul]
  constructor
  · rintro ⟨A, B, hA, hB, h0, rfl⟩
    have h0' : minor M r A B ≠ 0 := right_ne_zero_of_mul h0
    exact ⟨A, B, hA, hB, h0', (padicValInt_mul_of_not_dvd hcr h0').symm⟩
  · rintro ⟨A, B, hA, hB, h0, rfl⟩
    exact ⟨A, B, hA, hB, mul_ne_zero hcr0 h0, padicValInt_mul_of_not_dvd hcr h0⟩

/-- If `P M Q` has a non-zero `r × r` minor, so does `M`. -/
theorem minorValsP_nonempty_of_mul {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) {r : ℕ}
    (h : (minorValsP p (P * M * Q) r).Nonempty) : (minorValsP p M r).Nonempty := by
  obtain ⟨_, I, J, _, _, h0, _⟩ := h
  by_contra hne
  apply h0
  refine zero_dvd_iff.1 (dvd_minor_mul_mul P M Q (fun A B hA hB => ?_) I J)
  by_contra hm
  exact hne ⟨_, A, B, hA, hB, by rwa [zero_dvd_iff] at hm, rfl⟩

/-- `ddP_r(M) ≤ ddP_r(P M Q)` as soon as `P M Q` has a non-zero `r × r` minor. -/
theorem ddP_le_ddP_mul [Fact p.Prime] {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) {r : ℕ}
    (h : (minorValsP p (P * M * Q) r).Nonempty) : ddP p M r ≤ ddP p (P * M * Q) r :=
  le_ddP_of_dvd h fun A B _ _ =>
    dvd_minor_mul_mul P M Q (fun A B _ _ => pow_ddP_dvd_minor M r A B) A B

/-- **(D1)** (invariance) of `CSI14_the_ceiling_at_p.md`: if `p ∤ det P` and `p ∤ det Q`, then
`ddP p (P * M * Q) r = ddP p M r` for every `r`. -/
theorem D1_invariance (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (r : ℕ) :
    ddP p (P * M * Q) r = ddP p M r := by
  haveI := Fact.mk hp
  have hc : ¬ (p : ℤ) ∣ det P * det Q := fun h =>
    ((Nat.prime_iff_prime_int.1 hp).dvd_or_dvd h).elim hP hQ
  have hY := adjugate_mul_mul_adjugate P M Q
  by_cases h : (minorValsP p (P * M * Q) r).Nonempty
  · have h1 := ddP_le_ddP_mul P M Q h
    have hM := minorValsP_nonempty_of_mul P M Q h
    have hcM : (minorValsP p (adjugate P * (P * M * Q) * adjugate Q) r).Nonempty := by
      rwa [hY, minorValsP_smul hc]
    have h2 := ddP_le_ddP_mul (adjugate P) (P * M * Q) (adjugate Q) hcM
    have h3 : ddP p ((det P * det Q) • M) r = ddP p M r := by
      rw [ddP, ddP, minorValsP_smul hc]
    rw [hY, h3] at h2
    omega
  · have hM : ¬ (minorValsP p M r).Nonempty := by
      intro hM
      apply h
      apply minorValsP_nonempty_of_mul (adjugate P) _ (adjugate Q)
      rwa [hY, minorValsP_smul hc]
    rw [Set.not_nonempty_iff_eq_empty] at h hM
    rw [ddP, ddP, h, hM]

/-- `Π_{i ∈ A} u_i p^{e_i}` is non-zero of `p`-adic valuation `Σ_{i ∈ A} e_i` when `p ∤ u_i`.
(Proof of (D2) of `CSI14_the_ceiling_at_p.md`.) -/
theorem padicValInt_prod_diagP (hp : p.Prime) {ι : Type*} (e : ι → ℕ) {u : ι → ℤ}
    (hu : ∀ i, ¬ (p : ℤ) ∣ u i) (A : Finset ι) :
    ∏ i ∈ A, u i * (p : ℤ) ^ e i ≠ 0 ∧
      padicValInt p (∏ i ∈ A, u i * (p : ℤ) ^ e i) = ∑ i ∈ A, e i := by
  haveI := Fact.mk hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  have hnd : ¬ (p : ℤ) ∣ ∏ i ∈ A, u i := by
    intro h
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finset_prod_iff hpZ _).1 h
    exact hu i hi
  have h0 : ∏ i ∈ A, u i ≠ 0 := by intro h; rw [h] at hnd; exact hnd (dvd_zero _)
  have h2 : (p : ℤ) ^ ∑ i ∈ A, e i ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  refine ⟨mul_ne_zero h0 h2, ?_⟩
  rw [padicValInt_mul_of_not_dvd hnd h2]
  have : ((p : ℤ) ^ ∑ i ∈ A, e i) = ((p ^ ∑ i ∈ A, e i : ℕ) : ℤ) := by push_cast; rfl
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- **(D2)** (diagonal matrices) of `CSI14_the_ceiling_at_p.md`: for `e : Fin n → ℕ` monotone
and `u : Fin n → ℤ` with `p ∤ u i`,
`ddP p (diagonal fun i => u i * p ^ e i) r = Σ_{i<r} e i` for `r ≤ n`. -/
theorem D2_diagonal (hp : p.Prime) {n : ℕ} (e : Fin n → ℕ) (he : Monotone e)
    (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) {r : ℕ} (hr : r ≤ n) :
    ddP p (diagonal fun i => u i * (p : ℤ) ^ e i) r =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i := by
  set A₀ := univ.filter (fun i : Fin n => (i : ℕ) < r)
  have hA₀ : A₀.card = r := card_filter_lt hr
  have hm₀ := padicValInt_prod_diagP hp e hu A₀
  rw [← minor_diagonal_self _ hA₀] at hm₀
  apply le_antisymm
  · exact (ddP_le _ hA₀ hA₀ hm₀.1).trans hm₀.2.le
  · refine le_csInf ⟨_, A₀, A₀, hA₀, hA₀, hm₀.1, rfl⟩ ?_
    rintro v ⟨A, B, hA, hB, h0, rfl⟩
    have hAB : A = B := by
      by_contra hne; exact h0 (minor_diagonal_of_ne _ hA hB hne)
    subst hAB
    have hm := padicValInt_prod_diagP hp e hu A
    rw [← minor_diagonal_self _ hA] at hm
    rw [hm.2]
    exact firstSum_le_sum he hr hA

/-- **(D3)** of `CSI14_the_ceiling_at_p.md` (first part): if `P M Q = diag(u_i p^{e_i})` with
`p ∤ det P`, `p ∤ det Q`, `e` monotone and `p ∤ u i`, then `ddP p M r = Σ_{i<r} e i` for
`r ≤ n`. -/
theorem D3_sum (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (e : Fin n → ℕ) (he : Monotone e)
    (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i)
    (hD : P * M * Q = diagonal fun i => u i * (p : ℤ) ^ e i) {r : ℕ} (hr : r ≤ n) :
    ddP p M r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i := by
  rw [← D1_invariance hp M P Q hP hQ r, hD, D2_diagonal hp e he u hu hr]

/-- **(D3)** of `CSI14_the_ceiling_at_p.md` (second part): under the hypotheses of (D3),
`e r = ddP p M (r+1) − ddP p M r` for `r < n`. -/
theorem D3_increment (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (e : Fin n → ℕ) (he : Monotone e)
    (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i)
    (hD : P * M * Q = diagonal fun i => u i * (p : ℤ) ^ e i) (r : Fin n) :
    (e r : ℤ) = (ddP p M (r + 1) : ℤ) - ddP p M r := by
  rw [D3_sum hp M P Q hP hQ e he u hu hD r.2, D3_sum hp M P Q hP hQ e he u hu hD r.2.le]
  have := firstSum_succ e r
  simp only [firstSum] at this
  rw [this]; push_cast; ring

/-- **(D3)** of `CSI14_the_ceiling_at_p.md` (convexity): under the hypotheses of (D3),
`ddP p M (r+1) − ddP p M r ≤ ddP p M (r+2) − ddP p M (r+1)` whenever `r + 2 ≤ n`. -/
theorem D3_convex (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (e : Fin n → ℕ) (he : Monotone e)
    (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i)
    (hD : P * M * Q = diagonal fun i => u i * (p : ℤ) ^ e i) (r : ℕ) (hr : r + 2 ≤ n) :
    (ddP p M (r + 1) : ℤ) - ddP p M r ≤ (ddP p M (r + 2) : ℤ) - ddP p M (r + 1) := by
  have h1 := D3_increment hp M P Q hP hQ e he u hu hD ⟨r, by omega⟩
  have h2 := D3_increment hp M P Q hP hQ e he u hu hD ⟨r + 1, by omega⟩
  simp only at h1 h2
  rw [← h1, ← h2]
  have : e ⟨r, by omega⟩ ≤ e ⟨r + 1, by omega⟩ := he (by simp [Fin.le_def])
  exact_mod_cast this

end

end ColouredSand.OddTwist
