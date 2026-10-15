module

public import RequestProject.OddCeiling.PDivisors
public import RequestProject.DanceSmith.SmithForm

/-!
# Part Q of `CSI14_the_ceiling_at_p.md`: the Smith form at p of an integer matrix

The `p`-analogue of C15's `DanceSmith.Q1` / `DanceSmith.Q2`.

## Encoding

* Square integer matrices are `A : Matrix (Fin n) (Fin n) ℤ`; the prime is `p : ℕ` with
  `hp : p.Prime`; "`p ∤ det P`" is `¬ (p : ℤ) ∣ P.det`.
* The Smith form at `p` is `P * A * Q = diagonal D` with
  `D j = if (j : ℕ) < ρ then u j * p ^ e j else 0`, where `ρ ≤ n`, `e : ℕ → ℕ` is
  non-decreasing on `[0, ρ)` (`∀ i j, i ≤ j → j < ρ → e i ≤ e j`) and `u : ℕ → ℤ` with
  `∀ j, ¬ (p : ℤ) ∣ u j`.
* `Σ_{j<r} e j` is `∑ j ∈ Finset.range r, e j`; `ddP` is the `p`-adic determinantal divisor of
  Part D (`PDivisors.lean`); minors are C5's `Divisors.minor`.

The existence (Q1) is proved by elimination with a pivot of least `p`-valuation: every row and
column operation used multiplies the determinant by an integer prime to `p` (a pivot cofactor
`w` with `p ∤ w`, or `±1` for permutations), which clears denominators directly; then a
permutation sorts the diagonal by `p`-valuation, zeros last.  Mathlib's Smith normal form is not
used.  The block-matrix helpers `DanceSmith.blk`, … of C15 are reused.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Matrix DanceSmith

variable {p : ℕ}

/-- A permutation matrix has determinant prime to `p` (it is `±1`). (Auxiliary for (Q1) of
`CSI14_the_ceiling_at_p.md`.) -/
lemma not_dvd_det_perm (hp : p.Prime) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ¬ (p : ℤ) ∣ (σ.permMatrix ℤ).det := by
  rw [det_permutation]
  have h1 : ¬ (p : ℤ) ∣ 1 := fun h => (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_dvd_one h)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using h1

/-- `p ∤ a`, `p ∤ b` imply `p ∤ a b`. -/
lemma not_dvd_mul_of (hp : p.Prime) {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ a * b := fun h =>
  ((Nat.prime_iff_prime_int.1 hp).dvd_or_dvd h).elim ha hb

lemma p_pow_padicValInt_dvd [Fact p.Prime] (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  exact_mod_cast padicValInt_dvd (p := p) a

lemma not_p_pow_succ_dvd (hp : p.Prime) {a : ℤ} (ha : a ≠ 0) :
    ¬ (p : ℤ) ^ (padicValInt p a + 1) ∣ a := by
  haveI := Fact.mk hp
  intro h
  have := (padicValInt_dvd_iff (p := p) (padicValInt p a + 1) a).1 (by exact_mod_cast h)
  omega

/-- For `a ≠ 0`, `a = u · p^{v_p(a)}` with `p ∤ u`. (Auxiliary for (Q1) of
`CSI14_the_ceiling_at_p.md`.) -/
lemma not_dvd_div_p_pow (hp : p.Prime) {a : ℤ} (ha : a ≠ 0) :
    ¬ (p : ℤ) ∣ (a / (p : ℤ) ^ padicValInt p a) ∧
      a / (p : ℤ) ^ padicValInt p a * (p : ℤ) ^ padicValInt p a = a := by
  haveI := Fact.mk hp
  have hnd := not_p_pow_succ_dvd hp ha
  obtain ⟨w, hw⟩ := p_pow_padicValInt_dvd (p := p) a
  generalize padicValInt p a = v at hnd hw ⊢
  subst hw
  have hpos : (p : ℤ) ^ v ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  rw [Int.mul_ediv_cancel_left _ hpos]
  refine ⟨?_, by ring⟩
  rintro ⟨z, rfl⟩
  exact hnd ⟨z, by rw [pow_succ]; ring⟩

/-- Diagonalization of an integer square matrix by integer matrices of determinant prime to `p`
(first step of the proof of (Q1) of `CSI14_the_ceiling_at_p.md`). -/
theorem exists_diagonalP (hp : p.Prime) : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧
      ∃ d : Fin n → ℤ, P * A * Q = diagonal d := by
  haveI := Fact.mk hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h1 : ¬ (p : ℤ) ∣ 1 := fun h => hpZ.not_unit (isUnit_of_dvd_one h)
  intro n
  induction n with
  | zero =>
    intro A
    exact ⟨1, 1, by simpa using h1, by simpa using h1, fun i => i.elim0,
      by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A
    by_cases hA : A = 0
    · exact ⟨1, 1, by simpa using h1, by simpa using h1, 0, by simp [hA]⟩
    -- a pivot of least `p`-valuation
    have hS : ((univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
        (fun ij => A ij.1 ij.2 ≠ 0)).Nonempty := by
      by_contra h
      apply hA
      ext i j
      by_contra hij
      exact h ⟨(i, j), by simpa using hij⟩
    obtain ⟨⟨a, b⟩, hab, hmin⟩ := exists_min_image _ (fun ij => padicValInt p (A ij.1 ij.2)) hS
    simp only [mem_filter, mem_univ, true_and] at hab hmin
    set v := padicValInt p (A a b)
    have hdvd : ∀ i j, (p : ℤ) ^ v ∣ A i j := by
      intro i j
      by_cases h : A i j = 0
      · rw [h]; exact dvd_zero _
      · exact (pow_dvd_pow (p : ℤ) (hmin (i, j) h)).trans (p_pow_padicValInt_dvd _)
    obtain ⟨hwnd, hw⟩ := not_dvd_div_p_pow hp hab
    set w := A a b / (p : ℤ) ^ v
    -- move the pivot to `(0, 0)`
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 a
    set τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 b
    set A1 := A.submatrix σ τ with hA1
    have hA1_00 : A1 0 0 = (p : ℤ) ^ v * w := by
      simp only [hA1, submatrix_apply, σ, τ, Equiv.swap_apply_left]; rw [← hw]; ring
    have hdvd1 : ∀ i j, (p : ℤ) ^ v ∣ A1 i j := fun i j => hdvd _ _
    set c : Fin (n + 1) → ℤ := fun i => A1 i 0 / (p : ℤ) ^ v
    set c' : Fin (n + 1) → ℤ := fun j => A1 0 j / (p : ℤ) ^ v
    have hc : ∀ i, A1 i 0 = (p : ℤ) ^ v * c i :=
      fun i => (Int.mul_ediv_cancel' (hdvd1 i 0)).symm
    have hc' : ∀ j, A1 0 j = (p : ℤ) ^ v * c' j :=
      fun j => (Int.mul_ediv_cancel' (hdvd1 0 j)).symm
    -- elimination matrices
    set L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
      if i = 0 then (if j = 0 then 1 else 0) else if j = 0 then -c i else if i = j then w else 0
    set R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
      if j = 0 then (if i = 0 then 1 else 0) else if i = 0 then -c' j else if i = j then w else 0
    have hLdet : ¬ (p : ℤ) ∣ L.det := by
      rw [det_of_lowerTriangular]
      · intro h
        obtain ⟨i, _, hi⟩ := (Prime.dvd_finset_prod_iff hpZ _).1 h
        by_cases hi0 : i = 0
        · simp [L, hi0] at hi; exact h1 (by simpa using hi)
        · simp [L, hi0] at hi; exact hwnd hi
      · intro i j hij
        have hij' : i < j := hij
        have hj : j ≠ 0 := by rintro rfl; exact absurd hij' (Fin.not_lt_zero _)
        simp [L, hj, hij'.ne]
    have hRdet : ¬ (p : ℤ) ∣ R.det := by
      rw [det_of_upperTriangular]
      · intro h
        obtain ⟨i, _, hi⟩ := (Prime.dvd_finset_prod_iff hpZ _).1 h
        by_cases hi0 : i = 0
        · simp [R, hi0] at hi; exact h1 (by simpa using hi)
        · simp [R, hi0] at hi; exact hwnd hi
      · intro i j hij
        have hij' : j < i := hij
        have hi : i ≠ 0 := by rintro rfl; exact absurd hij' (Fin.not_lt_zero _)
        simp [R, hi, hij'.ne']
    -- the eliminated matrix
    set B := L * A1 * R with hB
    have hLA : ∀ i j, (L * A1) i j = if i = 0 then A1 0 j else -c i * A1 0 j + w * A1 i j := by
      intro i j
      rw [mul_apply, Fin.sum_univ_succ]
      by_cases hi : i = 0
      · subst hi; simp [L]
      · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
        rw [sum_eq_single i']
        · simp [L, hi]
        · intro k _ hk; simp [L, hi, (Fin.succ_injective _).ne (Ne.symm hk)]
        · simp
    have hLA0 : ∀ i : Fin n, (L * A1) i.succ 0 = 0 := by
      intro i
      rw [hLA, if_neg (Fin.succ_ne_zero _), hc i.succ, hA1_00]
      ring
    have hBe : ∀ i j, B i j =
        if j = 0 then (L * A1) i 0 else (L * A1) i 0 * -c' j + (L * A1) i j * w := by
      intro i j
      rw [hB, mul_apply, Fin.sum_univ_succ]
      by_cases hj : j = 0
      · subst hj; simp [R]
      · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
        rw [sum_eq_single j']
        · simp [R, hj]
        · intro k _ hk; simp [R, hj, (Fin.succ_injective _).ne hk]
        · simp
    have hB1 : ∀ j : Fin n, B 0 j.succ = 0 := by
      intro j
      rw [hBe, if_neg (Fin.succ_ne_zero _), hLA, hLA, if_pos rfl, if_pos rfl, hc' j.succ, hA1_00]
      ring
    have hB2 : ∀ i : Fin n, B i.succ 0 = 0 := by
      intro i; rw [hBe, if_pos rfl, hLA0]
    obtain ⟨P', Q', hP', hQ', d', hd'⟩ := ih (B.submatrix Fin.succ Fin.succ)
    refine ⟨blk 1 P' * L * σ.permMatrix ℤ, Equiv.Perm.permMatrix ℤ τ⁻¹ * R * blk 1 Q',
      ?_, ?_, Fin.cons (B 0 0) d', ?_⟩
    · rw [det_mul, det_mul, det_blk, one_mul]
      exact not_dvd_mul_of hp (not_dvd_mul_of hp hP' hLdet) (not_dvd_det_perm hp σ)
    · rw [det_mul, det_mul, det_blk, one_mul]
      exact not_dvd_mul_of hp (not_dvd_mul_of hp (not_dvd_det_perm hp _) hRdet) hQ'
    · have hBblk := eq_blk B hB1 hB2
      calc blk 1 P' * L * σ.permMatrix ℤ * A * (Equiv.Perm.permMatrix ℤ τ⁻¹ * R * blk 1 Q')
          = blk 1 P' * (L * (σ.permMatrix ℤ * A * Equiv.Perm.permMatrix ℤ τ⁻¹) * R) *
              blk 1 Q' := by
            simp only [Matrix.mul_assoc]
        _ = blk 1 P' * B * blk 1 Q' := by rw [← submatrix_perm_perm]
        _ = diagonal (Fin.cons (B 0 0) d') := by
            conv_lhs => rw [hBblk]
            rw [blk_mul, blk_mul, hd', diagonal_cons, one_mul, mul_one]

/-- The sort key of a diagonal entry: `⊤` for `0`, its `p`-valuation otherwise. (Auxiliary for
(Q1) of `CSI14_the_ceiling_at_p.md`.) -/
noncomputable def sortKeyP (p : ℕ) (z : ℤ) : WithTop ℕ :=
  if z = 0 then ⊤ else (padicValInt p z : ℕ)

/-- **(Q1)** (existence of the Smith form at `p`) of `CSI14_the_ceiling_at_p.md`: for a prime
`p`, every `n` and every `A : Matrix (Fin n) (Fin n) ℤ` there are `P, Q` with `p ∤ det P`,
`p ∤ det Q`, `ρ ≤ n`, exponents `e : ℕ → ℕ` non-decreasing on `[0, ρ)` and `u : ℕ → ℤ` with
`p ∤ u j`, such that `P A Q` is diagonal with entries `u j · p^{e j}` for `j < ρ` and `0` for
`ρ ≤ j < n`.  (For `p = 2` this is C15's `DanceSmith.Q1`.) -/
theorem Q1_smith (hp : p.Prime) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧
      ∃ ρ ≤ n, ∃ e : ℕ → ℕ, (∀ i j, i ≤ j → j < ρ → e i ≤ e j) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
          P * A * Q = diagonal (fun j : Fin n =>
            if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) := by
  have h1 : ¬ (p : ℤ) ∣ 1 := fun h =>
    (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_dvd_one h)
  obtain ⟨P0, Q0, hP0, hQ0, d, hd⟩ := exists_diagonalP hp n A
  set τ := Tuple.sort (fun j => sortKeyP p (d j))
  have hmono : Monotone (fun j => sortKeyP p (d (τ j))) :=
    Tuple.monotone_sort (fun j => sortKeyP p (d j))
  set d' : Fin n → ℤ := fun j => d (τ j)
  set ρ := (univ.filter (fun j : Fin n => d' j ≠ 0)).card
  have hkey : ∀ j, sortKeyP p (d' j) = ⊤ ↔ d' j = 0 := by
    intro j; unfold sortKeyP; split_ifs with h <;> simp [h]
  have hρ : ∀ j : Fin n, d' j ≠ 0 ↔ (j : ℕ) < ρ := by
    intro j
    constructor
    · intro hj
      have hsub : univ.filter (fun i : Fin n => i ≤ j) ⊆
          univ.filter (fun j : Fin n => d' j ≠ 0) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        intro h0
        have h1 := hmono hi
        have h2 : sortKeyP p (d' i) = ⊤ := (hkey i).2 h0
        exact hj ((hkey j).1 (top_le_iff.1 (h2 ▸ h1)))
      have := card_le_card hsub
      have hc : (univ.filter (fun i : Fin n => i ≤ j)).card = j + 1 := by
        rw [← Fin.card_Iic]; congr 1; ext; simp
      omega
    · intro hj h0
      have hsub : univ.filter (fun j : Fin n => d' j ≠ 0) ⊆
          univ.filter (fun i : Fin n => i < j) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        by_contra hlt
        apply hi
        have h1 := hmono (not_lt.1 hlt)
        have h2 : sortKeyP p (d' j) = ⊤ := (hkey j).2 h0
        exact (hkey i).1 (top_le_iff.1 (h2 ▸ h1))
      have := card_le_card hsub
      have hc : (univ.filter (fun i : Fin n => i < j)).card = j := by
        rw [← Fin.card_Iio]; congr 1; ext; simp
      omega
  set e : ℕ → ℕ := fun j => if h : j < n then padicValInt p (d' ⟨j, h⟩) else 0
  set u : ℕ → ℤ := fun j => if h : j < n then
    (if d' ⟨j, h⟩ = 0 then 1 else d' ⟨j, h⟩ / (p : ℤ) ^ e j) else 1
  have hρn : ρ ≤ n := by
    calc ρ ≤ (univ : Finset (Fin n)).card := card_le_card (filter_subset _ _)
      _ = n := by simp
  refine ⟨τ.permMatrix ℤ * P0, Q0 * Equiv.Perm.permMatrix ℤ τ⁻¹, ?_, ?_, ρ, hρn, e, ?_, u, ?_,
    ?_⟩
  · rw [det_mul]; exact not_dvd_mul_of hp (not_dvd_det_perm hp τ) hP0
  · rw [det_mul]; exact not_dvd_mul_of hp hQ0 (not_dvd_det_perm hp _)
  · intro i j hij hj
    have hjn : j < n := by omega
    have hi0 := (hρ ⟨i, by omega⟩).2 (by simp; omega)
    have hj0 := (hρ ⟨j, hjn⟩).2 hj
    have h := hmono (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hjn⟩ from hij)
    change sortKeyP p (d' _) ≤ sortKeyP p (d' _) at h
    simp only [sortKeyP, if_neg hi0, if_neg hj0] at h
    simp only [e, dif_pos hjn, dif_pos (show i < n by omega)]
    exact_mod_cast h
  · intro j
    simp only [u]
    split_ifs with h1' h2
    · exact h1
    · simp only [e, dif_pos h1']; exact (not_dvd_div_p_pow hp h2).1
    · exact h1
  · calc τ.permMatrix ℤ * P0 * A * (Q0 * Equiv.Perm.permMatrix ℤ τ⁻¹)
        = τ.permMatrix ℤ * (P0 * A * Q0) * Equiv.Perm.permMatrix ℤ τ⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (diagonal d).submatrix τ τ := by rw [hd, submatrix_perm_perm]
      _ = _ := by
          rw [submatrix_diagonal_equiv]
          congr 1
          funext j
          change d' j = _
          by_cases hj : d' j = 0
          · rw [if_neg (by rw [← hρ j]; exact not_not.2 hj), hj]
          · rw [if_pos ((hρ j).1 hj)]
            simp only [u, e, dif_pos j.2, if_neg hj]
            exact (not_dvd_div_p_pow hp hj).2.symm

/-! ### (Q2) -/

section Q2

variable {n : ℕ} {ρ : ℕ} {e : ℕ → ℕ} {u : ℕ → ℤ}

/-- The diagonal entries `u j p^{e j}` (`j < ρ`), `0` (`j ≥ ρ`) of (Q1) of
`CSI14_the_ceiling_at_p.md`. -/
def smithDiagP (p : ℕ) (ρ : ℕ) (e : ℕ → ℕ) (u : ℕ → ℤ) : Fin n → ℤ :=
  fun j => if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0

lemma prod_smithDiagP_of_lt (hp : p.Prime) (hu : ∀ j, ¬ (p : ℤ) ∣ u j) {B : Finset (Fin n)}
    (hB : ∀ i ∈ B, (i : ℕ) < ρ) :
    ∏ i ∈ B, smithDiagP p ρ e u i ≠ 0 ∧
      padicValInt p (∏ i ∈ B, smithDiagP p ρ e u i) = ∑ i ∈ B, e i := by
  have h := padicValInt_prod_diagP hp (fun i : Fin n => e i) (u := fun i : Fin n => u i)
    (fun i => hu i) B
  have heq : ∏ i ∈ B, smithDiagP p ρ e u i = ∏ i ∈ B, u i * (p : ℤ) ^ e i :=
    prod_congr rfl fun i hi => by simp [smithDiagP, hB i hi]
  rw [heq]; exact h

lemma prod_smithDiagP_eq_zero {B : Finset (Fin n)} (hB : ∃ i ∈ B, ρ ≤ (i : ℕ)) :
    ∏ i ∈ B, smithDiagP p ρ e u i = 0 := by
  obtain ⟨i, hi, hρi⟩ := hB
  exact prod_eq_zero hi (by simp [smithDiagP, not_lt.2 hρi])

/-- Every `r × r` minor of the diagonal matrix of (Q1) vanishes for `r > ρ`. -/
lemma minor_smithDiagP_zero {r : ℕ} (hr : ρ < r) (B C : Finset (Fin n)) (hB : B.card = r)
    (hC : C.card = r) : Divisors.minor (diagonal (smithDiagP (n := n) p ρ e u)) r B C = 0 := by
  by_cases hBC : B = C
  · subst hBC
    rw [Divisors.minor_diagonal_self _ hB]
    apply prod_smithDiagP_eq_zero
    by_contra h
    push_neg at h
    have hsub : B ⊆ univ.filter (fun i : Fin n => (i : ℕ) < ρ) := fun i hi => by simp [h i hi]
    have := card_le_card hsub
    rw [Divisors.card_filter_lt (show ρ ≤ n by
      have := card_le_univ B; simp at this; omega)] at this
    omega
  · exact Divisors.minor_diagonal_of_ne _ hB hC hBC

/-- The divisors of the diagonal matrix of (Q1): `ddP_r = Σ_{j<r} e j` for `r ≤ ρ`. -/
lemma ddP_smithDiagP (hp : p.Prime) (hρ : ρ ≤ n) (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ u j) {r : ℕ} (hr : r ≤ ρ) :
    ddP p (diagonal (smithDiagP (n := n) p ρ e u)) r = ∑ j ∈ range r, e j ∧
      (minorValsP p (diagonal (smithDiagP (n := n) p ρ e u)) r).Nonempty := by
  set A₀ := univ.filter (fun i : Fin n => (i : ℕ) < r)
  have hA₀ : A₀.card = r := Divisors.card_filter_lt (by omega)
  have hm₀ := prod_smithDiagP_of_lt (ρ := ρ) (e := e) hp hu (B := A₀) (fun i hi => by
    simp only [A₀, mem_filter] at hi; omega)
  rw [← Divisors.minor_diagonal_self _ hA₀] at hm₀
  have hsum : ∑ i ∈ A₀, e i = ∑ j ∈ range r, e j := sum_filter_lt_fin (by omega) e
  have hne : (minorValsP p (diagonal (smithDiagP (n := n) p ρ e u)) r).Nonempty :=
    ⟨_, A₀, A₀, hA₀, hA₀, hm₀.1, rfl⟩
  refine ⟨le_antisymm ?_ ?_, hne⟩
  · exact (ddP_le _ hA₀ hA₀ hm₀.1).trans (hm₀.2.trans hsum).le
  · refine le_csInf hne ?_
    rintro v ⟨B, C, hB, hC, h0, rfl⟩
    have hBC : B = C := by
      by_contra hne; exact h0 (Divisors.minor_diagonal_of_ne _ hB hC hne)
    subst hBC
    rw [Divisors.minor_diagonal_self _ hB] at h0 ⊢
    have hlt : ∀ i ∈ B, (i : ℕ) < ρ := by
      intro i hi
      by_contra h
      exact h0 (prod_smithDiagP_eq_zero ⟨i, hi, not_lt.1 h⟩)
    rw [(prod_smithDiagP_of_lt (e := e) hp hu hlt).2]
    set eM : Fin n → ℕ := fun i => e (min (i : ℕ) (ρ - 1))
    have hmono : Monotone eM := by
      intro i j hij
      simp only [eM]
      rcases Nat.eq_zero_or_pos ρ with h0 | h0
      · simp [h0]
      · exact he _ _ (by have : (i : ℕ) ≤ j := hij; omega) (by omega)
    have h1 := Divisors.firstSum_le_sum hmono (by omega : r ≤ n) hB
    have h2 : ∑ i ∈ B, eM i = ∑ i ∈ B, e i :=
      sum_congr rfl fun i hi => by simp only [eM]; congr 1; have := hlt i hi; omega
    have h3 : Divisors.firstSum eM r = ∑ j ∈ range r, e j := by
      rw [Divisors.firstSum, ← hsum]
      exact sum_congr rfl fun i hi => by
        simp only [A₀, mem_filter] at hi; simp only [eM]; congr 1; omega
    omega

/-- **(Q2)** of `CSI14_the_ceiling_at_p.md`: in the situation of (Q1)
(`P A Q = diag(u_0 p^{e_0}, …, u_{ρ−1} p^{e_{ρ−1}}, 0, …, 0)` with `p ∤ det P`, `p ∤ det Q`,
`ρ ≤ n`, `e` non-decreasing on `[0, ρ)` and `p ∤ u j`): `ddP p A r = Σ_{j<r} e j` for every
`r ≤ ρ`, every `r × r` minor of `A` is `0` for `r > ρ`, and `det A ≠ 0 ↔ ρ = n`. -/
theorem Q2_smith (hp : p.Prime) (A P Q : Matrix (Fin n) (Fin n) ℤ) (hP : ¬ (p : ℤ) ∣ P.det)
    (hQ : ¬ (p : ℤ) ∣ Q.det) (hρ : ρ ≤ n) (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ u j)
    (hD : P * A * Q = diagonal (fun j : Fin n =>
      if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0)) :
    (∀ r ≤ ρ, ddP p A r = ∑ j ∈ range r, e j) ∧
      (∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
        Divisors.minor A r B C = 0) ∧
      (A.det ≠ 0 ↔ ρ = n) := by
  have hD' : P * A * Q = diagonal (smithDiagP p ρ e u) := hD
  have hzero : ∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
      Divisors.minor A r B C = 0 := by
    intro r hr B C hB hC
    have hc : ¬ (p : ℤ) ∣ P.det * Q.det := not_dvd_mul_of hp hP hQ
    have hc0 : (P.det * Q.det) ^ r ≠ 0 :=
      pow_ne_zero _ (by rintro h; rw [h] at hc; exact hc (dvd_zero _))
    have h1 : Divisors.minor ((P.det * Q.det) • A) r B C = 0 := by
      rw [← Divisors.adjugate_mul_mul_adjugate, hD']
      exact zero_dvd_iff.1 (Divisors.dvd_minor_mul_mul _ _ _ (fun B' C' hB' hC' => by
        rw [minor_smithDiagP_zero hr B' C' hB' hC']) B C)
    rw [Divisors.minor_smul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  refine ⟨fun r hr => ?_, hzero, ⟨fun hdet => ?_, fun hρn => ?_⟩⟩
  · rw [← D1_invariance hp A P Q hP hQ r, hD']
    exact (ddP_smithDiagP hp hρ he hu hr).1
  · by_contra hne
    apply hdet
    rw [← Divisors.minor_univ]
    exact hzero n (by omega) _ _ (by simp) (by simp)
  · intro h0
    have := congrArg det hD'
    rw [det_mul, det_mul, h0, mul_zero, zero_mul, det_diagonal] at this
    exact (prod_smithDiagP_of_lt (e := e) hp hu (B := univ) (fun i _ => hρn ▸ i.2)).1 this.symm

end Q2

end ColouredSand.OddTwist
