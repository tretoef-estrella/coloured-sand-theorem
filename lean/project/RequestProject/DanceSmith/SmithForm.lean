module

public import RequestProject.Divisors.All

/-!
# Part Q of `C15_smith_form_of_the_dance_matrix.md`: the Smith form at 2 of an integer matrix

## Encoding

* Square integer matrices are `A : Matrix (Fin n) (Fin n) ℤ`; "`det P` odd" is `Odd P.det`.
* The Smith form at 2 is `P * A * Q = diagonal D` with
  `D j = if (j : ℕ) < ρ then u j * 2 ^ e j else 0`, where `ρ ≤ n`, `e : ℕ → ℕ` is non-decreasing
  on `[0, ρ)` (`∀ i j, i ≤ j → j < ρ → e i ≤ e j`) and `u : ℕ → ℤ` takes odd values.
* `Σ_{j<r} e j` is `∑ j ∈ Finset.range r, e j`.

The existence (Q1) is proved directly (Mathlib's Smith normal form is **not** used): an
elimination with a pivot of least 2-valuation, in which every row/column operation multiplies the
determinant by an odd integer, diagonalizes `A` (`exists_diagonal`); then a permutation sorts the
diagonal by 2-valuation, zeros last (`Tuple.sort`).
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix

/-! ### Block matrices with a `1 × 1` corner -/

/-- The matrix `[[a, 0], [0, X]]` of size `n + 1`. (Auxiliary for (Q1) of
`C15_smith_form_of_the_dance_matrix.md`.) -/
def blk {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => X i' j') j) i

@[simp] lemma blk_zero_zero {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) : blk a X 0 0 = a := rfl
@[simp] lemma blk_zero_succ {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    blk a X 0 j.succ = 0 := rfl
@[simp] lemma blk_succ_zero {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    blk a X i.succ 0 = 0 := rfl
@[simp] lemma blk_succ_succ {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    blk a X i.succ j.succ = X i j := rfl

lemma blk_mul {n : ℕ} (a b : ℤ) (X Y : Matrix (Fin n) (Fin n) ℤ) :
    blk a X * blk b Y = blk (a * b) (X * Y) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [mul_apply, Fin.sum_univ_succ]

lemma det_blk {n : ℕ} (a : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) : (blk a X).det = a * X.det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, blk_zero_zero, blk_zero_succ, mul_zero, zero_mul,
    sum_const_zero, add_zero, Fin.succAbove_zero]
  congr 1

lemma diagonal_cons {n : ℕ} (a : ℤ) (d : Fin n → ℤ) :
    diagonal (Fin.cons a d : Fin (n + 1) → ℤ) = blk a (diagonal d) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

lemma eq_blk {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (h1 : ∀ j : Fin n, B 0 j.succ = 0)
    (h2 : ∀ i : Fin n, B i.succ 0 = 0) : B = blk (B 0 0) (B.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [h1, h2]

/-- `A.submatrix σ τ = Pσ A Pτ⁻¹` with permutation matrices. (Auxiliary for (Q1) of
`C15_smith_form_of_the_dance_matrix.md`.) -/
lemma submatrix_perm_perm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) ℤ) :
    A.submatrix σ τ = σ.permMatrix ℤ * A * Equiv.Perm.permMatrix ℤ τ⁻¹ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

lemma odd_det_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Odd (σ.permMatrix ℤ).det := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-! ### Valuations -/

lemma two_pow_padicValInt_dvd (a : ℤ) : (2 : ℤ) ^ padicValInt 2 a ∣ a := by
  exact_mod_cast padicValInt_dvd (p := 2) a

lemma not_two_pow_succ_dvd {a : ℤ} (ha : a ≠ 0) : ¬ (2 : ℤ) ^ (padicValInt 2 a + 1) ∣ a := by
  intro h
  have := (padicValInt_dvd_iff (p := 2) (padicValInt 2 a + 1) a).1 (by exact_mod_cast h)
  omega

/-- For `a ≠ 0`, `a = u · 2^{v_2(a)}` with `u` odd. -/
lemma odd_div_two_pow {a : ℤ} (ha : a ≠ 0) :
    Odd (a / 2 ^ padicValInt 2 a) ∧ a / 2 ^ padicValInt 2 a * 2 ^ padicValInt 2 a = a := by
  have hnd := not_two_pow_succ_dvd ha
  obtain ⟨w, hw⟩ := two_pow_padicValInt_dvd a
  generalize padicValInt 2 a = v at hnd hw ⊢
  subst hw
  have hpos : (2 : ℤ) ^ v ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [Int.mul_ediv_cancel_left _ hpos]
  refine ⟨?_, by ring⟩
  rw [← Int.not_even_iff_odd]
  rintro ⟨z, rfl⟩
  exact hnd ⟨z, by rw [pow_succ]; ring⟩

/-! ### Diagonalization -/

/-- Diagonalization of an integer square matrix by matrices of odd determinant (first step of the
proof of (Q1) of `C15_smith_form_of_the_dance_matrix.md`). -/
theorem exists_diagonal : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ d : Fin n → ℤ,
      P * A * Q = diagonal d := by
  intro n
  induction n with
  | zero =>
    intro A
    exact ⟨1, 1, by simp, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A
    by_cases hA : A = 0
    · exact ⟨1, 1, by simp, by simp, 0, by simp [hA]⟩
    -- a pivot of least 2-valuation
    have hS : ((univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
        (fun ij => A ij.1 ij.2 ≠ 0)).Nonempty := by
      by_contra h
      apply hA
      ext i j
      by_contra hij
      exact h ⟨(i, j), by simpa using hij⟩
    obtain ⟨⟨a, b⟩, hab, hmin⟩ := exists_min_image _ (fun ij => padicValInt 2 (A ij.1 ij.2)) hS
    simp only [mem_filter, mem_univ, true_and] at hab hmin
    set v := padicValInt 2 (A a b)
    have hdvd : ∀ i j, (2 : ℤ) ^ v ∣ A i j := by
      intro i j
      by_cases h : A i j = 0
      · rw [h]; exact dvd_zero _
      · exact (pow_dvd_pow 2 (hmin (i, j) h)).trans (two_pow_padicValInt_dvd _)
    obtain ⟨hwodd, hw⟩ := odd_div_two_pow hab
    set w := A a b / 2 ^ v
    -- move the pivot to `(0, 0)`
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 a
    set τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 b
    set A1 := A.submatrix σ τ with hA1
    have hA1_00 : A1 0 0 = 2 ^ v * w := by
      simp only [hA1, submatrix_apply, σ, τ, Equiv.swap_apply_left]; rw [← hw]; ring
    have hdvd1 : ∀ i j, (2 : ℤ) ^ v ∣ A1 i j := fun i j => hdvd _ _
    set c : Fin (n + 1) → ℤ := fun i => A1 i 0 / 2 ^ v
    set c' : Fin (n + 1) → ℤ := fun j => A1 0 j / 2 ^ v
    have hc : ∀ i, A1 i 0 = 2 ^ v * c i := fun i => (Int.mul_ediv_cancel' (hdvd1 i 0)).symm
    have hc' : ∀ j, A1 0 j = 2 ^ v * c' j := fun j => (Int.mul_ediv_cancel' (hdvd1 0 j)).symm
    -- elimination matrices
    set L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
      if i = 0 then (if j = 0 then 1 else 0) else if j = 0 then -c i else if i = j then w else 0
    set R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
      if j = 0 then (if i = 0 then 1 else 0) else if i = 0 then -c' j else if i = j then w else 0
    have hLdet : Odd L.det := by
      rw [det_of_lowerTriangular]
      · refine prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun i _ => ?_
        by_cases hi : i = 0 <;> simp [L, hi, hwodd]
      · intro i j hij
        have hij' : i < j := hij
        have hj : j ≠ 0 := by rintro rfl; exact absurd hij' (Fin.not_lt_zero _)
        simp [L, hj, hij'.ne]
    have hRdet : Odd R.det := by
      rw [det_of_upperTriangular]
      · refine prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun i _ => ?_
        by_cases hi : i = 0 <;> simp [R, hi, hwodd]
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
    have hBe : ∀ i j, B i j = if j = 0 then (L * A1) i 0 else (L * A1) i 0 * -c' j + (L * A1) i j * w := by
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
      exact (hP'.mul hLdet).mul (odd_det_perm σ)
    · rw [det_mul, det_mul, det_blk, one_mul]
      exact ((odd_det_perm _).mul hRdet).mul hQ'
    · have hBblk := eq_blk B hB1 hB2
      calc blk 1 P' * L * σ.permMatrix ℤ * A * (Equiv.Perm.permMatrix ℤ τ⁻¹ * R * blk 1 Q')
          = blk 1 P' * (L * (σ.permMatrix ℤ * A * Equiv.Perm.permMatrix ℤ τ⁻¹) * R) * blk 1 Q' := by
            simp only [Matrix.mul_assoc]
        _ = blk 1 P' * B * blk 1 Q' := by rw [← submatrix_perm_perm]
        _ = diagonal (Fin.cons (B 0 0) d') := by
            conv_lhs => rw [hBblk]
            rw [blk_mul, blk_mul, hd', diagonal_cons, one_mul, mul_one]

/-! ### Sorting the diagonal -/

/-- The sort key of a diagonal entry: `⊤` for `0`, its 2-valuation otherwise. -/
noncomputable def sortKey (z : ℤ) : WithTop ℕ := if z = 0 then ⊤ else (padicValInt 2 z : ℕ)

/-- **(Q1)** (existence of the Smith form at 2) of `C15_smith_form_of_the_dance_matrix.md`: for every
`n` and every `A : Matrix (Fin n) (Fin n) ℤ` there are `P, Q` with `det P`, `det Q` odd, `ρ ≤ n`,
exponents `e : ℕ → ℕ` non-decreasing on `[0, ρ)` and odd integers `u j` such that `P A Q` is
diagonal with entries `u j · 2^{e j}` for `j < ρ` and `0` for `ρ ≤ j < n`.  (Proved by elimination
with a pivot of least 2-valuation; Mathlib's Smith normal form is not used.) -/
theorem Q1 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧
      ∃ ρ ≤ n, ∃ e : ℕ → ℕ, (∀ i j, i ≤ j → j < ρ → e i ≤ e j) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
          P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < ρ then u j * 2 ^ e j else 0) := by
  obtain ⟨P0, Q0, hP0, hQ0, d, hd⟩ := exists_diagonal n A
  set τ := Tuple.sort (fun j => sortKey (d j))
  have hmono : Monotone (fun j => sortKey (d (τ j))) := Tuple.monotone_sort (fun j => sortKey (d j))
  set d' : Fin n → ℤ := fun j => d (τ j)
  set ρ := (univ.filter (fun j : Fin n => d' j ≠ 0)).card
  have hkey : ∀ j, sortKey (d' j) = ⊤ ↔ d' j = 0 := by
    intro j; unfold sortKey; split_ifs with h <;> simp [h]
  have hρ : ∀ j : Fin n, d' j ≠ 0 ↔ (j : ℕ) < ρ := by
    intro j
    constructor
    · intro hj
      have hsub : univ.filter (fun i : Fin n => i ≤ j) ⊆ univ.filter (fun j : Fin n => d' j ≠ 0) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        intro h0
        have h1 := hmono hi
        have h2 : sortKey (d' i) = ⊤ := (hkey i).2 h0
        exact hj ((hkey j).1 (top_le_iff.1 (h2 ▸ h1)))
      have := card_le_card hsub
      have hc : (univ.filter (fun i : Fin n => i ≤ j)).card = j + 1 := by
        rw [← Fin.card_Iic]; congr 1; ext; simp
      omega
    · intro hj h0
      have hsub : univ.filter (fun j : Fin n => d' j ≠ 0) ⊆ univ.filter (fun i : Fin n => i < j) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        by_contra hlt
        apply hi
        have h1 := hmono (not_lt.1 hlt)
        have h2 : sortKey (d' j) = ⊤ := (hkey j).2 h0
        exact (hkey i).1 (top_le_iff.1 (h2 ▸ h1))
      have := card_le_card hsub
      have hc : (univ.filter (fun i : Fin n => i < j)).card = j := by
        rw [← Fin.card_Iio]; congr 1; ext; simp
      omega
  set e : ℕ → ℕ := fun j => if h : j < n then padicValInt 2 (d' ⟨j, h⟩) else 0
  set u : ℕ → ℤ := fun j => if h : j < n then (if d' ⟨j, h⟩ = 0 then 1 else d' ⟨j, h⟩ / 2 ^ e j)
    else 1
  have hρn : ρ ≤ n := by
    calc ρ ≤ (univ : Finset (Fin n)).card := card_le_card (filter_subset _ _)
      _ = n := by simp
  refine ⟨τ.permMatrix ℤ * P0, Q0 * Equiv.Perm.permMatrix ℤ τ⁻¹, ?_, ?_, ρ, hρn, e, ?_, u, ?_, ?_⟩
  · rw [det_mul]; exact (odd_det_perm τ).mul hP0
  · rw [det_mul]; exact hQ0.mul (odd_det_perm _)
  · intro i j hij hj
    have hjn : j < n := by omega
    have hi0 := (hρ ⟨i, by omega⟩).2 (by simp; omega)
    have hj0 := (hρ ⟨j, hjn⟩).2 hj
    have h := hmono (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hjn⟩ from hij)
    simp only [sortKey] at h
    change sortKey (d' _) ≤ sortKey (d' _) at h
    simp only [sortKey, if_neg hi0, if_neg hj0] at h
    simp only [e, dif_pos hjn, dif_pos (show i < n by omega)]
    exact_mod_cast h
  · intro j
    simp only [u]
    split_ifs with h1 h2
    · exact odd_one
    · simp only [e, dif_pos h1]; exact (odd_div_two_pow h2).1
    · exact odd_one
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
            exact (odd_div_two_pow hj).2.symm

/-! ### (Q2): the divisors of a matrix with a Smith form at 2 -/

/-- `Σ_{i : Fin n, i < r} f i = Σ_{j<r} f j` for `r ≤ n`. -/
lemma sum_filter_lt_fin {n r : ℕ} (hr : r ≤ n) (f : ℕ → ℕ) :
    ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), f i = ∑ j ∈ range r, f j := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun j => if j < r then f j else 0) n, ← sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

section Q2

variable {n : ℕ} {ρ : ℕ} (e : ℕ → ℕ) (u : ℕ → ℤ)

/-- The diagonal entries `u j 2^{e j}` (`j < ρ`), `0` (`j ≥ ρ`) of (Q1). -/
def smithDiag (ρ : ℕ) (e : ℕ → ℕ) (u : ℕ → ℤ) : Fin n → ℤ :=
  fun j => if (j : ℕ) < ρ then u j * 2 ^ e j else 0

variable {e u}

lemma minor_smithDiag_self {r : ℕ} {B : Finset (Fin n)} (hB : B.card = r) :
    Divisors.minor (diagonal (smithDiag (n := n) ρ e u)) r B B = ∏ i ∈ B, smithDiag ρ e u i :=
  Divisors.minor_diagonal_self _ hB

lemma prod_smithDiag_of_lt (hu : ∀ j, Odd (u j)) {B : Finset (Fin n)}
    (hB : ∀ i ∈ B, (i : ℕ) < ρ) :
    ∏ i ∈ B, smithDiag ρ e u i ≠ 0 ∧
      padicValInt 2 (∏ i ∈ B, smithDiag ρ e u i) = ∑ i ∈ B, e i := by
  have h := Divisors.padicValInt_prod_diag (fun i : Fin n => e i) (u := fun i : Fin n => u i)
    (fun i => hu i) B
  have heq : ∏ i ∈ B, smithDiag ρ e u i = ∏ i ∈ B, u i * 2 ^ e i :=
    prod_congr rfl fun i hi => by simp [smithDiag, hB i hi]
  rw [heq]; exact h

lemma prod_smithDiag_eq_zero {B : Finset (Fin n)} (hB : ∃ i ∈ B, ρ ≤ (i : ℕ)) :
    ∏ i ∈ B, smithDiag ρ e u i = 0 := by
  obtain ⟨i, hi, hρi⟩ := hB
  exact prod_eq_zero hi (by simp [smithDiag, not_lt.2 hρi])

/-- Every `r × r` minor of the diagonal matrix of (Q1) vanishes for `r > ρ`. -/
lemma minor_smithDiag_zero {r : ℕ} (hr : ρ < r) (B C : Finset (Fin n)) (hB : B.card = r)
    (hC : C.card = r) : Divisors.minor (diagonal (smithDiag (n := n) ρ e u)) r B C = 0 := by
  by_cases hBC : B = C
  · subst hBC
    rw [minor_smithDiag_self hB]
    apply prod_smithDiag_eq_zero
    by_contra h
    push_neg at h
    have hsub : B ⊆ univ.filter (fun i : Fin n => (i : ℕ) < ρ) := fun i hi => by simp [h i hi]
    have := card_le_card hsub
    rw [Divisors.card_filter_lt (show ρ ≤ n by
      have := card_le_univ B; simp at this; omega)] at this
    omega
  · exact Divisors.minor_diagonal_of_ne _ hB hC hBC

/-- The divisors of the diagonal matrix of (Q1): `dd_r = Σ_{j<r} e j` for `r ≤ ρ`. -/
lemma dd_smithDiag (hρ : ρ ≤ n) (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j) (hu : ∀ j, Odd (u j))
    {r : ℕ} (hr : r ≤ ρ) :
    Divisors.dd (diagonal (smithDiag (n := n) ρ e u)) r = ∑ j ∈ range r, e j ∧
      (Divisors.minorVals (diagonal (smithDiag (n := n) ρ e u)) r).Nonempty := by
  set A₀ := univ.filter (fun i : Fin n => (i : ℕ) < r)
  have hA₀ : A₀.card = r := Divisors.card_filter_lt (by omega)
  have hm₀ := prod_smithDiag_of_lt (ρ := ρ) (e := e) hu (B := A₀) (fun i hi => by
    simp only [A₀, mem_filter] at hi; omega)
  rw [← minor_smithDiag_self hA₀] at hm₀
  have hsum : ∑ i ∈ A₀, e i = ∑ j ∈ range r, e j := sum_filter_lt_fin (by omega) e
  have hne : (Divisors.minorVals (diagonal (smithDiag (n := n) ρ e u)) r).Nonempty :=
    ⟨_, A₀, A₀, hA₀, hA₀, hm₀.1, rfl⟩
  refine ⟨le_antisymm ?_ ?_, hne⟩
  · exact (Divisors.dd_le _ hA₀ hA₀ hm₀.1).trans (hm₀.2.trans hsum).le
  · refine le_csInf hne ?_
    rintro v ⟨B, C, hB, hC, h0, rfl⟩
    have hBC : B = C := by
      by_contra hne; exact h0 (Divisors.minor_diagonal_of_ne _ hB hC hne)
    subst hBC
    rw [minor_smithDiag_self hB] at h0 ⊢
    have hlt : ∀ i ∈ B, (i : ℕ) < ρ := by
      intro i hi
      by_contra h
      exact h0 (prod_smithDiag_eq_zero ⟨i, hi, not_lt.1 h⟩)
    rw [(prod_smithDiag_of_lt (e := e) hu hlt).2]
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

/-- **(Q2)** of `C15_smith_form_of_the_dance_matrix.md`: in the situation of (Q1)
(`P A Q = diag(u_0 2^{e_0}, …, u_{ρ−1} 2^{e_{ρ−1}}, 0, …, 0)` with `det P`, `det Q` odd, `ρ ≤ n`,
`e` non-decreasing on `[0, ρ)` and `u` odd), `Divisors.dd A r = Σ_{j<r} e j` for every `r ≤ ρ`, every
`r × r` minor of `A` is `0` for `r > ρ`, and `det A ≠ 0 ⟺ ρ = n`. -/
theorem Q2 (A P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (hρ : ρ ≤ n)
    (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j) (hu : ∀ j, Odd (u j))
    (hD : P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < ρ then u j * 2 ^ e j else 0)) :
    (∀ r ≤ ρ, Divisors.dd A r = ∑ j ∈ range r, e j) ∧
      (∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
        Divisors.minor A r B C = 0) ∧
      (A.det ≠ 0 ↔ ρ = n) := by
  have hD' : P * A * Q = diagonal (smithDiag ρ e u) := hD
  have hzero : ∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
      Divisors.minor A r B C = 0 := by
    intro r hr B C hB hC
    have hc : Odd (P.det * Q.det) := hP.mul hQ
    have hc0 : (P.det * Q.det) ^ r ≠ 0 := pow_ne_zero _ (by rintro h; rw [h] at hc; simp at hc)
    have h1 : Divisors.minor ((P.det * Q.det) • A) r B C = 0 := by
      rw [← Divisors.adjugate_mul_mul_adjugate, hD']
      exact zero_dvd_iff.1 (Divisors.dvd_minor_mul_mul _ _ _ (fun B' C' hB' hC' => by
        rw [minor_smithDiag_zero hr B' C' hB' hC']) B C)
    rw [Divisors.minor_smul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  refine ⟨fun r hr => ?_, hzero, ⟨fun hdet => ?_, fun hρn => ?_⟩⟩
  · rw [← Divisors.lemma_A1 A P Q hP hQ r, hD']
    exact (dd_smithDiag hρ he hu hr).1
  · by_contra hne
    apply hdet
    rw [← Divisors.minor_univ]
    exact hzero n (by omega) _ _ (by simp) (by simp)
  · intro h0
    have := congrArg det hD'
    rw [det_mul, det_mul, h0, mul_zero, zero_mul, det_diagonal] at this
    exact (prod_smithDiag_of_lt (e := e) hu (B := univ) (fun i _ => hρn ▸ i.2)).1 this.symm

/-- In the situation of (Q1), `A` has a non-zero `r × r` minor for every `r ≤ ρ` (proof of
(Q2) of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma Q2_nonempty (A P Q : Matrix (Fin n) (Fin n) ℤ) (hρ : ρ ≤ n)
    (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j) (hu : ∀ j, Odd (u j))
    (hD : P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < ρ then u j * 2 ^ e j else 0))
    {r : ℕ} (hr : r ≤ ρ) : (Divisors.minorVals A r).Nonempty := by
  have hD' : P * A * Q = diagonal (smithDiag ρ e u) := hD
  apply Divisors.minorVals_nonempty_of_mul P A Q
  rw [hD']
  exact (dd_smithDiag hρ he hu hr).2

end Q2

end DanceSmith
