module

public import RequestProject.Divisors.CauchyBinet

/-!
# Part A of `C5_divisors_theorem_65.md`: minors and 2-adic determinantal divisors

## Encoding

* An `n × n` integer matrix is `M : Matrix (Fin n) (Fin n) ℤ`; rows and columns are indexed by
  `Fin n = {0, …, n − 1}` with its usual order.  Minors are defined more generally for
  rectangular matrices over any commutative ring.
* A subset `A ⊆ {0, …, n − 1}` is a `Finset (Fin n)`; for `A.card = r`, its elements in
  increasing order are `A.orderEmbOfFin h : Fin r ↪o Fin n`.
* **Minor.** `minor M r A B` is `det M[A, B]`, i.e. the determinant of the `r × r` matrix
  `M.submatrix (A.orderEmbOfFin _) (B.orderEmbOfFin _)` (rows of `A` and columns of `B`, both in
  increasing order) when `|A| = |B| = r`, and `0` otherwise (the latter case is never used).
* **`dd_r(M)`.** `minorVals M r` is the set
  `{ v_2(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0 } ⊆ ℕ`, with `v_2 = padicValInt 2`, and
  `dd M r = sInf (minorVals M r)` is its minimum.  For `det M ≠ 0` and `r ≤ n` this set is
  non-empty (`minorVals_nonempty`), so `dd M r` is a genuine minimum
  (`dd_mem`, `dd_le`); `sInf ∅ = 0` is only a junk value outside of the setting.
-/

@[expose] public section

namespace Divisors

open Finset Matrix Equiv

variable {R : Type*} [CommRing R]

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: the `r × r` minor `det M[A, B]` of `M`, rows
of `A` and columns of `B` taken in increasing order (defined to be `0` unless
`|A| = |B| = r`). -/
noncomputable def minor {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (r : ℕ) (A : Finset (Fin m))
    (B : Finset (Fin n)) : R :=
  if h : A.card = r ∧ B.card = r then
    det (M.submatrix (A.orderEmbOfFin h.1) (B.orderEmbOfFin h.2))
  else 0

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: the set
`{ v_2(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0 }`. -/
def minorVals {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : Set ℕ :=
  {v | ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧ minor M r A B ≠ 0 ∧
    padicValInt 2 (minor M r A B) = v}

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: the **2-adic determinantal divisor**
`dd_r(M) = min { v_2(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0 }`. -/
noncomputable def dd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : ℕ :=
  sInf (minorVals M r)

theorem minor_of_card {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) {r : ℕ} {A : Finset (Fin m)}
    {B : Finset (Fin n)} (hA : A.card = r) (hB : B.card = r) :
    minor M r A B = det (M.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)) := by
  simp [minor, hA, hB]

theorem minor_of_not_card {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) {r : ℕ}
    {A : Finset (Fin m)} {B : Finset (Fin n)} (h : ¬ (A.card = r ∧ B.card = r)) :
    minor M r A B = 0 := by
  simp [minor, h]

/-- **Cauchy–Binet for minors** (used in Lemma A1 of `C5_divisors_theorem_65.md`):
`det (A B)[I, J] = Σ_{|S| = r} det A[I, S] · det B[S, J]`. -/
theorem minor_mul {m k n r : ℕ} (A : Matrix (Fin m) (Fin k) R) (B : Matrix (Fin k) (Fin n) R)
    {I : Finset (Fin m)} {J : Finset (Fin n)} (hI : I.card = r) (hJ : J.card = r) :
    minor (A * B) r I J =
      ∑ S : {S : Finset (Fin k) // S.card = r}, minor A r I S.1 * minor B r S.1 J := by
  rw [minor_of_card _ hI hJ, submatrix_mul _ _ _ id _ Function.bijective_id, cauchy_binet]
  refine sum_congr rfl fun S _ => ?_
  rw [minor_of_card _ hI S.2, minor_of_card _ S.2 hJ, submatrix_submatrix, submatrix_submatrix]
  rfl

/-- The determinant of a submatrix along injective maps is `±` a minor (rows and columns
reordered increasingly). (Auxiliary for Part A of `C5_divisors_theorem_65.md`.) -/
theorem det_submatrix_eq_or_neg {m n r : ℕ} (M : Matrix (Fin m) (Fin n) R)
    {f : Fin r → Fin m} {g : Fin r → Fin n} (hf : Function.Injective f)
    (hg : Function.Injective g) :
    det (M.submatrix f g) = minor M r (univ.image f) (univ.image g) ∨
      det (M.submatrix f g) = - minor M r (univ.image f) (univ.image g) := by
  have hS := card_image_of_injective_fin hf
  have hT := card_image_of_injective_fin hg
  obtain ⟨σ, hσ⟩ := exists_perm_of_injective hf hS
  obtain ⟨τ, hτ⟩ := exists_perm_of_injective hg hT
  rw [minor_of_card _ hS hT]
  set X := M.submatrix ((univ.image f).orderEmbOfFin hS) ((univ.image g).orderEmbOfFin hT)
  have hX : M.submatrix f g = (X.submatrix σ id).submatrix id τ := by
    ext i j; simp [X, hσ, hτ]
  rw [hX, det_permute', det_permute]
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Perm.sign τ) with h2 | h2 <;> simp [h1, h2]

/-- Every `r × r` minor of `M` is divisible by `2^{dd_r(M)}`. (Part A of
`C5_divisors_theorem_65.md`, consequence of the definition of `dd_r`.) -/
theorem pow_dd_dvd_minor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) (A B : Finset (Fin n)) :
    (2 : ℤ) ^ dd M r ∣ minor M r A B := by
  by_cases h : A.card = r ∧ B.card = r
  · by_cases h0 : minor M r A B = 0
    · rw [h0]; exact dvd_zero _
    · have hle : dd M r ≤ padicValInt 2 (minor M r A B) :=
        Nat.sInf_le ⟨A, B, h.1, h.2, h0, rfl⟩
      exact (pow_dvd_pow _ hle).trans (by exact_mod_cast padicValInt_dvd (p := 2) _)
  · rw [minor_of_not_card _ h]; exact dvd_zero _

/-- If `2^k` divides every `r × r` minor of `M` and some such minor is non-zero, then
`k ≤ dd_r(M)`. (Part A of `C5_divisors_theorem_65.md`.) -/
theorem le_dd_of_dvd {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {r k : ℕ}
    (hne : (minorVals M r).Nonempty)
    (h : ∀ A B : Finset (Fin n), A.card = r → B.card = r → (2 : ℤ) ^ k ∣ minor M r A B) :
    k ≤ dd M r := by
  refine le_csInf hne ?_
  rintro v ⟨A, B, hA, hB, h0, rfl⟩
  have := (padicValInt_dvd_iff (p := 2) k (minor M r A B)).1 (by exact_mod_cast h A B hA hB)
  tauto

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: when the set of valuations is non-empty,
`dd_r(M)` belongs to it (it is a minimum). -/
theorem dd_mem {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {r : ℕ} (hne : (minorVals M r).Nonempty) :
    dd M r ∈ minorVals M r :=
  Nat.sInf_mem hne

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: `dd_r(M) ≤ v_2(det M[A, B])` for every
non-zero `r × r` minor. -/
theorem dd_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) {r : ℕ} {A B : Finset (Fin n)}
    (hA : A.card = r) (hB : B.card = r) (h0 : minor M r A B ≠ 0) :
    dd M r ≤ padicValInt 2 (minor M r A B) :=
  Nat.sInf_le ⟨A, B, hA, hB, h0, rfl⟩

/-- The increasing enumeration of `univ : Finset (Fin n)` is the identity. -/
theorem orderEmbOfFin_univ_apply {n : ℕ} (h : (univ : Finset (Fin n)).card = n) (i : Fin n) :
    (univ : Finset (Fin n)).orderEmbOfFin h i = i := by
  have := orderEmbOfFin_unique h (f := id) (fun x => mem_univ x) strictMono_id
  exact (congrFun this i).symm

/-- The `n × n` minor of an `n × n` matrix is its determinant. -/
theorem minor_univ {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    minor M n univ univ = det M := by
  rw [minor_of_card _ (by simp) (by simp)]
  congr 1
  ext i j
  simp [orderEmbOfFin_univ_apply]

/-- A non-zero `(r+1) × (r+1)` minor gives a non-zero `r × r` minor (Laplace expansion along
the first row). (Auxiliary for Part A of `C5_divisors_theorem_65.md`.) -/
theorem exists_minor_ne_zero_of_succ {m n r : ℕ} (M : Matrix (Fin m) (Fin n) R)
    {A : Finset (Fin m)} {B : Finset (Fin n)} (hA : A.card = r + 1) (hB : B.card = r + 1)
    (h0 : minor M (r + 1) A B ≠ 0) :
    ∃ A' : Finset (Fin m), ∃ B' : Finset (Fin n), A'.card = r ∧ B'.card = r ∧
      minor M r A' B' ≠ 0 := by
  rw [minor_of_card _ hA hB, det_succ_row_zero] at h0
  obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero h0
  set X := M.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)
  have hdet : det (X.submatrix Fin.succ j.succAbove) ≠ 0 := by
    intro h; apply hj; rw [h, mul_zero]
  have hf : Function.Injective (fun i : Fin r => A.orderEmbOfFin hA (Fin.succ i)) :=
    (A.orderEmbOfFin hA).injective.comp (Fin.succ_injective _)
  have hg : Function.Injective (fun i : Fin r => B.orderEmbOfFin hB (j.succAbove i)) :=
    (B.orderEmbOfFin hB).injective.comp Fin.succAbove_right_injective
  have hXeq : X.submatrix Fin.succ j.succAbove = M.submatrix _ _ := rfl
  refine ⟨_, _, card_image_of_injective_fin hf, card_image_of_injective_fin hg, fun hm => ?_⟩
  rcases det_submatrix_eq_or_neg M hf hg with h | h <;>
    exact hdet (by simpa [hXeq, hm] using h)

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: if `det M ≠ 0` then for every `r ≤ n` the
set `{ v_2(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0 }` is non-empty. -/
theorem minorVals_nonempty {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hM : det M ≠ 0) {r : ℕ}
    (hr : r ≤ n) : (minorVals M r).Nonempty := by
  suffices ∀ k, k ≤ n → ∃ A B : Finset (Fin n), A.card = n - k ∧ B.card = n - k ∧
      minor M (n - k) A B ≠ 0 by
    obtain ⟨A, B, hA, hB, h0⟩ := this (n - r) (by omega)
    rw [show n - (n - r) = r by omega] at hA hB h0
    exact ⟨_, A, B, hA, hB, h0, rfl⟩
  intro k
  induction k with
  | zero => exact fun _ => ⟨univ, univ, by simp, by simp, by simpa [minor_univ] using hM⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, B, hA, hB, h0⟩ := ih (by omega)
    rw [show n - k = (n - (k + 1)) + 1 by omega] at hA hB h0
    exact exists_minor_ne_zero_of_succ M hA hB h0

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: `dd_0(M) = 0` (for every `M`). -/
theorem dd_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : dd M 0 = 0 := by
  have h1 : minor M 0 ∅ ∅ = 1 := by
    rw [minor_of_card M (A := ∅) (B := ∅) (by simp) (by simp)]
    exact det_isEmpty
  have h : (0 : ℕ) ∈ minorVals M 0 :=
    ⟨∅, ∅, by simp, by simp, by simp [h1], by simp [h1]⟩
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

/-- *Part A, Setting* of `C5_divisors_theorem_65.md`: `dd_n(M) = v_2(det M)` when
`det M ≠ 0`. -/
theorem dd_top {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hM : det M ≠ 0) :
    dd M n = padicValInt 2 (det M) := by
  have hset : minorVals M n = {padicValInt 2 (det M)} := by
    ext v
    simp only [minorVals, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨A, B, hA, hB, _, rfl⟩
      rw [eq_univ_of_card A (by simpa using hA), eq_univ_of_card B (by simpa using hB),
        minor_univ]
    · rintro rfl
      exact ⟨univ, univ, by simp, by simp, by rwa [minor_univ], by rw [minor_univ]⟩
  rw [dd, hset, csInf_singleton]

/-- Multiplying a matrix by `c` multiplies each `r × r` minor by `c^r`. (Proof of Lemma A1 of
`C5_divisors_theorem_65.md`.) -/
theorem minor_smul {m n : ℕ} (c : R) (M : Matrix (Fin m) (Fin n) R) (r : ℕ)
    (A : Finset (Fin m)) (B : Finset (Fin n)) : minor (c • M) r A B = c ^ r * minor M r A B := by
  by_cases h : A.card = r ∧ B.card = r
  · rw [minor_of_card _ h.1 h.2, minor_of_card _ h.1 h.2,
      show ∀ (f : Fin r → Fin m) (g : Fin r → Fin n), (c • M).submatrix f g
        = c • M.submatrix f g from fun _ _ => rfl, det_smul, Fintype.card_fin]
  · rw [minor_of_not_card _ h, minor_of_not_card _ h, mul_zero]

/-- `v_2(c · a) = v_2(a)` for `c` odd. -/
theorem padicValInt_odd_mul {c a : ℤ} (hc : Odd c) (ha : a ≠ 0) :
    padicValInt 2 (c * a) = padicValInt 2 a := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  rw [padicValInt.mul hc0 ha, padicValInt.eq_zero_of_not_dvd, zero_add]
  rw [← Int.not_even_iff_odd, even_iff_two_dvd] at hc
  exact_mod_cast hc

/-- Multiplying a matrix by an odd integer does not change the set of valuations of its
non-zero `r × r` minors. (Proof of Lemma A1 of `C5_divisors_theorem_65.md`.) -/
theorem minorVals_smul_odd {n : ℕ} {c : ℤ} (hc : Odd c) (M : Matrix (Fin n) (Fin n) ℤ)
    (r : ℕ) : minorVals (c • M) r = minorVals M r := by
  have hcr : Odd (c ^ r) := hc.pow
  have hcr0 : c ^ r ≠ 0 := by intro h; rw [h] at hcr; simp at hcr
  ext v
  simp only [minorVals, Set.mem_setOf_eq, minor_smul]
  constructor
  · rintro ⟨A, B, hA, hB, h0, rfl⟩
    have h0' : minor M r A B ≠ 0 := right_ne_zero_of_mul h0
    exact ⟨A, B, hA, hB, h0', (padicValInt_odd_mul hcr h0').symm⟩
  · rintro ⟨A, B, hA, hB, h0, rfl⟩
    exact ⟨A, B, hA, hB, mul_ne_zero hcr0 h0, padicValInt_odd_mul hcr h0⟩

/-- `dd_r(c M) = dd_r(M)` for every odd integer `c`. (Proof of Lemma A1 of
`C5_divisors_theorem_65.md`.) -/
theorem dd_smul_odd {n : ℕ} {c : ℤ} (hc : Odd c) (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    dd (c • M) r = dd M r := by
  rw [dd, dd, minorVals_smul_odd hc]

end Divisors
