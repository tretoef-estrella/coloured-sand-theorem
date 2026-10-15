module

public import RequestProject.Windows.All
public import RequestProject.CellFloor.All
public import RequestProject.Divisors.All
public import RequestProject.GoldenMatching.All
public import RequestProject.Rulers.All

/-!
# The *Setting* and *Part P* of `C15_smith_form_of_the_dance_matrix.md`

## Encoding (namespace `DanceSmith`)

* **Digit lists** `ds : List Bool` as in C14; `k = ds.length`, `I = Windows.Ids ds`,
  `m = Dance.mCount ds` (`= #I` by `Windows.card_Ids`), `N = 2 ^ Dance.mCount ds`, `K = 2 ^ k`.
* **The matrix** `M = Windows.finalMatrix ℤ ds α i : Matrix (Fin N) (Fin N) ℤ` (C14), with
  `α i : ℕ` (`α` is cast to `ℤ` where needed).
* **Bit reversal.** `bitRev m p` is the number whose bit `m − 1 − j` is bit `j` of `p` (`j < m`),
  defined by `bitRev 0 p = 0`, `bitRev (m+1) p = bitRev m (p / 2) + (p % 2) · 2^m`.
  `sl ds : Fin N → Fin N` is `p ↦ bitRev m p`, and `slPerm ds` is the same map as a permutation
  of `Fin N` (it is an involution).
* **The o-order matrix** `Mo ds α i p q = M (sl p) (sl q)`, i.e.
  `(finalMatrix ℤ ds α i).submatrix (sl ds) (sl ds)`.
* **Simultaneous permutation** of rows and columns of `M : Matrix (Fin n) (Fin n) ℤ` by
  `σ : Equiv.Perm (Fin n)` is `M.submatrix σ σ`.
* `Divisors.dd` and `Divisors.minor` are those of C5.
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix

/-! ### Bit reversal -/

/-- *Setting* ("Dancers in o-order") of `C15_smith_form_of_the_dance_matrix.md`: the bit reversal
of `p` on `m` bits (bit `m − 1 − j` of `bitRev m p` is bit `j` of `p`, for `j < m`). -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, p => bitRev m (p / 2) + (p % 2) * 2 ^ m

lemma bitRev_lt (m p : ℕ) : bitRev m p < 2 ^ m := by
  induction m generalizing p with
  | zero => simp [bitRev]
  | succ m ih =>
    simp only [bitRev, pow_succ]
    have := ih (p / 2)
    have : p % 2 ≤ 1 := by omega
    nlinarith

lemma testBit_bitRev (m p j : ℕ) (hj : j < m) :
    (bitRev m p).testBit j = p.testBit (m - 1 - j) := by
  induction m generalizing p j with
  | zero => omega
  | succ m ih =>
    simp only [bitRev]
    have hlt := bitRev_lt m (p / 2)
    rcases Nat.lt_or_ge j m with h | h
    · rw [show bitRev m (p / 2) + p % 2 * 2 ^ m = 2 ^ m * (p % 2) + bitRev m (p / 2) by ring,
        Nat.testBit_two_pow_mul_add _ hlt, if_pos h, ih _ _ h, Nat.testBit_div_two]
      congr 1; omega
    · obtain rfl : j = m := by omega
      rw [show bitRev j (p / 2) + p % 2 * 2 ^ j = 2 ^ j * (p % 2) + bitRev j (p / 2) by ring,
        Nat.testBit_two_pow_mul_add _ hlt, if_neg (by omega), show j + 1 - 1 - j = 0 by omega,
        Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one p with h2 | h2 <;> simp [h2]

lemma bitRev_bitRev {m p : ℕ} (hp : p < 2 ^ m) : bitRev m (bitRev m p) = p := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j m with h | h
  · rw [testBit_bitRev _ _ _ h, testBit_bitRev _ _ _ (by omega)]
    congr 1; omega
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitRev_lt _ _) (Nat.pow_le_pow_right two_pos h)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hp (Nat.pow_le_pow_right two_pos h))]

/-- *Setting* ("Dancers in o-order") of `C15_smith_form_of_the_dance_matrix.md`: the slot
`sl(p)` of the `p`-th dancer in o-order, the bit reversal of `p` on `m = mCount ds` bits. -/
def sl (ds : List Bool) (p : Fin (2 ^ Dance.mCount ds)) : Fin (2 ^ Dance.mCount ds) :=
  ⟨bitRev (Dance.mCount ds) p, bitRev_lt _ _⟩

lemma sl_sl (ds : List Bool) (p : Fin (2 ^ Dance.mCount ds)) : sl ds (sl ds p) = p :=
  Fin.ext (bitRev_bitRev p.2)

/-- `sl` as a permutation of `Fin N` (an involution). (*Setting* of
`C15_smith_form_of_the_dance_matrix.md`.) -/
def slPerm (ds : List Bool) : Equiv.Perm (Fin (2 ^ Dance.mCount ds)) where
  toFun := sl ds
  invFun := sl ds
  left_inv := sl_sl ds
  right_inv := sl_sl ds

@[simp] lemma slPerm_apply (ds : List Bool) (p : Fin (2 ^ Dance.mCount ds)) :
    slPerm ds p = sl ds p := rfl

/-- *Setting* of `C15_smith_form_of_the_dance_matrix.md`: the matrix in o-order,
`Mo p q := M (sl p) (sl q)` with `M = Windows.finalMatrix ℤ ds α i`. -/
noncomputable def Mo (ds : List Bool) (α i : ℕ) :
    Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ :=
  (Windows.finalMatrix ℤ ds α i).submatrix (sl ds) (sl ds)

/-! ### Part P -/

lemma rank_lt_card {I : Finset ℕ} {t : ℕ} (ht : t ∈ I) : Windows.rank I t < #I := by
  unfold Windows.rank
  exact card_lt_card (filter_ssubset.2 ⟨t, ht, lt_irrefl t⟩)

/-- **(P1)** of `C15_smith_form_of_the_dance_matrix.md`: `sl` is an involution (hence a bijection)
of `{0, …, N − 1}`, and `Windows.Dset ds (sl p) = TheoremF.dancer I p` for every `p < N`. -/
theorem P1 (ds : List Bool) :
    (∀ p, sl ds (sl ds p) = p) ∧ Function.Bijective (sl ds) ∧
      ∀ p : Fin (2 ^ Dance.mCount ds),
        Windows.Dset ds (sl ds p) = TheoremF.dancer (Windows.Ids ds) p := by
  refine ⟨sl_sl ds, (slPerm ds).bijective, fun p => ?_⟩
  unfold Windows.Dset TheoremF.dancer
  apply filter_congr
  intro t ht
  have hr := rank_lt_card ht
  rw [Windows.card_Ids] at hr
  simp only [sl]
  rw [testBit_bitRev _ _ _ (by omega), show Dance.mCount ds - 1 -
    (Dance.mCount ds - 1 - Windows.rank (Windows.Ids ds) t) = Windows.rank (Windows.Ids ds) t by
    omega, Nat.testBit_eq_decide_div_mod_eq, Houses.bit]
  simp [Windows.rank]

/-- `M.submatrix σ σ = P M Pᵀ` with `P` the permutation matrix of `σ`. (Proof of (P2) of
`C15_smith_form_of_the_dance_matrix.md`.) -/
lemma submatrix_perm_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ) :
    M.submatrix σ σ = σ.permMatrix ℤ * M * Equiv.Perm.permMatrix ℤ σ⁻¹ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

lemma odd_det_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Odd (σ.permMatrix ℤ).det := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **(P2)** of `C15_smith_form_of_the_dance_matrix.md`, general form: for any `n`, any permutation
`σ` of `Fin n`, any `M : Matrix (Fin n) (Fin n) ℤ` and every `r`,
`Divisors.dd (M.submatrix σ σ) r = Divisors.dd M r`. -/
theorem P2_general {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    Divisors.dd (M.submatrix σ σ) r = Divisors.dd M r := by
  rw [submatrix_perm_eq]
  exact Divisors.lemma_A1 M _ _ (odd_det_permMatrix σ) (odd_det_permMatrix _) r

/-- **(P2)** of `C15_smith_form_of_the_dance_matrix.md`: for every `r`,
`Divisors.dd Mo r = Divisors.dd M r`. -/
theorem P2 (ds : List Bool) (α i r : ℕ) :
    Divisors.dd (Mo ds α i) r = Divisors.dd (Windows.finalMatrix ℤ ds α i) r :=
  P2_general (slPerm ds) _ r

/-- `Mo = P M Pᵀ` with `P` of odd determinant (the permutation matrix of `sl`). (Used in Parts S
and Z of `C15_smith_form_of_the_dance_matrix.md`.) -/
lemma Mo_eq_mul (ds : List Bool) (α i : ℕ) :
    Mo ds α i = (slPerm ds).permMatrix ℤ * Windows.finalMatrix ℤ ds α i *
      Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ :=
  submatrix_perm_eq (slPerm ds) _

end DanceSmith
