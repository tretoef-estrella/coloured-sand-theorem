module

public import RequestProject.TheoremB.Basic

/-!
# (B2) Ballot numbers

This file corresponds to **(B2) Ballot numbers** of `CS3_theorem_B.md`.

## Encoding

* `ballot k v : ℕ` is `C(v+2k−1, k) − C(v+2k−1, k−1)`, with the convention `C(n, −1) = 0`
  (written `if k = 0 then 0 else C(v+2k−1, k−1)`) and truncated subtraction on `ℕ`.
  `ballot_cast` shows that for `v ≥ 1` the subtraction does not truncate, i.e. `b(k,v)` is the
  integer `C(v+2k−1, k) − C(v+2k−1, k−1)`.
* `ballot_eq` is the identity `C(v+2k−1, k) − C(v+2k−1, k−1) = (v/(v+2k))·C(v+2k, k)`, stated in
  `ℚ`.
* `ballot_eq_strMult` relates `b(k,v)` to the string multiplicity
  `strMult m k = C(m,k) − C(m,k−1)` of CS1 (`RequestProject/Strings/Global.lean`), for
  `m = v + 2k − 1`.
-/

@[expose] public section

namespace ColouredSand.TheoremB

/-- The ballot number `b(k, v) = C(v+2k−1, k) − C(v+2k−1, k−1)` (with `C(n,−1) = 0`), (B2). -/
def ballot (k v : ℕ) : ℕ :=
  (v + 2 * k - 1).choose k - if k = 0 then 0 else (v + 2 * k - 1).choose (k - 1)

lemma ballot_eq_strMult (k v : ℕ) : ballot k v = ColouredSand.Strings.strMult (v + 2 * k - 1) k :=
  rfl

/-- The key relation `C(n,k-1) ≤ C(n,k)` for `n = v + 2k − 1`, `v ≥ 1`, in the form
`C(n,k'+1) (k'+1) = C(n,k') (v + k' + 1)`. -/
lemma choose_rel (v k : ℕ) :
    (v + 2 * k + 1).choose (k + 1) * (k + 1) = (v + 2 * k + 1).choose k * (v + k + 1) := by
  rw [Nat.choose_succ_right_eq]
  congr 1
  omega

/-- **(B2)**: for `v ≥ 1`, `k ≥ 0`, `C(v+2k−1, k) − C(v+2k−1, k−1) = (v/(v+2k))·C(v+2k, k)`
(with `C(n, −1) = 0`), as rational numbers. -/
theorem ballot_identity (v k : ℕ) (hv : 1 ≤ v) :
    ((v + 2 * k - 1).choose k : ℚ) - (if k = 0 then 0 else ((v + 2 * k - 1).choose (k - 1) : ℚ)) =
      (v : ℚ) / (v + 2 * k) * (v + 2 * k).choose k := by
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  rcases k with _ | k
  · simp [hv0]
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have e1 : w + 1 + 2 * (k + 1) - 1 = w + 2 * k + 1 + 1 := by omega
    have e2 : w + 1 + 2 * (k + 1) = (w + 2 * k + 2) + 1 := by omega
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [e1]
    have hrel := choose_rel (w + 1) k
    rw [show w + 1 + 2 * k + 1 = w + 2 * k + 1 + 1 by omega] at hrel
    have hpas := Nat.choose_succ_succ (w + 2 * k + 2) k
    rw [show ((w + 1 : ℕ) : ℚ) + 2 * ((k + 1 : ℕ) : ℚ) = ((w + 2 * k + 2 + 1 : ℕ) : ℚ) by
      push_cast; ring]
    rw [show w + 2 * k + 1 + 1 = w + 2 * k + 2 by omega] at hrel ⊢
    rw [e2, hpas]
    have hrel' : ((w + 2 * k + 2).choose (k + 1) : ℚ) * (k + 1) =
        ((w + 2 * k + 2).choose k : ℚ) * (w + 1 + k + 1) := by exact_mod_cast hrel
    have hpos : ((w + 2 * k + 2 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    linear_combination 2 * hrel'

/-- `b(k,v)` is an integer: for `v ≥ 1` the truncated subtraction in `ballot` is exact, so
`b(k,v) = C(v+2k−1, k) − C(v+2k−1, k−1) = (v/(v+2k))·C(v+2k, k)`. -/
theorem ballot_cast (v k : ℕ) (hv : 1 ≤ v) :
    (ballot k v : ℚ) =
      ((v + 2 * k - 1).choose k : ℚ) - (if k = 0 then 0 else ((v + 2 * k - 1).choose (k - 1) : ℚ))
    ∧ (ballot k v : ℚ) = (v : ℚ) / (v + 2 * k) * (v + 2 * k).choose k := by
  have hle : (if k = 0 then 0 else (v + 2 * k - 1).choose (k - 1)) ≤ (v + 2 * k - 1).choose k := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have hrel := choose_rel w k
      rw [show w + 1 + 2 * (k + 1) - 1 = w + 2 * k + 1 + 1 by omega]
      have h2 := choose_rel (w + 1) k
      rw [show w + 1 + 2 * k + 1 = w + 2 * k + 1 + 1 by omega] at h2
      by_contra hlt
      push_neg at hlt
      have : (w + 2 * k + 1 + 1).choose (k + 1) * (k + 1) <
          (w + 2 * k + 1 + 1).choose k * (w + 1 + k + 1) :=
        calc (w + 2 * k + 1 + 1).choose (k + 1) * (k + 1)
            < (w + 2 * k + 1 + 1).choose k * (k + 1) :=
              Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos _)
          _ ≤ (w + 2 * k + 1 + 1).choose k * (w + 1 + k + 1) :=
              Nat.mul_le_mul_left _ (by omega)
      omega
  have hc : (ballot k v : ℚ) =
      ((v + 2 * k - 1).choose k : ℚ) -
        (if k = 0 then 0 else ((v + 2 * k - 1).choose (k - 1) : ℚ)) := by
    unfold ballot
    rw [Nat.cast_sub hle]
    split_ifs <;> simp
  exact ⟨hc, hc.trans (ballot_identity v k hv)⟩

end ColouredSand.TheoremB
