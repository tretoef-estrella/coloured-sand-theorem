module

public import RequestProject.OddDeficit.DeficitLaw
public import RequestProject.OddTheoremI.Basic

/-!
# `CSI11_the_odd_deficit_law.md` — **(D1)** stated for `λ` (CSI10's digits)

Namespace `ColouredSand.OddTwist`.  The opening block of the file says: «If you state (D1) also
for `λ`, the digit list is `ds = (Nat.digits p (λ+1)).take (kTop p λ)` and the top digit is
`digitL p λ (kTop p λ)`.»  This file does that.  It uses CSI10's `digitL`, `kTop` and `Iset`
unchanged.

* `Iod_lambda`: for this digit list, `Iod ds = Iset p λ`, and `ds.length = kTop p λ`.
* `D1_lambda`: (D1) for `λ`.  The hypotheses on the digits (all `< p`, top digit in
  `[1, p − 1]`) are proved here, not assumed.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- The digit list `d_0, …, d_{k−1}` of `λ + 1` in base `p` (lowest first, top digit removed),
as in the opening block of `CSI11_the_odd_deficit_law.md`. -/
def dsL (p l : ℕ) : List ℕ := (Nat.digits p (l + 1)).take (kTop p l)

lemma length_dsL (p l : ℕ) : (dsL p l).length = kTop p l := by
  unfold dsL kTop
  rw [List.length_take]; omega

lemma getD_dsL (p l t : ℕ) (ht : t < kTop p l) : (dsL p l).getD t 0 = digitL p l t := by
  unfold dsL digitL
  have h1 : t < ((Nat.digits p (l + 1)).take (kTop p l)).length := by
    rw [List.length_take]; unfold kTop at ht ⊢; omega
  have h2 : t < (Nat.digits p (l + 1)).length := by unfold kTop at ht; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_take]

/-- For CSI10's digits, `I(ds) = Iset p λ` (`CSI11_the_odd_deficit_law.md`, opening block, and
`CSI10`'s Setting). -/
theorem Iod_lambda (p l : ℕ) : Iod (dsL p l) = Iset p l := by
  ext t
  simp only [Iod, Iset, mem_filter, mem_range, length_dsL]
  constructor
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [← getD_dsL p l t ht]⟩
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [getD_dsL p l t ht]⟩

/-- **(D1) for `λ`** (`CSI11_the_odd_deficit_law.md`, Part D, with CSI10's digits): for `p` an
odd prime and any `λ`, let `k = kTop p λ`, `d_k = digitL p λ k`, and
`q_t = aP p (dsL p λ) t` with `dsL p λ = (Nat.digits p (λ+1)).take k`.  Then
`[q_k^{d_k}]_∅ = 1`, and for every non-empty `Δ ⊆ Iset p λ` the coefficient
`[q_k^{d_k}]_Δ` is non-zero with `v_p = k − |Δ| − min Δ`. -/
theorem D1_lambda {p : ℕ} (hp : p.Prime) (hodd : Odd p) (l : ℕ) :
    starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iset p l →
        starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ ≠ 0 ∧
          padicValInt p (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ) =
            kTop p l - Δ.card - Δ.min' h := by
  have hds : ∀ d ∈ dsL p l, d < p := fun d hd =>
    Nat.digits_lt_base hp.one_lt (List.mem_of_mem_take hd)
  have hne : Nat.digits p (l + 1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hlen : kTop p l < (Nat.digits p (l + 1)).length := by
    unfold kTop; have := List.length_pos_of_ne_nil hne; omega
  have htop : digitL p l (kTop p l) = (Nat.digits p (l + 1)).getLast hne := by
    unfold digitL
    rw [List.getD_eq_getElem _ _ hlen, List.getLast_eq_getElem]
    rfl
  have hdk0 : digitL p l (kTop p l) ≠ 0 := by
    rw [htop]; exact Nat.getLast_digit_ne_zero p (by omega)
  have hdkp : digitL p l (kTop p l) < p := by
    rw [htop]; exact Nat.digits_lt_base hp.one_lt (List.getLast_mem hne)
  have hD := oddDef_D1 hp hodd hds (digitL p l (kTop p l)) (by omega) (by omega)
  rw [length_dsL, Iod_lambda] at hD
  exact hD

end ColouredSand.OddTwist
