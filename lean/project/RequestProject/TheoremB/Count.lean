module

public import RequestProject.TheoremB.Ballot

/-!
# The multiplicities `n_v` of Theorem B and the reindexing of the summands

This file corresponds to the definition of `n_v` in **(B3) Theorem B** of `CS3_theorem_B.md`,
and to the step "put `v = m − 2k + 1`, … collect the factors" of its proof.

## Encoding

* `nCount d q v` is `n_v = Σ_{j,k ≥ 0, j + 2k = d + 1 − v, (j,k) ≠ (0,0)} C(d,j) (q−2)^j b(k,v)`.
  The sum is written over `j, k ∈ {0, …, d}` (this is no restriction when `1 ≤ v ≤ d`, since
  then `j + 2k = d + 1 − v ≤ d`), with `b(k,v) = ballot k v` from
  `RequestProject/TheoremB/Ballot.lean` and `q − 2` the truncated subtraction on `ℕ` (exact for
  `q ≥ 2`).
* `BigIdx d q` indexes all the cyclic summands obtained from Theorem A (CS2) and Theorem E (CS1):
  a piece `σ = (j, i)` of Theorem A (`i < C(d,j) (q−2)^j`), then a string `(k, l)` of Theorem E
  for `m = d − j` and `c = j` (`k ≤ m/2`, `(j,k) ≠ (0,0)`, `l < C(m,k) − C(m,k−1)`).
* `gIdx` sends such an index to `v − 1 = m − 2k ∈ Fin d`; `bigIdxEquiv` identifies `BigIdx d q`
  with `Σ v : Fin d, Fin (n_{v+1})` compatibly with `gIdx` (`card_fiber_gIdx` is the count).
-/

@[expose] public section

open Finset

namespace ColouredSand.TheoremB

open ColouredSand.Strings

/-- `n_v = Σ_{j + 2k = d + 1 − v, (j,k) ≠ (0,0)} C(d,j) (q−2)^j b(k,v)` (B3), the sum being taken
over `0 ≤ j, k ≤ d`. -/
def nCount (d q v : ℕ) : ℕ :=
  ∑ j ∈ range (d + 1), ∑ k ∈ range (d + 1),
    if j + 2 * k = d + 1 - v ∧ (j, k) ≠ (0, 0) then d.choose j * (q - 2) ^ j * ballot k v else 0

/-- The pieces of Theorem A: `σ = (j, i)` with `i < C(d,j) (q−2)^j`. -/
abbrev PieceIdx (d q : ℕ) : Type := Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))

/-- The torsion strings of Theorem E for `(c, m)`: `(k, l)` with `k ≤ m/2`, `(c,k) ≠ (0,0)`,
`l < C(m,k) − C(m,k−1)`. -/
abbrev StrIdxE (c m : ℕ) : Type :=
  Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)

/-- All cyclic summands: a piece `σ = (j,i)`, then a torsion string of `X_q(d−j, j)`. -/
abbrev BigIdx (d q : ℕ) : Type := Σ σ : PieceIdx d q, StrIdxE σ.1 (d - σ.1)

lemma gIdx_lt {d : ℕ} (hd : 1 ≤ d) {j k : ℕ} (hjk : (j, k) ≠ (0, 0)) :
    d - j - 2 * k < d := by
  have : j ≠ 0 ∨ k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hjk (by rw [h.1, h.2])
  omega

/-- `gIdx x = v − 1 = m − 2k` for `x = ((j,i),(k,l))`, `m = d − j`. -/
def gIdx {d q : ℕ} (hd : 1 ≤ d) (x : BigIdx d q) : Fin d :=
  ⟨d - x.1.1 - 2 * x.2.1.val.val, gIdx_lt hd x.2.1.property⟩

lemma gIdx_val {d q : ℕ} (hd : 1 ≤ d) (x : BigIdx d q) :
    (gIdx hd x : ℕ) = d - x.1.1 - 2 * x.2.1.val.val := rfl

lemma sum_subtype_fin (M : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    ∑ k : {k : Fin (M + 1) // P k}, f k = ∑ k ∈ range (M + 1), if P k then f k else 0 := by
  rw [← Finset.sum_subtype (univ.filter (fun k : Fin (M + 1) => P k)) (by simp)
    (fun k => f k), Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun k => if P k then f k else 0) _

/-- The count for a fixed `j`. -/
lemma count_fixed_j {d j v : ℕ} (hj : j ≤ d) (hv : v < d) :
    ∑ k : {k : Fin ((d - j) / 2 + 1) // (j, (k : ℕ)) ≠ (0, 0)},
        (if d - j - 2 * (k : ℕ) = v then strMult (d - j) k else 0) =
      ∑ k ∈ range (d + 1),
        if j + 2 * k = d + 1 - (v + 1) ∧ (j, k) ≠ (0, 0) then ballot k (v + 1) else 0 := by
  rw [sum_subtype_fin _ (fun k => (j, k) ≠ (0, 0))
    (fun k => if d - j - 2 * k = v then strMult (d - j) k else 0)]
  have hsub : range ((d - j) / 2 + 1) ⊆ range (d + 1) := by
    intro k; simp only [mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    by_cases h1 : (j, k) ≠ (0, 0)
    · by_cases h2 : d - j - 2 * k = v
      · rw [if_pos h1, if_pos h2, if_pos ⟨by omega, h1⟩, ballot_eq_strMult]
        congr 1
        omega
      · rw [if_pos h1, if_neg h2, if_neg]
        rintro ⟨h3, -⟩
        omega
    · rw [if_neg h1, if_neg]
      rintro ⟨-, h3⟩
      exact h1 h3
  · intro k _ hk
    rw [mem_range] at hk
    rw [if_neg]
    rintro ⟨h3, -⟩
    omega

/-- **The count**: the number of cyclic summands with `m − 2k = v − 1` is `n_v`. -/
theorem card_fiber_gIdx {d q : ℕ} (hd : 1 ≤ d) (v : Fin d) :
    Fintype.card {x : BigIdx d q // gIdx hd x = v} = nCount d q (v + 1) := by
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_sigma, Fin.ext_iff, gIdx_val]
  simp only [Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [Finset.filter_const, apply_ite Finset.card, Finset.card_univ, Fintype.card_fin,
    Finset.card_empty, Nat.cast_id]
  rw [nCount, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := Nat.lt_succ_iff.mp j.2
  rw [count_fixed_j hj v.2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- The reindexing `BigIdx d q ≃ Σ v : Fin d, Fin (n_{v+1})`, compatible with `gIdx`. -/
noncomputable def bigIdxEquiv {d q : ℕ} (hd : 1 ≤ d) :
    BigIdx d q ≃ Σ v : Fin d, Fin (nCount d q (v + 1)) :=
  (Equiv.sigmaFiberEquiv (gIdx (q := q) hd)).symm.trans
    (Equiv.sigmaCongrRight fun v => Fintype.equivFinOfCardEq (card_fiber_gIdx hd v))

lemma bigIdxEquiv_fst {d q : ℕ} (hd : 1 ≤ d) (x : BigIdx d q) :
    (bigIdxEquiv hd x).1 = gIdx hd x := rfl

end ColouredSand.TheoremB
