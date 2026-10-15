module

public import RequestProject.Doubling.All

/-!
# `CSI1_the_odd_twist.md`: Setting, and (A0) — the coefficient `q(c, r)`

Encodings (namespace `ColouredSand.OddTwist`), reusing C18 (`DPLattice`, `IsDP`, `H`, `Hom`,
`InWt`, `one`, `delta`, `nabla`, …), C19 (`WeylFilt.Hom.id`, `WeylFilt.Hom.comp`,
`WeylFilt.ShortExact`) and C20 (`Doubling.RecData`, `Doubling.isDP_of_rec`, `Doubling.homOfOne`,
`Doubling.comm_of_rec`, `Doubling.Iso`, `Doubling.Iso.ofInverse`, …):

* `p` is a natural number with `[Fact p.Prime]` and the ring is `A = ℤ_[p]` (Mathlib's `p`-adic
  integers, a domain of characteristic zero). The hypothesis `p ≠ 2` of the file turns out not to
  be needed anywhere (every statement of this folder holds for every prime `p`, which is more
  general; for `p = 2` the construction is a rescaled form of C20's `Φ`).
* `qc p c r : ℤ_[p]` is the coefficient `q(c, r) = p^c · c! / r!` of the Setting. It is defined
  directly inside `ℤ_[p]`: writing `n! = p^{v_p(n!)} · n!'` with `n!'` prime to `p` (Mathlib's
  `ordProj`/`ordCompl`), `qc p c r := p^{c + v_p(c!) − v_p(r!)} · c!' · (r!')⁻¹` (the inverse
  `Ring.inverse` in `ℤ_[p]`, a genuine inverse since `r!'` is prime to `p`). (A0) is `A0`: for
  `r / p ≤ c` (natural-number division), `(r! : ℤ_[p]) · qc p c r = p^c · c!`, the image of
  `qc p c r` in `ℚ_[p]` is `p^c · c! / r!`, and this `p`-adic number has norm `≤ 1`.
* Slot vectors: for a basis type `ι`, the module `Fin p × ι → A` is `A^p ⊗ (ι → A)`; for a natural
  number `k`, `bv p k n` is the vector "with `n` in slot `k`", i.e. `b_k n`
  (`bv p k n (j, i) = n i` if `j = k`, and `0` otherwise). Slots are indexed by natural numbers so
  that the formulas of the file (`b_{j+1}`, `b_{j+r−pc}`, …) can be written literally; for
  `k ≥ p` the vector `bv p k n` is `0` (this never occurs in the formulas, where the index is
  always proved to be `< p`). `sl p j x` is the slot `j` of `x`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

/-! ### Integers prime to `p` are units of `ℤ_[p]` -/

section units

variable (p : ℕ) [Fact p.Prime]

/-- Setting: an integer prime to `p` is a unit of `ℤ_[p]`. -/
lemma isUnit_natCast_of_coprime {n : ℕ} (h : p.Coprime n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; exact h

/-- A natural number which is not divisible by `p` is a unit of `ℤ_[p]`. -/
lemma isUnit_natCast_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) :=
  isUnit_natCast_of_coprime p ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr h)

/-! ### Legendre's inequality -/

/-- (A0) Legendre: if `r / p ≤ c` then `v_p(r!) ≤ c + v_p(c!)`. -/
lemma legendre_le {c r : ℕ} (h : r / p ≤ c) :
    padicValNat p r ! ≤ c + padicValNat p c ! := by
  have hr : r = p * (r / p) + r % p := (Nat.div_add_mod r p).symm
  have hlt : r % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  have h1 : padicValNat p r ! = padicValNat p (r / p) ! + r / p := by
    rw [hr, padicValNat_factorial_mul_add _ hlt, padicValNat_factorial_mul, ← hr]
  have h2 : padicValNat p (r / p) ! ≤ padicValNat p c ! := by
    have hd : (r / p)! ∣ c ! := Nat.factorial_dvd_factorial h
    rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero c)]
    exact (pow_padicValNat_dvd).trans hd
  omega

/-! ### The coefficient `q(c, r)` -/

/-- Setting, (A0): the coefficient `q(c, r) = p^c · c! / r!` as an element of `ℤ_[p]`
(meaningful for `r / p ≤ c`, see `A0`): `p^{c + v_p(c!) − v_p(r!)} · c!' · (r!')⁻¹`, where
`n! = p^{v_p(n!)} · n!'` with `n!'` prime to `p`. -/
def qc (c r : ℕ) : ℤ_[p] :=
  (p : ℤ_[p]) ^ (c + (c !).factorization p - (r !).factorization p) *
    (((c ! / p ^ (c !).factorization p : ℕ)) : ℤ_[p]) *
    Ring.inverse (((r ! / p ^ (r !).factorization p : ℕ)) : ℤ_[p])

lemma isUnit_ordCompl_factorial (r : ℕ) :
    IsUnit (((r ! / p ^ (r !).factorization p : ℕ)) : ℤ_[p]) :=
  isUnit_natCast_of_coprime p (Nat.coprime_ordCompl Fact.out (Nat.factorial_ne_zero r))

/-- (A0), the identity: for `r / p ≤ c`, `(r! : ℤ_[p]) · q(c, r) = p^c · c!`. -/
theorem qc_spec {c r : ℕ} (h : r / p ≤ c) :
    ((r ! : ℕ) : ℤ_[p]) * qc p c r = (p : ℤ_[p]) ^ c * ((c ! : ℕ) : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  have hle : (r !).factorization p ≤ c + (c !).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]; exact legendre_le p h
  have er := Nat.ordProj_mul_ordCompl_eq_self (r !) p
  have ec := Nat.ordProj_mul_ordCompl_eq_self (c !) p
  set vr := (r !).factorization p
  set vc := (c !).factorization p
  set orr := r ! / p ^ vr
  set occ := c ! / p ^ vc
  have hu := isUnit_ordCompl_factorial p r
  have hr' : ((r ! : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ vr * (orr : ℤ_[p]) := by exact_mod_cast er.symm
  have hc' : ((c ! : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ vc * (occ : ℤ_[p]) := by exact_mod_cast ec.symm
  rw [qc, hr', hc']
  have hinv : (orr : ℤ_[p]) * Ring.inverse (orr : ℤ_[p]) = 1 := Ring.mul_inverse_cancel _ hu
  have hpow : (p : ℤ_[p]) ^ vr * (p : ℤ_[p]) ^ (c + vc - vr) = (p : ℤ_[p]) ^ c * (p : ℤ_[p]) ^ vc := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  calc (p : ℤ_[p]) ^ vr * (orr : ℤ_[p]) *
        ((p : ℤ_[p]) ^ (c + vc - vr) * (occ : ℤ_[p]) * Ring.inverse (orr : ℤ_[p]))
      = ((p : ℤ_[p]) ^ vr * (p : ℤ_[p]) ^ (c + vc - vr)) * (occ : ℤ_[p]) *
          ((orr : ℤ_[p]) * Ring.inverse (orr : ℤ_[p])) := by ring
    _ = (p : ℤ_[p]) ^ c * ((p : ℤ_[p]) ^ vc * (occ : ℤ_[p])) := by rw [hinv, hpow]; ring

/-- (A0), the image in `ℚ_[p]`: for `r / p ≤ c`, `(q(c, r) : ℚ_[p]) = p^c · c! / r!`. -/
theorem qc_coe {c r : ℕ} (h : r / p ≤ c) :
    ((qc p c r : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ c * ((c ! : ℕ) : ℚ_[p]) / ((r ! : ℕ) : ℚ_[p]) := by
  have hr : ((r ! : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  rw [eq_div_iff hr, mul_comm]
  have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) (qc_spec p h)
  simpa using this

/-- (A0) The `p`-adic number `p^c · c! / r!` lies in `ℤ_[p]` (norm `≤ 1`) for `r / p ≤ c`,
`q(c, r)` is its preimage, and `(r! : ℤ_[p]) · q(c, r) = p^c · c!`. -/
theorem A0 {c r : ℕ} (h : r / p ≤ c) :
    ‖(p : ℚ_[p]) ^ c * ((c ! : ℕ) : ℚ_[p]) / ((r ! : ℕ) : ℚ_[p])‖ ≤ 1 ∧
    ((qc p c r : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ c * ((c ! : ℕ) : ℚ_[p]) / ((r ! : ℕ) : ℚ_[p]) ∧
    ((r ! : ℕ) : ℤ_[p]) * qc p c r = (p : ℤ_[p]) ^ c * ((c ! : ℕ) : ℤ_[p]) := by
  refine ⟨?_, qc_coe p h, qc_spec p h⟩
  rw [← qc_coe p h]
  exact (qc p c r).2

/-- The two recursions of `q(c, r)` used in Part A (no wrap / wrap), consequences of (A0):
`q(c, r) = (r+1) · q(c, r+1)` for `(r+1)/p ≤ c`. -/
lemma qc_succ {c r : ℕ} (h : (r + 1) / p ≤ c) :
    qc p c r = ((r : ℤ_[p]) + 1) * qc p c (r + 1) := by
  have h' : r / p ≤ c := le_trans (Nat.div_le_div_right (Nat.le_succ r)) h
  have hr : ((r ! : ℕ) : ℤ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  apply mul_left_cancel₀ hr
  rw [qc_spec p h', ← mul_assoc]
  have := qc_spec p h
  rw [Nat.factorial_succ] at this
  push_cast at this ⊢
  linear_combination -this

/-- The wrap recursion of `q(c, r)`: `p (c+1) q(c, r) = (r+1) q(c+1, r+1)` for `r / p ≤ c`. -/
lemma qc_succ_succ {c r : ℕ} (h : r / p ≤ c) :
    (p : ℤ_[p]) * ((c : ℤ_[p]) + 1) * qc p c r = ((r : ℤ_[p]) + 1) * qc p (c + 1) (r + 1) := by
  have h' : (r + 1) / p ≤ c + 1 := by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    calc (r + 1) / p ≤ r / p + 1 := by
          rw [Nat.div_le_iff_le_mul_add_pred hp]
          have := Nat.lt_mul_div_succ r hp
          nlinarith [Nat.div_mul_le_self r p]
      _ ≤ c + 1 := by omega
  have hr : ((r ! : ℕ) : ℤ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  apply mul_left_cancel₀ hr
  have h1 := qc_spec p h
  have h2 := qc_spec p h'
  rw [Nat.factorial_succ, Nat.factorial_succ] at h2
  push_cast at h1 h2 ⊢
  linear_combination ((p : ℤ_[p]) * ((c : ℤ_[p]) + 1)) * h1 - h2

end units

/-! ### Slot vectors -/

section slots

variable {A : Type*} [CommRing A] (p : ℕ) {ι : Type*}

/-- Setting: `b_k n`, the vector of `Fin p × ι → A` with `n` in slot `k` (zero if `k ≥ p`). -/
def bv (k : ℕ) : (ι → A) →ₗ[A] (Fin p × ι → A) where
  toFun n x := if (x.1 : ℕ) = k then n x.2 else 0
  map_add' m m' := by funext x; by_cases h : (x.1 : ℕ) = k <;> simp [h]
  map_smul' c m := by funext x; by_cases h : (x.1 : ℕ) = k <;> simp [h]

/-- Setting: the slot `j` of a vector of `Fin p × ι → A`. -/
def sl (j : Fin p) : (Fin p × ι → A) →ₗ[A] (ι → A) where
  toFun f i := f (j, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma bv_apply (k : ℕ) (n : ι → A) (x : Fin p × ι) :
    bv p k n x = if (x.1 : ℕ) = k then n x.2 else 0 := rfl

@[simp] lemma sl_apply (j : Fin p) (f : Fin p × ι → A) (i : ι) : sl p j f i = f (j, i) := rfl

lemma sl_bv (j : Fin p) (k : ℕ) (n : ι → A) :
    sl p j (bv p k n) = if (j : ℕ) = k then n else 0 := by
  funext i; by_cases h : (j : ℕ) = k <;> simp [h]

lemma single_eq_bv [DecidableEq ι] (j : Fin p) (i : ι) :
    (Pi.single (j, i) (1 : A) : Fin p × ι → A) = bv p j (Pi.single i 1) := by
  funext ⟨j', i'⟩
  by_cases hj : j' = j <;> by_cases hi : i' = i <;>
    simp [Pi.single_apply, hj, hi, Fin.val_eq_val]

lemma eq_sum_bv [Fintype ι] (f : Fin p × ι → A) : f = ∑ j : Fin p, bv p j (sl p j f) := by
  funext ⟨j, i⟩
  simp only [Finset.sum_apply, bv_apply, sl_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Fin.val_eq_val, Ne.symm hb]
  · simp

lemma bv_of_ge {k : ℕ} (hk : p ≤ k) (n : ι → A) : bv p k n = 0 := by
  funext ⟨j, i⟩; have := j.isLt; simp only [bv_apply]; rw [if_neg (by omega)]; rfl

/-- Weights of slot vectors: if `n` has weight `μ` for `wt`, then `b_k n` has weight `ν` for any
weight function `wt'` on `Fin p × ι` with `wt' (k, i) = ν` whenever `wt i = μ`. -/
lemma inWt_bv {wt : ι → ℤ} {wt' : Fin p × ι → ℤ} {μ ν : ℤ} (k : ℕ)
    (hw : ∀ (j : Fin p) (i : ι), (j : ℕ) = k → wt i = μ → wt' (j, i) = ν) {n : ι → A}
    (hn : InWt wt μ n) : InWt wt' ν (bv p k n) := by
  intro ⟨j, i⟩ hji
  simp only [bv_apply]
  split_ifs with hj
  · exact hn i fun hi => hji (hw j i hj hi)
  · rfl

end slots

/-! ### Euclidean division by `p` -/

lemma div_mod_unique {p t c m : ℕ} (ht : t = p * c + m) (hm : m < p) : t / p = c ∧ t % p = m := by
  have hp : 0 < p := by omega
  subst ht
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hm, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

lemma eq_of_add_mul_eq {p k m a c : ℕ} (hk : k < p) (hm : m < p) (h : k + p * c = m + p * a) :
    k = m ∧ a = c := by
  rcases lt_trichotomy a c with h1 | h1 | h1
  · have : p * a + p ≤ p * c := by nlinarith
    omega
  · subst h1; omega
  · have : p * c + p ≤ p * a := by nlinarith
    omega

end ColouredSand.OddTwist
