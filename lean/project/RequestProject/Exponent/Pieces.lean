module

public import RequestProject.Exponent.Inverse
public import RequestProject.Exponent.Criterion
public import RequestProject.Exponent.Carries

/-!
# The exponent of the pieces `coker (q (c + H) + U)` over `ℤ_[p]`

This file is part of the proof of **(C4) Theorem C** of `CS4_theorem_C_exponent.md` (second and
fourth bullet points of its proof): it combines (C1) (`opM_invVec`) and (C2)
(`kills_coker_iff_integral'`) to decide which powers of `p` kill the `ℤ_[p]`-cokernel of
`M = q (c + H) + U` on `B_m(ℤ_[p])`.

## Encoding

* `B_m(ℤ_[p]) = Finset (Fin m) → ℤ_[p]`, `M = opM m ℤ_[p] q c` (from `RequestProject/Strings/`),
  and `coker M = B_m(ℤ_[p]) ⧸ range M`.
* "`p^n` kills `X`" is `∀ x : X, (p : ℤ_[p]) ^ n • x = 0`.

## Results

* `invCoeff_eq_inv_nat`: `(−1)^k k! ∏_{i=0}^{k} 1/(q (c+s+i)) = (−1)^k / (q^{k+1} L C(b, L))` with
  `L = k + 1`, `b = c + s + k`, using `b!/((a−1)!(b−a)!) = L C(b, L)` for `a = c + s`.
* `pow_mul_invCoeff_integral_iff`: `p^n (M^{−1})_{T,S}` is integral iff
  `e L + v_p(L) + v_p C(b, L) ≤ n`.
* `piece_kills_iff` (`c ≥ 1`): `p^n` kills `coker M` iff
  `e L + v_p(L) + v_p C(b, L) ≤ n` for all `L = k + 1`, `b = c + s + k` with `s + k ≤ m`.
* `piece_zero_kills_torsion` (`c = 0`): `p^n` kills the torsion of `coker M_0` as soon as the
  same bound holds for all `s ≥ 1`.  As in the file, the row of `∅` in `M_0` is zero, so a torsion
  class is represented by a vector supported on nonempty sets, and those are handled by the
  columns `w_S`, `S ≠ ∅`, of the inverse of `M_0` restricted to `B′ = ⊕_{s ≥ 1} B_m(s)`.
-/

@[expose] public section

open Finset ColouredSand.Strings

open scoped Nat

namespace ColouredSand.Exponent

variable {p : ℕ} [hp : Fact p.Prime]

/-- `(−1)^k k! ∏_{i=0}^{k} 1/(q (c+s+i)) = (−1)^k / (q^{k+1} (k+1) C(c+s+k, k+1))` when
`c + s ≥ 1`. -/
lemma invCoeff_eq_inv_nat {K : Type*} [Field K] [CharZero K] (q c s k : ℕ) (hcs : 1 ≤ c + s) :
    invCoeff (q : K) (c : K) s k =
      (-1) ^ k * (((q ^ (k + 1) * ((k + 1) * (c + s + k).choose (k + 1)) : ℕ) : K))⁻¹ := by
  obtain ⟨n, hn⟩ : ∃ n, c + s = n + 1 := ⟨c + s - 1, by omega⟩
  have hprod : ∏ i ∈ range (k + 1), ((q : K) * ((c : K) + ((s + i : ℕ) : K))) =
      ((q ^ (k + 1) * ((k + 1) * k ! * (c + s + k).choose (k + 1)) : ℕ) : K) := by
    rw [prod_mul_distrib, prod_const, card_range]
    have h1 : ∏ i ∈ range (k + 1), ((c : K) + ((s + i : ℕ) : K)) =
        (((c + s).ascFactorial (k + 1) : ℕ) : K) := by
      rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [h1, hn, Nat.ascFactorial_eq_factorial_mul_choose, Nat.factorial_succ,
      show n + (k + 1) = n + 1 + k by ring]
    push_cast; ring
  unfold invCoeff
  rw [prod_inv_distrib, hprod]
  have hk : (k ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast
  field_simp

lemma padic_valuation_neg_one_pow (k : ℕ) : ((-1 : ℚ_[p]) ^ k).valuation = 0 := by
  have h := Padic.valuation_mul (p := p) (x := -1) (y := -1) (by norm_num) (by norm_num)
  simp only [mul_neg, mul_one, neg_neg, Padic.valuation_one] at h
  rw [Padic.valuation_pow]
  have : (-1 : ℚ_[p]).valuation = 0 := by omega
  rw [this, mul_zero]

/-- **Valuation of an entry of `M^{−1}`.**  For `q ≠ 0` and `c + s ≥ 1`, with `L = k + 1` and
`b = c + s + k`, `p^n (−1)^k k! ∏_{i=0}^{k} 1/(q (c+s+i))` is integral iff
`e L + v_p(L) + v_p C(b, L) ≤ n`, where `e = v_p(q)`. -/
theorem pow_mul_invCoeff_integral_iff (n q c s k : ℕ) (hq : q ≠ 0) (hcs : 1 ≤ c + s) :
    (∃ r : ℤ_[p], (r : ℚ_[p]) = (p : ℚ_[p]) ^ n * invCoeff (q : ℚ_[p]) (c : ℚ_[p]) s k) ↔
      carryTerm p (padicValNat p q) (k + 1) (c + s + k) ≤ n := by
  rw [padic_pow_mul_integral_iff, invCoeff_eq_inv_nat q c s k hcs]
  set N := q ^ (k + 1) * ((k + 1) * (c + s + k).choose (k + 1)) with hN
  have hC : (c + s + k).choose (k + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hN0 : N ≠ 0 := by positivity
  have hN0' : ((N : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hN0
  have hx0 : (-1 : ℚ_[p]) ^ k * ((N : ℕ) : ℚ_[p])⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero hN0')
  rw [Padic.valuation_mul (pow_ne_zero _ (by norm_num)) (inv_ne_zero hN0'),
    padic_valuation_neg_one_pow, Padic.valuation_inv, Padic.valuation_natCast]
  have hvN : padicValNat p N = carryTerm p (padicValNat p q) (k + 1) (c + s + k) := by
    rw [hN, padicValNat.mul (by positivity) (by positivity), padicValNat.pow _ hq,
      padicValNat.mul (by omega) hC, carryTerm]
    ring
  rw [hvN]
  simp only [ne_eq, hx0, not_false_eq_true, forall_const, zero_add]
  omega

/-- `q (c + H) + U` over `ℚ_[p]` extends `q (c + H) + U` over `ℤ_[p]`. -/
lemma opM_padic_comp (m q c : ℕ) (f : B m ℤ_[p]) :
    opM m ℚ_[p] (q : ℚ_[p]) (c : ℚ_[p]) (fun i => algebraMap ℤ_[p] ℚ_[p] (f i)) =
      fun i => algebraMap ℤ_[p] ℚ_[p] (opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) (c : ℤ_[p]) f i) := by
  funext T
  simp only [opM_apply', map_add, map_mul, map_sum, map_natCast, Int.cast_natCast]

lemma opM_padic_ne_zero {q c : ℕ} (hq : q ≠ 0) {t : ℕ} (ht : 1 ≤ c + t) :
    (q : ℚ_[p]) * ((c : ℚ_[p]) + (t : ℚ_[p])) ≠ 0 := by
  have : q * (c + t) ≠ 0 := by positivity
  exact_mod_cast this

/-- The entries `invEntry` are integral after multiplication by `p^n` as soon as the
corresponding `carryTerm`s are at most `n`. -/
lemma invEntry_integral {m q c n : ℕ} (hq : q ≠ 0) (S : Finset (Fin m)) (hS : 1 ≤ c + S.card)
    (h : ∀ k, S.card + k ≤ m → carryTerm p (padicValNat p q) (k + 1) (c + S.card + k) ≤ n)
    (T : Finset (Fin m)) :
    ∃ r : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] r =
      algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n) * invVec (q : ℚ_[p]) (c : ℚ_[p]) S T := by
  rw [map_pow, map_natCast]
  simp only [invVec, invEntry]
  split_ifs with hST
  · have hcard : S.card + (T.card - S.card) ≤ m := by
      have := card_le_card hST
      have := card_le_univ T
      simp only [Fintype.card_fin] at this
      omega
    exact (pow_mul_invCoeff_integral_iff n q c S.card _ hq hS).mpr (h _ hcard)
  · exact ⟨0, by simp⟩

/-- **The pieces with `c ≥ 1`.**  For `q ≠ 0` and `c ≥ 1`, `p^n` kills `coker (q (c + H) + U)` on
`B_m(ℤ_[p])` iff `e L + v_p(L) + v_p C(b, L) ≤ n` for all `L = k + 1`, `b = c + s + k` with
`s + k ≤ m` (where `e = v_p(q)`).  This is (C1) + (C2) for these pieces. -/
theorem piece_kills_iff (m q c n : ℕ) (hq : q ≠ 0) (hc : 1 ≤ c) :
    (∀ x : B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) (c : ℤ_[p])),
        ((p : ℤ_[p]) ^ n) • x = 0) ↔
      ∀ s k : ℕ, s + k ≤ m → carryTerm p (padicValNat p q) (k + 1) (c + s + k) ≤ n := by
  have hw : ∀ S : Finset (Fin m),
      opM m ℚ_[p] (q : ℚ_[p]) (c : ℚ_[p]) (invVec (q : ℚ_[p]) (c : ℚ_[p]) S) = Pi.single S 1 :=
    fun S => opM_invVec _ _ S fun t _ _ => opM_padic_ne_zero hq (by omega)
  have hsurj : Function.Surjective (opM m ℚ_[p] (q : ℚ_[p]) (c : ℚ_[p])) := by
    intro f
    refine ⟨∑ S, f S • invVec (q : ℚ_[p]) (c : ℚ_[p]) S, ?_⟩
    rw [map_sum]
    simp_rw [map_smul, hw]
    conv_rhs => rw [← Finset.univ_sum_single f]
    refine sum_congr rfl fun S _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [kills_coker_iff_integral' (IsFractionRing.injective ℤ_[p] ℚ_[p]) _ _
    (opM_padic_comp m q c) (LinearMap.injective_iff_surjective.mpr hsurj) _ hw]
  constructor
  · intro h s k hsk
    obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin m)))
      (n := s + k) (by simpa using hsk)
    obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq (s := T) (n := s) (by omega)
    obtain ⟨r, hr⟩ := h T S
    rw [map_pow, map_natCast] at hr
    simp only [invVec, invEntry, if_pos hST, hT, hS, Nat.add_sub_cancel_left] at hr
    exact (pow_mul_invCoeff_integral_iff n q c s k hq (by omega)).mp ⟨r, hr⟩
  · intro h T S
    exact invEntry_integral hq S (by omega) (fun k hk => h _ _ hk) T

/-- **The piece with `c = 0`.**  For `q ≠ 0`, if `e L + v_p(L) + v_p C(b, L) ≤ n` for all
`L = k + 1`, `b = s + k` with `s ≥ 1` and `s + k ≤ m`, then `p^n` kills the torsion submodule of
`coker (q H + U)` on `B_m(ℤ_[p])`. -/
theorem piece_zero_kills_torsion (m q c n : ℕ) (hq : q ≠ 0) (hc : c = 0)
    (h : ∀ s k : ℕ, 1 ≤ s → s + k ≤ m → carryTerm p (padicValNat p q) (k + 1) (c + s + k) ≤ n) :
    ∀ x ∈ Submodule.torsion ℤ_[p]
      (B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) (c : ℤ_[p]))),
      ((p : ℤ_[p]) ^ n) • x = 0 := by
  subst hc
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  set MR := opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) ((0 : ℕ) : ℤ_[p])
  -- every `p^n e_S` with `S ≠ ∅` lies in the range
  have hS : ∀ S : Finset (Fin m), S ≠ ∅ →
      ((p : ℤ_[p]) ^ n) • (Pi.single S 1 : B m ℤ_[p]) ∈ LinearMap.range MR := by
    intro S hSne
    have hS1 : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
    exact smul_single_mem_range (IsFractionRing.injective ℤ_[p] ℚ_[p]) MR
      (opM m ℚ_[p] (q : ℚ_[p]) ((0 : ℕ) : ℚ_[p])) (opM_padic_comp m q 0)
      (opM_invVec _ _ S fun t ht _ => opM_padic_ne_zero hq (by omega))
      (invEntry_integral hq S (by omega) (fun k hk => h _ _ hS1 hk))
  obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff _).mp hx
  rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  obtain ⟨y, hy⟩ := hax
  -- the coefficient of `e_∅` vanishes
  have hf0 : f ∅ = 0 := by
    have := congrFun hy ∅
    rw [opM_apply'] at this
    simp only [card_empty, Nat.cast_zero, add_zero, mul_zero, zero_mul, sum_empty,
      Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (nonZeroDivisors.ne_zero ha)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hfsum : f = ∑ S, f S • (Pi.single S 1 : B m ℤ_[p]) := by
    conv_lhs => rw [← Finset.univ_sum_single f]
    refine sum_congr rfl fun S _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hfsum, smul_sum]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hSe : S = ∅
  · rw [hSe, hf0, zero_smul, smul_zero]
    exact Submodule.zero_mem _
  · rw [smul_comm]
    exact Submodule.smul_mem _ _ (hS S hSe)

end ColouredSand.Exponent
