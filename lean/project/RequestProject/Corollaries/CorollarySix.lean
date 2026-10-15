module

public import RequestProject.Corollaries.JordanType
public import RequestProject.NumberOfFactors.TheoremD

/-!
# (Q4) Corollary 6: the number of cyclic factors of `Syl_3 K(H(d,q))` when `3 ∣ q`

This file corresponds to **(Q4) Corollary 6** of `CS6_corollaries_1_and_6.md`.

## Encoding

* `K(H(d,q)) = sandpile d q` is the torsion subgroup of `coker L = cokerL d q`
  (`RequestProject/TheoremB`), and `Syl_3 G` is `AddCommGroup.primaryComponent G 3`.
* The number of cyclic factors is
  `N = Module.finrank (ZMod 3) (ZMod 3 ⊗[ℤ] Syl_3 K(H(d,q)))`, exactly the left side of
  `ColouredSand.NumberOfFactors.theorem_D` at `p = 3` (Mathlib puts the `ZMod 3`-module
  structure on `ZMod 3 ⊗[ℤ] G`).
* The identity `6 N = 6 (q−1)^d + 2 (q^d − (q−1)^d) − ((q−1)^d − (q−3)^d) − 6` is stated in `ℤ`.
* `f(m)` is `fCoker m` of `RequestProject/Corollaries/JordanType.lean`.

## Proof

As in the file, **not** through Wilson's diagonal form (neither `theorem_D` nor the rank
formula `rank_U_zmod` of CS5 is used): `coker L ≅ ℤ ⊕ K` with `K` finite
(`cokerL_equiv_int_prod_sandpile`) and `𝔽_3 ⊗ K ≅ 𝔽_3 ⊗ Syl_3 K` (`tensorPrimaryEquiv`), so
`N + 1 = dim (𝔽_3 ⊗ coker L)`; Theorem A and right exactness, with `q (j+H) + U ≡ U` mod 3
(`tensorXqEquiv`), give `dim (𝔽_3 ⊗ coker L) = ∑_j C(d,j) (q−2)^j f(d−j)`
(`finrank_tensor_cokerL_three`); (Q3) gives `6 f(m) = 2·2^m + 3 + (−1)^m` (`six_fCoker`); and the
binomial theorem sums it up.

The statement holds for every `d ≥ 0` (the file assumes `d ≥ 1`); `q ≥ 3` and `3 ∣ q` are as
in the file.  `corollary6_q_three` gives `N = 3^{d−1} + 2^{d−1} − 1` for `q = 3`, `d ≥ 1`.
-/

@[expose] public section

open Finset Module TensorProduct

namespace ColouredSand.Corollaries

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB
  ColouredSand.NumberOfFactors

instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- `dim_{𝔽_3} (𝔽_3 ⊗ coker L) = ∑_{j=0}^{d} C(d,j) (q−2)^j f(d−j)` for `3 ∣ q`, `q ≥ 2`. -/
lemma finrank_tensor_cokerL_three {d q : ℕ} (hq : 2 ≤ q) (h3 : 3 ∣ q) :
    finrank (ZMod 3) (ZMod 3 ⊗[ℤ] cokerL d q) =
      ∑ j ∈ range (d + 1), d.choose j * (q - 2) ^ j * fCoker (d - j) := by
  obtain ⟨E⟩ := theorem_A d q hq
  let E1 := LinearEquiv.baseChange ℤ (ZMod 3) _ _ E
  let E2 := TensorProduct.piRight ℤ (ZMod 3) (ZMod 3)
    (fun σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) => Xq q (d - σ.1) σ.1)
  let E3 := LinearEquiv.piCongrRight
    fun σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) =>
      tensorXqEquiv 3 h3 (d - σ.1) σ.1
  rw [((E1.trans E2).trans E3).finrank_eq, Module.finrank_pi_fintype, Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun j => d.choose j * (q - 2) ^ j * fCoker (d - j)) (d + 1)

/-- `N + 1 = dim_{𝔽_3} (𝔽_3 ⊗ coker L)`, where `N = dim_{𝔽_3} (𝔽_3 ⊗ Syl_3 K)`. -/
lemma nFactors_add_one {d q : ℕ} (hq : 1 ≤ q) :
    finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) 3) + 1 =
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] cokerL d q) := by
  obtain ⟨⟨E⟩, hfin⟩ := cokerL_equiv_int_prod_sandpile d q hq
  haveI := hfin
  rw [(tensorPrimaryEquiv 3 (sandpile d q)).finrank_eq]
  let E1 := LinearEquiv.baseChange ℤ (ZMod 3) _ _ E
  let E2 := TensorProduct.prodRight ℤ (ZMod 3) (ZMod 3) ℤ (sandpile d q)
  haveI : Module.Finite ℤ (sandpile d q) := Module.Finite.of_finite
  have h1 : finrank (ZMod 3) (ZMod 3 ⊗[ℤ] ℤ) = 1 := by
    rw [Module.finrank_baseChange, Module.finrank_self]
  haveI : Module.Free (ZMod 3) (ZMod 3 ⊗[ℤ] sandpile d q) := Module.Free.of_divisionRing _ _
  haveI : Module.Free (ZMod 3) (ZMod 3 ⊗[ℤ] ℤ) := Module.Free.of_divisionRing _ _
  rw [(E1.trans E2).finrank_eq, Module.finrank_prod, h1]
  omega

/-- From (Q3): `6 f(m) = 2·2^m + 3 + (−1)^m`. -/
lemma six_fCoker (m : ℕ) : 6 * (fCoker m : ℤ) = 2 * 2 ^ m + 3 + (-1) ^ m := by
  have hf := fCoker_eq m
  rw [(rank_U_zmod_three m).1] at hf
  obtain ⟨-, h2, h3⟩ := jordanABC_closed m
  have hd := jordan_dim m
  have h4 := one_add_mod_two_le_two_pow m
  have key : 3 * fCoker m + m % 2 = 2 ^ m + 2 := by omega
  rcases Nat.even_or_odd m with he | ho
  · have : m % 2 = 0 := Nat.even_iff.mp he
    rw [this, add_zero] at key
    rw [he.neg_one_pow]
    have : (3 * fCoker m : ℤ) = 2 ^ m + 2 := by exact_mod_cast key
    linarith
  · have : m % 2 = 1 := Nat.odd_iff.mp ho
    rw [this] at key
    rw [ho.neg_one_pow]
    have : (3 * fCoker m + 1 : ℤ) = 2 ^ m + 2 := by exact_mod_cast key
    linarith

/-- The binomial sums: `6 ∑_j C(d,j) (q−2)^j f(d−j) = 2 q^d + 3 (q−1)^d + (q−3)^d`. -/
lemma six_sum_fCoker (d : ℕ) (x : ℤ) :
    6 * ∑ j ∈ range (d + 1), (d.choose j : ℤ) * x ^ j * (fCoker (d - j) : ℤ) =
      2 * (x + 2) ^ d + 3 * (x + 1) ^ d + (x + (-1)) ^ d := by
  rw [add_pow, add_pow, add_pow, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := six_fCoker (d - j)
  rw [one_pow]
  linear_combination ((d.choose j : ℤ) * x ^ j) * h

/-- **(Q4) Corollary 6.**  Let `q ≥ 3` with `3 ∣ q`, and `d ∈ ℕ` (the file assumes `d ≥ 1`; the
statement holds for all `d`).  The number of cyclic factors of `Syl_3 K(H(d,q))`,
`N = dim_{𝔽_3} (𝔽_3 ⊗ Syl_3 K(H(d,q)))`, satisfies, in `ℤ`,
`6 N = 6 (q−1)^d + 2 (q^d − (q−1)^d) − ((q−1)^d − (q−3)^d) − 6`. -/
theorem corollary6 (d q : ℕ) (hq : 3 ≤ q) (h3 : 3 ∣ q) :
    6 * (finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) 3) : ℤ) =
      6 * ((q : ℤ) - 1) ^ d + 2 * ((q : ℤ) ^ d - ((q : ℤ) - 1) ^ d) -
        (((q : ℤ) - 1) ^ d - ((q : ℤ) - 3) ^ d) - 6 := by
  have h1 := nFactors_add_one (d := d) (q := q) (by omega)
  rw [finrank_tensor_cokerL_three (by omega) h3] at h1
  have h2 : ((finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) 3) : ℤ)
      + 1) = ∑ j ∈ range (d + 1), (d.choose j : ℤ) * ((q : ℤ) - 2) ^ j * (fCoker (d - j) : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    push_cast [Nat.cast_sub (show 2 ≤ q by omega)] at this
    exact this
  have h4 := six_sum_fCoker d ((q : ℤ) - 2)
  rw [← h2] at h4
  have e1 : (q : ℤ) - 2 + 2 = q := by ring
  have e2 : (q : ℤ) - 2 + 1 = q - 1 := by ring
  have e3 : (q : ℤ) - 2 + -1 = q - 3 := by ring
  rw [e1, e2, e3] at h4
  linarith

lemma q_three_aux (N d : ℕ) (hd : 1 ≤ d)
    (h : 6 * (N : ℤ) = 6 * (((3 : ℕ) : ℤ) - 1) ^ d + 2 * (((3 : ℕ) : ℤ) ^ d - (((3 : ℕ) : ℤ) - 1) ^ d) -
      ((((3 : ℕ) : ℤ) - 1) ^ d - (((3 : ℕ) : ℤ) - 3) ^ d) - 6) :
    N = 3 ^ (d - 1) + 2 ^ (d - 1) - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h3 : 1 ≤ 3 ^ n + 2 ^ n := le_add_right (Nat.one_le_pow _ _ (by norm_num))
  push_cast at h
  rw [zero_pow (by omega), pow_succ, pow_succ] at h
  norm_num at h
  zify [h3]
  linarith

/-- **(Q4) for `q = 3`.**  For `d ≥ 1`, the number of cyclic factors of `Syl_3 K(H(d,3))` is
`N = 3^{d−1} + 2^{d−1} − 1`. -/
theorem corollary6_q_three (d : ℕ) (hd : 1 ≤ d) :
    finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d 3) 3) =
      3 ^ (d - 1) + 2 ^ (d - 1) - 1 :=
  q_three_aux _ d hd (corollary6 d 3 le_rfl dvd_rfl)

end ColouredSand.Corollaries
