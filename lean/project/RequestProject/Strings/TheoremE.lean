module

public import RequestProject.Strings.StringCoker

/-!
# Theorem E (S5)

This file corresponds to **(S5) Theorem E (pieces with `m < p`)** of
`CS1_strings_and_theorem_E.md`.

## Encoding

* `B_m(ℤ_[p]) = Finset (Fin m) → ℤ_[p]`, `H`, `U` as in `RequestProject/Strings/Basic.lean`;
  the operator `M = q (c + H) + U` is written literally as
  `(q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p]`,
  so that `M e_S = q (c + |S|) e_S + U e_S`.
* `e = v_p(q)` is `padicValInt p q`, and `v_p(c + r)` is `padicValNat p (c + r)`.
* `coker M` is `B m ℤ_[p] ⧸ LinearMap.range M`; "`≅`" is the existence of a
  `ℤ_[p]`-linear equivalence.
* The free summand "`ℤ_[p]` if `c = 0`, else `0`" is `Fin (if c = 0 then 1 else 0) → ℤ_[p]`.
* The direct sum `⨁_{0 ≤ k ≤ m/2, (c,k) ≠ (0,0)} (ℤ_[p] ⧸ (p^{A_k}))^{C(m,k) − C(m,k−1)}` is the
  (finite) product over the index type
  `Σ k : {k : Fin (m / 2 + 1) // (c, k) ≠ (0, 0)}, Fin (strMult m k)`,
  where `strMult m k = C(m,k) − C(m,k−1)` (with `C(m,−1) = 0`) and `A_k = expA p q c m k`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Strings

/-- The exponent `A_k = ∑_{r=k}^{m−k} (e + v_p(c + r))`, `e = v_p(q)`, of Theorem E. -/
def expA (p : ℕ) (q : ℤ) (c m k : ℕ) : ℕ :=
  ∑ r ∈ Icc k (m - k), (padicValInt p q + padicValNat p (c + r))

section padic

variable {p : ℕ} [hp : Fact p.Prime]

lemma padicInt_isUnit_intCast {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : IsUnit (w : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra h
  push_neg at h
  exact hw ((PadicInt.norm_int_lt_one_iff_dvd w).mp h)

lemma padicInt_isUnit_natCast {n : ℕ} (h1 : 1 ≤ n) (h2 : n < p) : IsUnit (n : ℤ_[p]) := by
  have := padicInt_isUnit_intCast (p := p) (w := n) (by
    rw [Int.natCast_dvd_natCast]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega)
  simpa using this

lemma padicInt_associated_intCast {z : ℤ} (hz : z ≠ 0) :
    Associated (z : ℤ_[p]) ((p : ℤ_[p]) ^ padicValInt p z) := by
  obtain ⟨w, hw⟩ := padicValInt_dvd (p := p) z
  have hdvd := padicValInt_dvd_iff (p := p) (padicValInt p z + 1) z
  generalize padicValInt p z = v at hw hdvd ⊢
  have hndvd : ¬ (p : ℤ) ∣ w := by
    rintro ⟨u, rfl⟩
    rcases hdvd.mp ⟨u, hw.trans (by ring)⟩ with h | h
    · exact hz h
    · omega
  have hu := padicInt_isUnit_intCast hndvd
  have : (z : ℤ_[p]) = (p : ℤ_[p]) ^ v * (w : ℤ_[p]) := by rw [hw]; push_cast; ring
  rw [this]
  exact (associated_mul_unit_right _ _ hu).symm

lemma span_prod_eq (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m k : ℕ) (hk : 2 * k ≤ m)
    (hck : (c, k) ≠ (0, 0)) :
    Ideal.span {∏ i : Fin (m - 2 * k + 1), (q : ℤ_[p]) * ((c : ℤ_[p]) + ((k + i : ℕ) : ℤ_[p]))} =
      Ideal.span {(p : ℤ_[p]) ^ expA p q c m k} := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  rw [Ideal.span_singleton_eq_span_singleton]
  have hfac : ∀ i : Fin (m - 2 * k + 1),
      Associated ((q : ℤ_[p]) * ((c : ℤ_[p]) + ((k + i : ℕ) : ℤ_[p])))
        ((p : ℤ_[p]) ^ (padicValInt p q + padicValNat p (c + (k + i)))) := by
    intro i
    have hne : (c + (k + i) : ℕ) ≠ 0 := by
      intro h
      apply hck
      simp only [Prod.mk.injEq]
      omega
    have h := padicInt_associated_intCast (p := p) (z := q * ((c + (k + i) : ℕ) : ℤ))
      (mul_ne_zero hq0 (by exact_mod_cast hne))
    rw [padicValInt.mul hq0 (by exact_mod_cast hne), padicValInt.of_nat] at h
    convert h using 1
    push_cast
    ring
  have hsum : ∑ i : Fin (m - 2 * k + 1), (padicValInt p q + padicValNat p (c + (k + i))) =
      expA p q c m k := by
    rw [Fin.sum_univ_eq_sum_range (fun i => padicValInt p q + padicValNat p (c + (k + i))), expA,
      show Icc k (m - k) = Ico k (m - k + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show m - k + 1 - k = m - 2 * k + 1 by omega]
  refine (Associated.prod _ _ _ (fun i _ => hfac i)).trans ?_
  rw [prod_pow_eq_pow_sum, hsum]
  exact Associated.refl _

end padic

/-- Reindexing the strings with `(c, k) ≠ (0, 0)`. -/
def strIdxEquiv (c m : ℕ) :
    {t : StrIdx (fun k : Fin (m / 2 + 1) => strMult m k) //
        ¬ (c, ((t.1 : Fin (m / 2 + 1)) : ℕ)) = (0, 0)} ≃
      (Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) where
  toFun b := ⟨⟨b.1.1, b.2⟩, b.1.2⟩
  invFun t := ⟨⟨t.1.1, t.2⟩, t.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **(S5) Theorem E (pieces with `m < p`).**  Let `p` be a prime, `q ∈ ℤ` with
`e = v_p(q) ≥ 1`, `c ∈ ℕ` and `m < p`.  Let `M := q (c + H) + U` on `B_m(ℤ_[p])`.  Then
`coker M ≅ (ℤ_[p] if c = 0 else 0) ⊕ ⨁_{0 ≤ k ≤ m/2, (c,k) ≠ (0,0)}
(ℤ_[p] / (p^{A_k}))^{C(m,k) − C(m,k−1)}`, with `A_k = ∑_{r=k}^{m−k} (e + v_p(c + r))`.
See the module docstring for the encoding of the cokernel, of the free summand and of the direct
sum (a finite product indexed by `Σ k, Fin (C(m,k) − C(m,k−1))`). -/
theorem theorem_E (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m : ℕ)
    (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}))) := by
  classical
  have hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : ℤ_[p]) :=
    fun n h1 h2 => padicInt_isUnit_natCast h1 (by omega)
  let β : Fin (m / 2 + 1) → ℕ := fun k => strMult m k
  let bas : (k : Fin (m / 2 + 1)) → Module.Basis (Fin (β k)) ℤ_[p] (Lam m ℤ_[p] k) := fun k =>
    Module.finBasisOfFinrankEq ℤ_[p] (Lam m ℤ_[p] k)
      (Lam_free_finrank hR (by have := k.2; omega)).2
  obtain ⟨E1⟩ := coker_opM_equiv β bas hR (q : ℤ_[p]) (c : ℤ_[p])
  -- notation for the factors
  let d : StrIdx β → ℤ_[p] := fun t =>
    ∏ i : Fin (m - 2 * (t.1 : ℕ) + 1), (q : ℤ_[p]) * ((c : ℤ_[p]) + ((t.1 + i : ℕ) : ℤ_[p]))
  let X : StrIdx β → Type := fun t => ℤ_[p] ⧸ Ideal.span {d t}
  let Z : StrIdx β → Prop := fun t => (c, ((t.1 : Fin (m / 2 + 1)) : ℕ)) = (0, 0)
  -- splitting the index set
  let eS := Equiv.sumCompl Z
  let EA : ((t : StrIdx β) → X t) ≃ₗ[ℤ_[p]] ((s : {t // Z t} ⊕ {t // ¬ Z t}) → X (eS s)) :=
    (LinearEquiv.piCongrLeft ℤ_[p] X eS).symm
  let EB := LinearEquiv.sumPiEquivProdPi ℤ_[p] {t // Z t} {t // ¬ Z t} (fun s => X (eS s))
  -- the free part
  have hd0 : ∀ a : {t // Z t}, Ideal.span {d a.1} = ⊥ := by
    intro a
    rw [Ideal.span_singleton_eq_bot]
    have ha := a.2
    simp only [Z, Prod.mk.injEq] at ha
    refine prod_eq_zero (i := ⟨0, by omega⟩) (mem_univ _) ?_
    simp [ha.1, ha.2]
  let EF1 : ((a : {t // Z t}) → X a.1) ≃ₗ[ℤ_[p]] ({t // Z t} → ℤ_[p]) :=
    LinearEquiv.piCongrRight (fun a => Submodule.quotEquivOfEqBot _ (hd0 a))
  have hcard : Fintype.card (Fin (if c = 0 then 1 else 0)) = Fintype.card {t // Z t} := by
    rw [Fintype.card_fin]
    split_ifs with hc
    · symm
      rw [Fintype.card_eq_one_iff]
      have h1 : 0 < β ⟨0, by omega⟩ := by simp [β, strMult]
      refine ⟨⟨⟨⟨0, by omega⟩, ⟨0, h1⟩⟩, by simp [Z, hc]⟩, ?_⟩
      rintro ⟨⟨k, j⟩, hk⟩
      simp only [Z, Prod.mk.injEq, hc, true_and] at hk
      obtain rfl : k = ⟨0, Nat.succ_pos _⟩ := Fin.ext hk
      have hj : (j : ℕ) = 0 := by
        have := j.2
        simp only [β, strMult, Nat.choose_zero_right, if_true, Nat.sub_zero] at this
        omega
      congr
      exact Fin.ext hj
    · symm
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun a => ?_⟩
      have := a.2
      simp only [Z, Prod.mk.injEq] at this
      exact hc this.1
  let EF2 : ({t // Z t} → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin (if c = 0 then 1 else 0) → ℤ_[p]) :=
    LinearEquiv.funCongrLeft ℤ_[p] ℤ_[p] (Fintype.equivOfCardEq hcard)
  -- the torsion part
  have hdA : ∀ b : {t // ¬ Z t}, Ideal.span {d b.1} =
      Ideal.span {(p : ℤ_[p]) ^ expA p q c m b.1.1} := by
    intro b
    exact span_prod_eq q hq c m b.1.1 (by have := b.1.1.2; omega) b.2
  let ET1 : ((b : {t // ¬ Z t}) → X b.1) ≃ₗ[ℤ_[p]]
      ((b : {t // ¬ Z t}) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m b.1.1}) :=
    LinearEquiv.piCongrRight (fun b => Submodule.quotEquivOfEq _ _ (hdA b))
  let eT := strIdxEquiv c m
  let ET2 := LinearEquiv.piCongrLeft ℤ_[p]
    (fun t : (Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) =>
      ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}) eT
  exact ⟨E1.trans (EA.trans (EB.trans ((EF1.trans EF2).prodCongr (ET1.trans ET2))))⟩

end ColouredSand.Strings
