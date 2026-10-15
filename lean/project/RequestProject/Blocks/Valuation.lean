module

public import RequestProject.Blocks.PChain
public import RequestProject.Blocks.TwoByTwo
public import RequestProject.Blocks.Defs

/-!
# Valuations of the relation coefficients (CSG1, §3 "Non-unit subdiagonal entries")

Bookkeeping for the elimination of §3 of `CSG1_lemma_8_the_blocks.md`: the coefficients produced
by contracting the unit links (`segCoef`, `segD`) and by the `ϖ`-chain lemma (`pcCoef`) are,
up to units, products of diagonal entries; over `ℤ_[p]` the product of the `N t` is
`p^{Σ v t}` up to a unit (preamble: "`v t` is the `p`-adic valuation of `N t`").
"Up to a unit" is Mathlib's `Associated`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Blocks

section general

variable {R : Type*} [CommRing R]

/-- Contracting the unit links multiplies by a product of diagonal entries, up to a unit. -/
lemma segCoef_associated {L : ℕ} {d s : ℕ → R} :
    ∀ j : ℕ, (∀ i < j, (i + 1) % L ≠ 0 → IsUnit (s i)) →
      Associated (segCoef L d s j) (∏ i ∈ Ico (j / L * L) j, d i) := by
  intro j
  induction j with
  | zero => intro _; simp [segCoef]
  | succ j ih =>
    intro hs
    by_cases hmod : (j + 1) % L = 0
    · have h1 : (j + 1) / L * L = j + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      rw [h1, segCoef, if_pos hmod]; simp
    · have hdiv : (j + 1) / L = j / L :=
        Nat.succ_div_of_not_dvd (fun h => hmod (Nat.mod_eq_zero_of_dvd h))
      have hle : j / L * L ≤ j := Nat.div_mul_le_self j L
      rw [hdiv, segCoef, if_neg hmod, Finset.prod_Ico_succ_top hle]
      have hu : IsUnit (-Ring.inverse (s j)) :=
        (Ring.inverse_unit (hs j (by omega) hmod).unit ▸ (Units.isUnit _)).neg
      have h2 : -d j * Ring.inverse (s j) * segCoef L d s j =
          segCoef L d s j * d j * (-Ring.inverse (s j)) := by ring
      rw [h2]
      exact (associated_mul_unit_left _ _ hu).trans
        ((ih (fun i hi => hs i (by omega))).mul_right _)

/-- The end-of-segment coefficient `segD` is the product of the diagonal over the segment, up to
a unit. -/
lemma segD_associated {n L : ℕ} (hL : 0 < L) {d s : ℕ → R}
    (hs : ∀ i < n, (i + 1) % L ≠ 0 → IsUnit (s i)) {t : ℕ} (ht : t ≤ n / L) :
    Associated (segD n L d s t) (∏ i ∈ Ico (t * L) (min (t * L + L - 1) n + 1), d i) := by
  have htL : t * L ≤ n := mul_le_of_le_div ht
  set e := min (t * L + L - 1) n with he
  have he1 : t * L ≤ e := by omega
  have he2 : e / L = t := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul]; omega)
  rw [segD, ← he, Finset.prod_Ico_succ_top he1]
  have := segCoef_associated (L := L) (d := d) (s := s) e (fun i hi h => hs i (by omega) h)
  rw [he2] at this
  rw [mul_comm]
  exact this.mul_right _

/-- The `ϖ`-chain coefficient: `ϖ^a κ_a` is `∏_{t<a} D t` up to a unit. -/
lemma pcCoef_associated (ϖ : R) {D P w : ℕ → R} :
    ∀ a : ℕ, (∀ t < a, D t = ϖ * P t) → (∀ t < a, IsUnit (w t)) →
      Associated (ϖ ^ a * pcCoef P w a) (∏ t ∈ range a, D t) := by
  intro a
  induction a with
  | zero => intro _ _; simp [pcCoef]
  | succ a ih =>
    intro hD hw
    rw [prod_range_succ, pcCoef, hD a (by omega)]
    have hu : IsUnit (-Ring.inverse (w a)) :=
      (Ring.inverse_unit (hw a (by omega)).unit ▸ (Units.isUnit _)).neg
    have h2 : ϖ ^ (a + 1) * (-P a * Ring.inverse (w a) * pcCoef P w a) =
        (ϖ ^ a * pcCoef P w a) * (ϖ * P a) * (-Ring.inverse (w a)) := by ring
    rw [h2]
    exact (associated_mul_unit_left _ _ hu).trans
      ((ih (fun t ht => hD t (by omega)) (fun t ht => hw t (by omega))).mul_right _)

/-- Regrouping a product over `[0, mL)` into `m` segments of length `L`. -/
lemma prod_segments {M : Type*} [CommMonoid M] (f : ℕ → M) (L : ℕ) :
    ∀ m : ℕ, ∏ t ∈ range m, ∏ i ∈ Ico (t * L) (t * L + L), f i = ∏ i ∈ range (m * L), f i := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih, Nat.add_mul, one_mul, prod_range_add,
      prod_Ico_eq_prod_range]
    congr 1
    rw [show m * L + L - m * L = L by omega]

end general

section padic

variable {p : ℕ} [hp : Fact p.Prime]

lemma isUnit_natCast_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 h

lemma isUnit_succ_of_lt {i : ℕ} (h : i + 1 < p) : IsUnit ((i : ℤ_[p]) + 1) := by
  have := isUnit_natCast_of_not_dvd (p := p) (n := i + 1)
    (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  simpa using this

/-- A nonzero natural number is `p^{v_p(n)}` up to a unit in `ℤ_[p]`. -/
lemma natCast_associated {n : ℕ} (hn : n ≠ 0) :
    Associated (n : ℤ_[p]) ((p : ℤ_[p]) ^ padicValNat p n) := by
  have h := Nat.ordProj_mul_ordCompl_eq_self n p
  rw [Nat.factorization_def n hp.out] at h
  have hu := isUnit_natCast_of_not_dvd (p := p) (Nat.not_dvd_ordCompl hp.out hn)
  rw [Nat.factorization_def n hp.out] at hu
  conv_lhs => rw [← h]
  push_cast
  exact associated_mul_unit_left _ _ hu

variable {q c k : ℕ}

omit hp in
lemma q_ne_zero (hq : 1 ≤ padicValNat p q) : q ≠ 0 := by
  rintro rfl; simp at hq

/-- `N t = p^{v t}` up to a unit, when `c + k + t ≥ 1`. -/
lemma Nt_associated (hq : 1 ≤ padicValNat p q) {t : ℕ} (ht : 1 ≤ c + k + t) :
    Associated (Nt p q c k t) ((p : ℤ_[p]) ^ vt p q c k t) := by
  have hq0 := q_ne_zero hq
  have h := natCast_associated (p := p) (n := q * (c + k + t))
    (Nat.mul_ne_zero hq0 (by omega))
  rwa [padicValNat.mul hq0 (by omega)] at h

lemma p_dvd_Nt (hq : 1 ≤ padicValNat p q) (t : ℕ) : (p : ℤ_[p]) ∣ Nt p q c k t := by
  unfold Nt
  exact Nat.cast_dvd_cast (Nat.dvd_trans (dvd_of_one_le_padicValNat hq) (dvd_mul_right _ _))

lemma Nt_zero_of (hc : c = 0) (hk : k = 0) : Nt p q c k 0 = 0 := by
  subst hc hk; simp [Nt]

/-- `∏_{t ∈ s} N t = p^{Σ_{t∈s} v t}` up to a unit, when `c + k ≥ 1`. -/
lemma prod_Nt_associated (hq : 1 ≤ padicValNat p q) (hck : 1 ≤ c + k) (s : Finset ℕ) :
    Associated (∏ t ∈ s, Nt p q c k t) ((p : ℤ_[p]) ^ ∑ t ∈ s, vt p q c k t) := by
  rw [← prod_pow_eq_pow_sum]
  exact Associated.prod _ _ _ (fun t _ => Nt_associated hq (by omega))

/-- `ℤ_[p] ⧸ (x) ≃+ ZMod (p^E)` when `x = p^E` up to a unit. -/
noncomputable def quotAssocEquiv {x : ℤ_[p]} {E : ℕ} (h : Associated x ((p : ℤ_[p]) ^ E)) :
    (ℤ_[p] ⧸ (Ideal.span {x} : Submodule ℤ_[p] ℤ_[p])) ≃+ ZMod (p ^ E) :=
  (Submodule.quotEquivOfEq _ _ (Ideal.span_singleton_eq_span_singleton.2 h)).toAddEquiv.trans
    (padicQuotEquiv E)

/-- `ℤ_[p] ⧸ (0) ≃+ ℤ_[p]`. -/
noncomputable def quotZeroEquiv :
    (ℤ_[p] ⧸ (Ideal.span {(0 : ℤ_[p])} : Submodule ℤ_[p] ℤ_[p])) ≃+ ℤ_[p] :=
  ((Submodule.quotEquivOfEq _ ⊥ (by simp)).trans (Submodule.quotEquivOfEqBot ⊥ rfl)).toAddEquiv

/-- `(ℤ_[p])^a ⧸ (p)^a ≃+ (ZMod p)^a`. -/
noncomputable def piSpanEquiv (a : ℕ) :
    ((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p])) ≃+ (Fin a → ZMod p) :=
  (Submodule.quotientPi (fun _ : Fin a => (Ideal.span {(p : ℤ_[p])} : Submodule ℤ_[p] ℤ_[p]))
    ).toAddEquiv.trans
    (AddEquiv.piCongrRight (fun _ => (Submodule.quotEquivOfEq _ _ (by rw [pow_one])).toAddEquiv.trans
      ((padicQuotEquiv 1).trans (by rw [pow_one]))))

end padic

end ColouredSand.Blocks
