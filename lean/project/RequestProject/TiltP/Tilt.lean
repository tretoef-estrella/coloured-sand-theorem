module

public import RequestProject.TiltP.Tglue

/-!
# (T3) The tilting lattices `Ttilt p l` for `l ≤ p² + p − 1` (CSG3, Part T, (T3))

## Encoding

* `IsSimpleWt p l` ("`l` is simple"): `l ≤ p − 1`, or `p ∣ l + 1` and `l ≤ p² − 1`
  (natural-number subtraction, as in the file).
* `rT p l = (l − p) % p + 1` and `aT p l = (l − p) / p` (natural-number operations).
* `Ttilt p l = delta ℤ_[p] l` if `l` is simple, and `Tglue p (rT p l) (aT p l)` otherwise.
* `T3` is the arithmetic statement of (T3); `T3_simple_iff` is the parenthetical "also" of (T3).
  Both only use that `p ≥ 2` (they hold for every prime `p`, including `p = 2`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice ColouredSand.Blocks ColouredSand.Glue

/-- (T3) `l` is *simple*: `l ≤ p − 1`, or `p ∣ l + 1` and `l ≤ p² − 1`. -/
def IsSimpleWt (p l : ℕ) : Prop := l ≤ p - 1 ∨ (p ∣ l + 1 ∧ l ≤ p ^ 2 - 1)

/-- (T3) `r = (l − p) % p + 1`. -/
def rT (p l : ℕ) : ℕ := (l - p) % p + 1

/-- (T3) `a = (l − p) / p`. -/
def aT (p l : ℕ) : ℕ := (l - p) / p

open Classical in
/-- (T3) **The tilting lattice** `Ttilt p l`: `Δ(l)` if `l` is simple, and `Tglue p r a` with
`r = (l − p) % p + 1`, `a = (l − p) / p` otherwise. -/
def Ttilt (p : ℕ) [Fact p.Prime] (l : ℕ) : DPLattice ℤ_[p] :=
  if IsSimpleWt p l then delta ℤ_[p] l else Tglue p (rT p l) (aT p l)

/-- (T3) `Ttilt p l = Δ(l)` for simple `l`. -/
theorem Ttilt_of_simple (p : ℕ) [Fact p.Prime] {l : ℕ} (h : IsSimpleWt p l) :
    Ttilt p l = delta ℤ_[p] l := by
  classical
  unfold Ttilt; rw [if_pos h]

/-- (T3) `Ttilt p l = Tglue p r a` for non-simple `l`. -/
theorem Ttilt_of_not_simple (p : ℕ) [Fact p.Prime] {l : ℕ} (h : ¬ IsSimpleWt p l) :
    Ttilt p l = Tglue p (rT p l) (aT p l) := by
  classical
  unfold Ttilt; rw [if_neg h]

/-- Division with remainder, packaged: `l − p = p a + s` with `s < p`. -/
private lemma divmod_facts (p l : ℕ) (hp : 2 ≤ p) :
    p * aT p l + (rT p l - 1) = l - p ∧ rT p l - 1 < p ∧ 1 ≤ rT p l := by
  refine ⟨?_, ?_, ?_⟩
  · unfold aT rT; rw [Nat.add_sub_cancel]; exact Nat.div_add_mod _ _
  · unfold rT; rw [Nat.add_sub_cancel]; exact Nat.mod_lt _ (by omega)
  · unfold rT; omega

/-- **(T3)** If `l` is not simple and `l ≤ p² + p − 1`, then `l ≥ p`, `1 ≤ r ≤ p`, `a ≤ p − 1`,
`r = p → a = p − 1`, and `lam p r a = l`, where `r = (l − p) % p + 1`, `a = (l − p) / p`.
(Stated for every `p ≥ 2`.) -/
theorem T3 {p l : ℕ} (hp : 2 ≤ p) (hns : ¬ IsSimpleWt p l) (hl : l ≤ p ^ 2 + p - 1) :
    p ≤ l ∧ 1 ≤ rT p l ∧ rT p l ≤ p ∧ aT p l ≤ p - 1 ∧ (rT p l = p → aT p l = p - 1) ∧
      lam p (rT p l) (aT p l) = l := by
  obtain ⟨hd, hs, hr1⟩ := divmod_facts p l hp
  unfold IsSimpleWt at hns
  push_neg at hns
  have hpl : p ≤ l := by have := hns.1; omega
  have hsq : p ^ 2 = p * p := by ring
  rw [hsq] at hl hns
  have ha : aT p l ≤ p - 1 := by
    by_contra hcon
    have h1 : p * p ≤ p * aT p l := Nat.mul_le_mul_left p (by omega)
    generalize p * aT p l = X at *
    generalize p * p = P at *
    omega
  refine ⟨hpl, hr1, by omega, ha, ?_, ?_⟩
  · intro hrp
    have hdvd : p ∣ l + 1 := by
      have : l + 1 = p * (aT p l + 2) := by
        rw [Nat.mul_add]; omega
      rw [this]; exact dvd_mul_right _ _
    have hbig := hns.2 hdvd
    by_contra hcon
    have h1 : p * aT p l + p ≤ p * (p - 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left p (by omega)
    have h2 : p * (p - 1) + p = p * p := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    generalize p * aT p l = X at *
    generalize p * (p - 1) = Y at *
    generalize p * p = P at *
    omega
  · unfold lam
    generalize p * aT p l = X at *
    omega

/-- **(T3), "also"**: for `l ≤ p² + p − 1`, `l` is simple iff `l ≤ p − 1` or
(`r = p` and `a < p − 1`).  (Stated for every `p ≥ 2`.) -/
theorem T3_simple_iff {p l : ℕ} (hp : 2 ≤ p) (hl : l ≤ p ^ 2 + p - 1) :
    IsSimpleWt p l ↔ l ≤ p - 1 ∨ (rT p l = p ∧ aT p l < p - 1) := by
  obtain ⟨hd, hs, hr1⟩ := divmod_facts p l hp
  have hsq : p ^ 2 = p * p := by ring
  unfold IsSimpleWt
  rw [hsq] at hl ⊢
  have h2 : p * (p - 1) + p = p * p := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  constructor
  · rintro (h | ⟨hdvd, hle⟩)
    · exact Or.inl h
    · by_cases hlp : l ≤ p - 1
      · exact Or.inl hlp
      right
      have hl1 : l + 1 = p * (aT p l + 1) + rT p l := by rw [Nat.mul_add]; omega
      have hdvd' : p ∣ rT p l := by
        rw [hl1] at hdvd
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp hdvd
      have hrp : rT p l = p := le_antisymm (by omega) (Nat.le_of_dvd (by omega) hdvd')
      refine ⟨hrp, ?_⟩
      by_contra hcon
      have h1 : p * (p - 1) ≤ p * aT p l := Nat.mul_le_mul_left p (by omega)
      generalize p * aT p l = X at *
      generalize p * (p - 1) = Y at *
      generalize p * p = P at *
      omega
  · rintro (h | ⟨hrp, ha⟩)
    · exact Or.inl h
    · have hpl : p ≤ l := by
        by_contra hcon
        have : l - p = 0 := by omega
        rw [this] at hd
        have : aT p l = 0 ∨ p = 0 := by
          rcases Nat.eq_zero_of_add_eq_zero hd with ⟨h1, _⟩
          exact (Nat.mul_eq_zero.mp h1).symm
        omega
      right
      refine ⟨?_, ?_⟩
      · have : l + 1 = p * (aT p l + 2) := by rw [Nat.mul_add]; omega
        rw [this]; exact dvd_mul_right _ _
      · have h1 : p * aT p l + p ≤ p * (p - 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left p (by omega)
        generalize p * aT p l = X at *
        generalize p * (p - 1) = Y at *
        generalize p * p = P at *
        omega

end ColouredSand.TiltP
