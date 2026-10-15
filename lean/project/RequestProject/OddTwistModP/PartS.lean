module

public import RequestProject.OddTwistModP.PartT

/-!
# `CSI2_reduction_mod_p.md`: Part S (the Steinberg lattice) and (C0) (Wilson)

Encodings:
* `φ : ℤ_[p] →+* B` is any ring homomorphism, `B` a commutative ring with `hp : (p : B) = 0`.
* `St φ` is `St = baseChange φ (delta ℤ_[p] (p − 1))` (C21's base change of C18's `Δ(p − 1)`):
  basis `Fin (p − 1 + 1)` (this is `Fin p`), basis vectors `e_s = Pi.single s 1`, weights
  `p − 1 − 2s`.
* `n!'` (the part of `n!` prime to `p`) is Mathlib's `ordCompl[p] n! = n! / p ^ v_p(n!)`, as in
  CSI1's definition of `qc`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

local notation:10000 n "!" => Nat.factorial n

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime]

/-! ### Part S -/

section St

variable (φ : ℤ_[p] →+* B)

/-- Part S: the Steinberg lattice `St := baseChange φ (delta ℤ_[p] (p − 1))` over `B`
(basis `Fin (p − 1 + 1)`, weights `p − 1 − 2s`). -/
abbrev St : DPLattice B := Twist.baseChange φ (delta ℤ_[p] (p - 1))

lemma St_Fd_single (t : ℕ) (j : Fin (p - 1 + 1)) :
    (St φ).Fd t (Pi.single j 1) = if h : (j : ℕ) + t ≤ p - 1 then
      (((j : ℕ) + t).choose t : B) •
        (Pi.single (⟨j + t, by omega⟩ : Fin (p - 1 + 1)) (1 : B) : Fin (p - 1 + 1) → B)
      else 0 := by
  show Twist.bc φ ((delta ℤ_[p] (p - 1)).Fd t) (Pi.single j 1) = _
  rw [← Twist.comp_single φ j, Twist.bc_apply_comp, delta_Fd_single]
  split_ifs
  · rw [Twist.comp_smul, map_natCast, Twist.comp_single]
  · exact Twist.comp_zero φ

lemma St_Ed_single (t : ℕ) (j : Fin (p - 1 + 1)) :
    (St φ).Ed t (Pi.single j 1) = if h : t ≤ (j : ℕ) then
      ((p - 1 - j + t).choose t : B) •
        (Pi.single (⟨j - t, by omega⟩ : Fin (p - 1 + 1)) (1 : B) : Fin (p - 1 + 1) → B)
      else 0 := by
  show Twist.bc φ ((delta ℤ_[p] (p - 1)).Ed t) (Pi.single j 1) = _
  rw [← Twist.comp_single φ j, Twist.bc_apply_comp, delta_Ed_single]
  split_ifs
  · rw [Twist.comp_smul, map_natCast, Twist.comp_single]
  · exact Twist.comp_zero φ

lemma St_Fd_high {r : ℕ} (hr : p ≤ r) : (St φ).Fd r = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ext_single fun (j : Fin (p - 1 + 1)) => ?_
  rw [St_Fd_single, dif_neg (show ¬ ((j : ℕ) + r ≤ p - 1) by omega)]; rfl

lemma St_Ed_high {r : ℕ} (hr : p ≤ r) : (St φ).Ed r = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ext_single fun (j : Fin (p - 1 + 1)) => ?_
  have := j.isLt
  rw [St_Ed_single, dif_neg (show ¬ (r ≤ (j : ℕ)) by omega)]; rfl

/-- (S1) On `St = baseChange φ (Δ(p − 1))`: basis `Fin (p − 1 + 1)`, weights `p − 1 − 2s`; for every
`0 ≤ j ≤ p − 1` and every `t` (more generally than `0 ≤ t ≤ p − 1`):
`F^{(t)} e_j = C(j + t, t) · e_{j+t}` if `j + t ≤ p − 1` and `0` otherwise;
`E^{(t)} e_j = C(p − 1 − j + t, t) · e_{j−t}` if `t ≤ j` and `0` otherwise;
and for `r ≥ p`, `F^{(r)} = E^{(r)} = 0` on `St`. -/
theorem oddModP_S1 :
    (St φ).ι = Fin (p - 1 + 1) ∧
    (∀ s : Fin (p - 1 + 1), (St φ).wt s = ((p - 1 : ℕ) : ℤ) - 2 * (s : ℤ)) ∧
    (∀ (j : Fin (p - 1 + 1)) (t : ℕ), (St φ).Fd t (Pi.single j 1) =
      if h : (j : ℕ) + t ≤ p - 1 then
        (((j : ℕ) + t).choose t : B) •
          (Pi.single (⟨j + t, by omega⟩ : Fin (p - 1 + 1)) (1 : B) : Fin (p - 1 + 1) → B)
      else 0) ∧
    (∀ (j : Fin (p - 1 + 1)) (t : ℕ), (St φ).Ed t (Pi.single j 1) =
      if h : t ≤ (j : ℕ) then
        ((p - 1 - j + t).choose t : B) •
          (Pi.single (⟨j - t, by omega⟩ : Fin (p - 1 + 1)) (1 : B) : Fin (p - 1 + 1) → B)
      else 0) ∧
    (∀ r : ℕ, p ≤ r → (St φ).Fd r = 0 ∧ (St φ).Ed r = 0) :=
  ⟨rfl, fun _ => rfl, fun j t => St_Fd_single φ t j, fun j t => St_Ed_single φ t j, fun _ hr => ⟨St_Fd_high φ hr, St_Ed_high φ hr⟩⟩

end St

/-! ### (C0) Wilson -/

section wilson

variable (hp : (p : B) = 0)

include hp in
/-- (C0, proof) Wilson's theorem in `B`: `(p − 1)! = −1`. -/
lemma wilson_B : (((p - 1)! : ℕ) : B) = -1 := by
  have h := ZMod.wilsons_lemma (p := p)
  have h2 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := natCast_eq_zero_of_dvd hp h2
  push_cast at this
  linear_combination this

omit [Fact p.Prime] in
lemma ordCompl_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : ordCompl[p] n = n := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

include hp in
lemma ordCompl_fact_add (c : ℕ) : ∀ t : ℕ, t ≤ p - 1 →
    ((ordCompl[p] (p * c + t)! : ℕ) : B) = ((ordCompl[p] (p * c)! : ℕ) : B) * ((t ! : ℕ) : B) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  intro t
  induction t with
  | zero => intro; simp
  | succ t ih =>
    intro ht
    rw [← add_assoc, Nat.factorial_succ, Nat.ordCompl_mul, ordCompl_of_not_dvd, Nat.cast_mul,
      ih (by omega), Nat.factorial_succ]
    · have : ((p * c + t + 1 : ℕ) : B) = ((t + 1 : ℕ) : B) := by
        push_cast; rw [hp]; ring
      rw [this]; push_cast; ring
    · intro hd
      have := (Nat.dvd_add_right (dvd_mul_right p c)).mp (by rwa [add_assoc] at hd)
      have := Nat.le_of_dvd (by omega) this
      omega

include hp in
lemma ordCompl_fact_mul (c : ℕ) :
    ((ordCompl[p] (p * c)! : ℕ) : B) = (-1) ^ c * ((ordCompl[p] c ! : ℕ) : B) := by
  have hpp : p.Prime := Fact.out
  have hp1 : 1 < p := hpp.one_lt
  induction c with
  | zero => simp
  | succ c ih =>
    have e : p * (c + 1) = (p * c + (p - 1)) + 1 := by rw [Nat.mul_succ]; omega
    rw [e, Nat.factorial_succ, Nat.ordCompl_mul, ← e, Nat.cast_mul, ordCompl_fact_add hp c _ le_rfl,
      ih, wilson_B hp, Nat.factorial_succ, Nat.ordCompl_mul (c + 1), Nat.cast_mul]
    have : ordCompl[p] (p * (c + 1)) = ordCompl[p] (c + 1) := by
      simpa using Nat.ordCompl_self_pow_mul (c + 1) 1 hpp
    rw [this]; ring

include hp in
/-- (C0, proof) `(pc + t)!' ≡ (−1)^c · c!' · t!` (modulo `p`, i.e. in `B`), for `t ≤ p − 1`,
where `n!' = n! / p^{v_p(n!)}`. -/
lemma ordCompl_fact (c t : ℕ) (ht : t ≤ p - 1) :
    ((ordCompl[p] (p * c + t)! : ℕ) : B) =
      (-1) ^ c * ((ordCompl[p] c ! : ℕ) : B) * ((t ! : ℕ) : B) := by
  rw [ordCompl_fact_add hp c t ht, ordCompl_fact_mul hp]

lemma factorization_fact (c t : ℕ) (ht : t ≤ p - 1) :
    ((p * c + t)!).factorization p = c + (c !).factorization p := by
  have hpp : p.Prime := Fact.out
  have hp1 : 1 < p := hpp.one_lt
  rw [Nat.factorization_def _ hpp, Nat.factorization_def _ hpp,
    padicValNat_factorial_mul_add c (by omega), padicValNat_factorial_mul]
  ring

variable (φ : ℤ_[p] →+* B)

include hp in
/-- (C0) Wilson. For `r = p·c + t` with `0 ≤ t ≤ p − 1`: `φ(q(c, r)) · t! = (−1)^c` (i.e.
`φ(q(c, r)) = (−1)^c (t!)⁻¹`, `t!` being a unit of `B`), and `φ(q(c', r)) = 0` for every
`c' ≥ c + 1`. -/
theorem C0 (c t : ℕ) (ht : t ≤ p - 1) :
    φ (qc p c (p * c + t)) * ((t ! : ℕ) : B) = (-1) ^ c ∧
    ∀ c' : ℕ, c + 1 ≤ c' → φ (qc p c' (p * c + t)) = 0 := by
  have hpp : p.Prime := Fact.out
  have hv := factorization_fact c t ht
  refine ⟨?_, fun c' hc' => ?_⟩
  · have hu := isUnit_ordCompl_factorial p (p * c + t)
    have h2 := congrArg φ (Ring.mul_inverse_cancel _ hu)
    rw [map_mul, map_one, map_natCast] at h2
    have h1 := ordCompl_fact hp c t ht
    have h3 : ((-1 : B) ^ c) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [qc, show c + (c !).factorization p - ((p * c + t)!).factorization p = 0 by omega,
      pow_zero, one_mul, map_mul, map_natCast]
    linear_combination (-1 : B) ^ c * h2 -
      (-1 : B) ^ c * φ (Ring.inverse ((ordCompl[p] (p * c + t)! : ℕ) : ℤ_[p])) * h1 -
      ((ordCompl[p] c ! : ℕ) : B) * φ (Ring.inverse ((ordCompl[p] (p * c + t)! : ℕ) : ℤ_[p])) *
        ((t ! : ℕ) : B) * h3
  · have hle : (c !).factorization p ≤ (c' !).factorization p :=
      (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)).mpr
        (Nat.factorial_dvd_factorial (by omega)) p
    obtain ⟨e, he⟩ : ∃ e, c' + (c' !).factorization p - ((p * c + t)!).factorization p = e + 1 :=
      ⟨c' + (c' !).factorization p - ((p * c + t)!).factorization p - 1, by omega⟩
    rw [qc, he, map_mul, map_mul, map_pow, map_natCast, hp, zero_pow (by omega), zero_mul,
      zero_mul]

end wilson

end ColouredSand.OddTwist
