module

public import RequestProject.OddDance.Rule
public import RequestProject.TiltDec.Rule

/-!
# `CSI6_the_dance_lattices.md`, Part K — agreement with stage 3 (CSG5)

Namespace `ColouredSand.OddTwist`. Reuses CSG3 `ColouredSand.TiltP.IsSimpleWt`, `rT`, `aT` and
CSG5 `ColouredSand.TiltDec.VdotP`, `LP`, `mP` (with `VdotP_zero`, `VdotP_simple_small`,
`VdotP_simple_large`, `VdotP_r_one`, `VdotP_r_mid`, `VdotP_r_top_pos`, `VdotP_r_top_ext`, `M3`).

Encodings: lists of weights are compared up to `List.Perm` (formal sums); the multiplicity of a
weight is `List.count`. The hypothesis "`p` an odd prime" is replaced by the weaker `3 ≤ p`
(every odd prime satisfies it), so the statements are slightly more general than in the file.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open ColouredSand.TiltP ColouredSand.TiltDec

section arith

variable {p l d b : ℕ}

/-- (K1), arithmetic: if `λ + 1 = d + p (b + 1)` with `1 ≤ d < p`, then `rT p λ = d`. -/
lemma rT_of_digits (hk : l + 1 = d + p * (b + 1)) (hd1 : 1 ≤ d) (hdp : d < p) : rT p l = d := by
  have h : l - p = (d - 1) + p * b := by rw [Nat.mul_succ] at hk; omega
  unfold rT
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- (K1), arithmetic: if `λ + 1 = d + p (b + 1)` with `1 ≤ d < p`, then `aT p λ = b`. -/
lemma aT_of_digits (hk : l + 1 = d + p * (b + 1)) (hd1 : 1 ≤ d) (hdp : d < p) : aT p l = b := by
  have h : l - p = (d - 1) + p * b := by rw [Nat.mul_succ] at hk; omega
  unfold aT
  rw [h, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]

/-- (K1), arithmetic: if `λ + 1 = d + p (b + 1)` with `1 ≤ d < p`, then `λ` is not simple. -/
lemma not_simple_of_digits (hk : l + 1 = d + p * (b + 1)) (hd1 : 1 ≤ d) (hdp : d < p) :
    ¬ IsSimpleWt p l := by
  have hpb : p ≤ p * (b + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rintro (h | ⟨hdv, -⟩)
  · omega
  · have : (l + 1) % p = d := by rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdp]
    rw [Nat.dvd_iff_mod_eq_zero] at hdv
    omega

end arith

/-- **(K1)** (Part K of `CSI6_the_dance_lattices.md`): for `λ ≤ p² + p − 2`, `VdotL p λ` is a
permutation of CSG5's `VdotP p λ` (stated for every `p ≥ 3`, in particular every odd prime). -/
theorem K1_perm {p : ℕ} (hp3 : 3 ≤ p) {l : ℕ} (hl : l ≤ p ^ 2 + p - 2) :
    (VdotL p l).Perm (VdotP p l) := by
  by_cases h0 : l = 0
  · subst h0; rw [VdotL_zero, VdotP_zero]
  by_cases h1 : l + 1 < p
  · rw [VdotL_small (by omega) (by omega),
      VdotP_simple_small (simple_of_le (by omega)) (by omega) (by omega)]
  have hl' : p - 1 ≤ l := by omega
  have hk := succ_eq_d0_b (by omega : 1 ≤ p) hl'
  have hdp : (l + 1) % p < p := Nat.mod_lt _ (by omega)
  have hpp : p ^ 2 = p * p := sq p
  have hbp : (l + 1) / p - 1 ≤ p - 1 := by
    have : (l + 1) / p < p + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
      rw [Nat.add_mul, one_mul]; omega)
    omega
  by_cases hd0 : (l + 1) % p = 0
  · rw [VdotL_d0_zero (by omega) hl' hd0]
    rw [VdotP_simple_large (by omega) ?_ hl']
    refine Or.inr ⟨Nat.dvd_of_mod_eq_zero hd0, ?_⟩
    have : p * ((l + 1) / p - 1 + 1) ≤ p * p := Nat.mul_le_mul_left _ (by omega)
    omega
  generalize hd : (l + 1) % p = d at *
  generalize hb : (l + 1) / p - 1 = b at *
  have hd1 : 1 ≤ d := by omega
  have hrT := rT_of_digits hk hd1 hdp
  have haT := aT_of_digits hk hd1 hdp
  have hns := not_simple_of_digits hk hd1 hdp
  by_cases hdo : d = 1
  · subst hdo
    rw [VdotL_d0_one (by omega) hl' hd, VdotP_r_one hns hrT]
  by_cases hdm : d ≤ p - 2
  · rw [VdotL_d0_mid hl' (by omega) (by omega), VdotP_r_mid hns (by omega) (by omega)]
  have hdt : d = p - 1 := by omega
  rw [VdotL_d0_top hp3 hl' (by omega), hb]
  have hpb : p * (b + 1) = p * b + p := Nat.mul_succ p b
  by_cases hb0 : b = 0
  · subst hb0
    rw [VdotL_zero, VdotP_r_top_ext hp3 hns (by omega) (Or.inl haT)]
    rw [show (List.map (fun b' => p * b' + p - 1) [1]) = [l + 1] by simp; omega]
    exact List.Perm.swap _ _ _
  by_cases hbm : b ≤ p - 2
  · rw [VdotL_small (by omega) hbm,
      VdotP_r_top_pos hp3 hns (by omega) (by omega) (by omega)]
    have hpb' : p * (b - 1) + p = p * b := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    have hpb1 : p ≤ p * b := Nat.le_mul_of_pos_right _ (by omega)
    rw [show (List.map (fun b' => p * b' + p - 1) [b + 1, b - 1]) =
      [l + 1, l - 2 * rT p l - 1] by simp; omega]
    exact List.Perm.swap _ _ _
  · have hbt : b = p - 1 := by omega
    subst hbt
    rw [VdotL_d0_zero (by omega) le_rfl (by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]),
      VdotP_r_top_ext hp3 hns (by omega) (Or.inr haT)]
    rw [show (List.map (fun b' => p * b' + p - 1) [p - 1 + 1]) = [l + 1] by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [Nat.sub_add_cancel (by omega)]
      rw [Nat.sub_add_cancel (by omega)] at hk
      omega]
    exact List.Perm.swap _ _ _

/-- **(K2)** (Part K of `CSI6_the_dance_lattices.md`): for `m ≤ p² + p − 1`, `LL p m` is a
permutation of CSG5's `LP p m` (for every `p ≥ 3`). -/
theorem K2_perm {p : ℕ} (hp3 : 3 ≤ p) {m : ℕ} (hm : m ≤ p ^ 2 + p - 1) :
    (LL p m).Perm (LP p m) := by
  induction m with
  | zero => exact List.Perm.refl _
  | succ m ih =>
    rw [LL_succ, LP_succ]
    refine ((ih (by omega)).flatMap_right _).trans (List.Perm.flatMap_left _ fun l hl => ?_)
    exact K1_perm hp3 (by have := (M3 (by omega) m l hl).1; omega)

/-- **(K2)** (Part K of `CSI6_the_dance_lattices.md`), multiplicities: for `m ≤ p² + p − 1`,
`n_λ(m) = (LL p m).count λ = mP p λ m` (CSG5's multiplicity). -/
theorem K2_count {p : ℕ} (hp3 : 3 ≤ p) {m : ℕ} (hm : m ≤ p ^ 2 + p - 1) (l : ℕ) :
    nL p l m = mP p l m :=
  (K2_perm hp3 hm).count_eq l

end ColouredSand.OddTwist
