module

public import RequestProject.TiltRules.Split

/-!
# Slices of the Weyl chains and small identities (auxiliary for `CSG4_tensor_rules.md`, §3)

* `slice0_AV`, `slice1_AV`, …: the two slots (`b_0`- and `b_1`-components) of the vectors
  `AV i`, `BV i`, `CV j`, `DV j` of `RequestProject/TiltRules/Weyl.lean`.
* `stilde_zero'`, `stilde_one'`: `s̃_0 = s_0 + x ℓ_r`, `s̃_1 = s_1 + x (r + 1) ℓ_{r+1}`.
* `norm_div_unit`, `norm_natCast_le`: norms in `ℚ_[p]`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

@[simp] lemma slice0_AV (i : ℕ) : slice 0 (AV p L M i) = ell p L M i := by
  unfold AV; split_ifs <;> simp

@[simp] lemma slice1_AV (i : ℕ) :
    slice 1 (AV p L M i) = if 1 ≤ i then ell p L M (i - 1) else 0 := by
  unfold AV; split_ifs <;> simp

@[simp] lemma slice0_BV (i : ℕ) :
    slice 0 (BV p L M i) = (-(((i : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1))) • ell p L M (i + 1) := by
  unfold BV; simp only [map_smul, map_sub, slice0_bvec1, slice_bvec_self, smul_zero, zero_sub,
    smul_neg, smul_smul]
  rw [← neg_smul]; congr 1; ring

@[simp] lemma slice1_BV (i : ℕ) :
    slice 1 (BV p L M i) = (((L : ℚ_[p]) - i) / ((L : ℚ_[p]) + 1)) • ell p L M i := by
  unfold BV; simp only [map_smul, map_sub, slice1_bvec0, slice_bvec_self, smul_zero, sub_zero,
    smul_smul]
  congr 1; ring

@[simp] lemma slice0_CV (j : ℕ) : slice 0 (CV p L M j) = ess p L M j := by
  unfold CV; split_ifs <;> simp

@[simp] lemma slice1_CV (j : ℕ) :
    slice 1 (CV p L M j) = if 1 ≤ j then ess p L M (j - 1) else 0 := by
  unfold CV; split_ifs <;> simp

@[simp] lemma slice0_DV (j : ℕ) :
    slice 0 (DV p L M j) = (-(((j : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) • ess p L M (j + 1) := by
  unfold DV; simp only [map_smul, map_sub, slice0_bvec1, slice_bvec_self, smul_zero, zero_sub,
    smul_neg, smul_smul]
  rw [← neg_smul]; congr 1; ring

@[simp] lemma slice1_DV (j : ℕ) :
    slice 1 (DV p L M j) = (((M : ℚ_[p]) - j) / ((M : ℚ_[p]) + 1)) • ess p L M j := by
  unfold DV; simp only [map_smul, map_sub, slice1_bvec0, slice_bvec_self, smul_zero, sub_zero,
    smul_smul]
  congr 1; ring

lemma stilde_zero' (r : ℕ) (x : ℚ_[p]) :
    stilde p L M r x 0 = ess p L M 0 + x • ell p L M r := by
  unfold stilde; rw [if_pos (Nat.zero_le _)]; simp

lemma stilde_one' (r : ℕ) (x : ℚ_[p]) (hM : 1 ≤ M) :
    stilde p L M r x 1 = ess p L M 1 + (x * ((r : ℚ_[p]) + 1)) • ell p L M (r + 1) := by
  unfold stilde; rw [if_pos hM, add_comm 1 r, Nat.choose_one_right]
  push_cast; rfl

lemma Sum_elim_eq {ι κ : Type*} (a : ι → ℚ_[p]) (b : κ → ℚ_[p]) :
    (Sum.elim a b : ι ⊕ κ → ℚ_[p]) = inlL a + inrL b := by
  funext y; rcases y with i | k <;> simp

lemma norm_div_unit {a c : ℚ_[p]} (hc : ‖c‖ = 1) : ‖a / c‖ = ‖a‖ := by
  rw [norm_div, hc, div_one]

lemma norm_natCast_le (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one ℚ_[p] n

lemma norm_mul_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

lemma norm_natCast_add_le (n : ℕ) (m : ℕ) : ‖(n : ℚ_[p]) + m‖ ≤ 1 := by
  rw [← Nat.cast_add]; exact norm_natCast_le _

end ColouredSand.TiltRules
