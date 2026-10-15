module

public import RequestProject.OddSES.PartS5a

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S5) — `π_1 ∘ ι_2 = 0`

`ι_2 = iotaHom p N 1 _ _ : psi p N 2 → V ⊗ psi p N 1` and `π_1 = pi1Hom p N _ _`. As for
`π_r`, since `π_1` commutes with `F` it suffices that `π_1(α(n)) = 0` and `π_1(γ(n)) = 0`; these
follow from (S3), `κ` (CSI3 (B1)) and the operators of `twist p N` (CSI1 (B1)).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]} (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1)

lemma pi1_A0 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    (pi1Hom p N h1 h2).toLin (tv (ι := Bool × Fin p × N.ι) 0 (aV p j n)) =
      Sum.elim ((j : ℤ_[p]) • bv p (j - 1) n)
        ((2 : ℤ_[p]) • (twist p N).Ed 1 (bv p j n) -
          H (twist p N) ((j : ℤ_[p]) • bv p (j - 1) n)) :=
  (S3 p N h1 h2 (aV p j n) (bv p j n) ((j : ℤ_[p]) • bv p (j - 1) n)
    (by rw [kappa_aV hj, map_smul]; rfl)).1

lemma pi1_A1 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    (pi1Hom p N h1 h2).toLin (tv (ι := Bool × Fin p × N.ι) 1 (aV p j n)) =
      Sum.elim (-bv p j n)
        (-H (twist p N) (bv p j n) -
          (2 : ℤ_[p]) • (twist p N).Fd 1 ((j : ℤ_[p]) • bv p (j - 1) n)) :=
  (S3 p N h1 h2 (aV p j n) (bv p j n) ((j : ℤ_[p]) • bv p (j - 1) n)
    (by rw [kappa_aV hj, map_smul]; rfl)).2

lemma pi1_C0 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    (pi1Hom p N h1 h2).toLin (tv (ι := Bool × Fin p × N.ι) 0 (cV p j n)) =
      Sum.elim (bv p j n) ((2 : ℤ_[p]) • (twist p N).Ed 1 0 - H (twist p N) (bv p j n)) :=
  (S3 p N h1 h2 (cV p j n) 0 (bv p j n)
    (by rw [kappa_cV hj, map_zero, zero_add]; rfl)).1

lemma pi1_C1 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    (pi1Hom p N h1 h2).toLin (tv (ι := Bool × Fin p × N.ι) 1 (cV p j n)) =
      Sum.elim (-0) (-H (twist p N) 0 - (2 : ℤ_[p]) • (twist p N).Fd 1 (bv p j n)) :=
  (S3 p N h1 h2 (cV p j n) 0 (bv p j n)
    (by rw [kappa_cV hj, map_zero, zero_add]; rfl)).2

variable (hp3 : 3 ≤ p)
include hp3

/-- (S5) `π_1(α(n)) = 0`. -/
lemma pi1_alpha (n : N.ι → ℤ_[p]) :
    (pi1Hom p N h1 h2).toLin (alphaL p N 1 n) = 0 := by
  have hpos : 0 < p := by omega
  simp only [alphaL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    map_smul]
  rw [pi1_A0 h1 h2 hpos, pi1_C1 h1 h2 (by omega), (B1 p N).2.2.2.1,
    (B1 p N).1 _ _ (by omega), show p - (1 + 1) + 1 = p - 1 by omega]
  funext x
  cases x <;> simp
  split_ifs <;> ring

/-- (S5) `π_1(γ(n)) = 0`. -/
lemma pi1_gamma {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    (pi1Hom p N h1 h2).toLin (gammaL p N 1 w n) = 0 := by
  have hpos : 0 < p := by omega
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [pi1_C0 h1 h2 (by omega), pi1_A1 h1 h2 (by omega), pi1_C1 h1 h2 hpos,
    (B1 p N).2.2.2.2 1 w n hn, map_smul, (B1 p N).1 0 n (by omega)]
  funext x
  cases x with
  | inl x => simp
  | inr x =>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Sum.elim_inr, map_zero, smul_zero,
      neg_zero, zero_sub, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, Nat.cast_one, one_mul,
      zero_add]
    push_cast
    ring

/-- (S5) `π_1 ∘ ι_2 = 0`. -/
theorem pi1_comp_iota :
    (pi1Hom p N h1 h2).toLin ∘ₗ (iotaHom p N 1 le_rfl hp3).toLin = 0 := by
  have h2' : 1 ≤ p - 1 := by omega
  have hF : ∀ (k : ℕ) (z : Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]),
      (pi1Hom p N h1 h2).toLin ((ZF (psiD p N 1 le_rfl h2') ^ k) z) =
        ((Lemma35.dsum (twist p N) (twist p N)).Fd 1 ^ k) ((pi1Hom p N h1 h2).toLin z) :=
    fun k z => comp_pow_of_comm _ (ZF (psiD p N 1 le_rfl h2')) _
      ((pi1Hom p N h1 h2).comm_F 1) k z
  refine ext_single fun x => ?_
  obtain ⟨b, j, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  cases b
  · rw [single_false]
    change (pi1Hom p N h1 h2).toLin (iota (psiD p N 1 le_rfl h2')
      (aV p j (Pi.single i 1))) = 0
    rw [iota_aV _ j.isLt, hF, pi1_alpha h1 h2 hp3, map_zero]
  · rw [single_true]
    change (pi1Hom p N h1 h2).toLin (iota (psiD p N 1 le_rfl h2')
      (cV p j (Pi.single i 1))) = 0
    rw [iota_cV _ j.isLt hn, hF, pi1_gamma h1 h2 hp3 hn, map_zero]

end ColouredSand.OddTwist
