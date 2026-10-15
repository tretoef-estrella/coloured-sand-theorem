module

public import RequestProject.OddSES.PartS4b

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S5) — `π_r ∘ ι_{r+1} = 0` for `2 ≤ r ≤ p − 2`

With `r = s + 1`: `ι_{r+1} = iotaHom p N (s+1) _ _ : psi p N (s+2) → V ⊗ psi p N (s+1)` and
`π_r = piHom p N s _ _ : V ⊗ psi p N (s+1) → psi p N s`. Since `ι(A_j n) = F^j α(n)` and
`ι(C_j n) = F^j γ(n)` (CSI3 `iota_aV`, `iota_cV`) and `π_r` commutes with `F`, it suffices that
`π_r(α(n)) = 0` (`pi_alpha`) and `π_r(γ(n)) = 0` (`pi_gamma`), which are direct computations with
the formula (S2) for `π_r` (`contr (b̂_0 ⊗ (b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1)) = y_1`, ...).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

section contrPsi

variable (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ p - 1) (m : Bool × Fin p × N.ι → ℤ_[p])

/-! The contraction on `V ⊗ (V ⊗ psi)`, with the vectors written with CSI3's index types. -/

lemma contrP00 : (contrHom (psi p N s h1 h2)).toLin
    (tv (ι := Fin 2 × (Bool × Fin p × N.ι)) 0 (tv (ι := Bool × Fin p × N.ι) 0 m)) = 0 :=
  contr_tv00 (psi p N s h1 h2) m

lemma contrP01 : (contrHom (psi p N s h1 h2)).toLin
    (tv (ι := Fin 2 × (Bool × Fin p × N.ι)) 0 (tv (ι := Bool × Fin p × N.ι) 1 m)) = m :=
  contr_tv01 (psi p N s h1 h2) m

lemma contrP10 : (contrHom (psi p N s h1 h2)).toLin
    (tv (ι := Fin 2 × (Bool × Fin p × N.ι)) 1 (tv (ι := Bool × Fin p × N.ι) 0 m)) = -m :=
  contr_tv10 (psi p N s h1 h2) m

lemma contrP11 : (contrHom (psi p N s h1 h2)).toLin
    (tv (ι := Fin 2 × (Bool × Fin p × N.ι)) 1 (tv (ι := Bool × Fin p × N.ι) 1 m)) = 0 :=
  contr_tv11 (psi p N s h1 h2) m

end contrPsi

variable (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)

lemma piHom_tv' (e : Fin 2) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    (piHom p N s hs1 hsp).toLin (tv (ι := Bool × Fin p × N.ι) e x) =
      (contrHom (psi p N s hs1 (by omega))).toLin
        (tv (ι := Fin 2 × (Bool × Fin p × N.ι)) e (iota (psiD p N s hs1 (by omega)) x)) :=
  piHom_tv s hs1 hsp e x

/-- (S5) `π_r(α(n)) = 0`, `r = s + 1`. -/
lemma pi_alpha {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    (piHom p N s hs1 hsp).toLin (alphaL p N (s + 1) n) = 0 := by
  have h2 : s ≤ p - 1 := by omega
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  simp only [alphaL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    map_smul]
  rw [piHom_tv', piHom_tv', iota_aV _ hpos, iota_cV _ (by omega) (inWt_E hn), pow_zero,
    Module.End.one_apply]
  simp only [alphaL, gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul, Zs_Fpow_tv0, Zs_Fpow_tv1, contrP00 s hs1 h2,
    contrP01 s hs1 h2, contrP10 s hs1 h2, contrP11 s hs1 h2]
  rw [psiF_pow_cV s (j := 1) (k := p - (s + 1 + 1)) (by omega),
    show 1 + (p - (s + 1 + 1)) = p - (s + 1) by omega]
  simp

/-- (S5) `π_r(γ(n)) = 0`, `r = s + 1`. -/
lemma pi_gamma {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    (piHom p N s hs1 hsp).toLin (gammaL p N (s + 1) w n) = 0 := by
  have h2 : s ≤ p - 1 := by omega
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [piHom_tv', piHom_tv', piHom_tv', iota_cV _ (by omega) hn, iota_aV _ (by omega),
    iota_cV _ hpos hn, pow_zero, Module.End.one_apply]
  simp only [alphaL, gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul, Zs_Fpow_tv0, Zs_Fpow_tv1, contrP00 s hs1 h2,
    contrP01 s hs1 h2, contrP10 s hs1 h2, contrP11 s hs1 h2]
  rw [psiF_pow_cV s (j := 1) (k := 0) (by omega), psiF_pow_aV s (j := 0) (k := s + 1) (by omega),
    psiF_pow_aV s (j := s) (k := 1) (by omega), psiF_pow_cV s (j := 0) (k := 1) (by omega)]
  simp only [Nat.cast_one, one_smul, smul_zero, sub_zero, zero_add, add_zero, smul_neg]
  rw [sub_neg_eq_add, Nat.cast_add, Nat.cast_one]
  module

/-- (S5) `π_r ∘ ι = 0` for CSI3's `ι = iota (psiD p N (s+1) _ _)` on `psi p N (s+2)`-coordinates
(the formula of `ι` makes sense for `s + 2 ≤ p`; it is `ι_{r+1}` for `s + 3 ≤ p` and, composed
with (P1), `ι_p` for `s + 2 = p`). -/
theorem pi_comp_iotaL :
    (piHom p N s hs1 hsp).toLin ∘ₗ iota (psiD p N (s + 1) (by omega) (by omega)) = 0 := by
  have h2 : s + 1 ≤ p - 1 := by omega
  have hF : ∀ (k : ℕ) (z : Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]),
      (piHom p N s hs1 hsp).toLin ((ZF (psiD p N (s + 1) (by omega) h2) ^ k) z) =
        ((psi p N s hs1 (by omega)).Fd 1 ^ k) ((piHom p N s hs1 hsp).toLin z) :=
    fun k z => comp_pow_of_comm _ (ZF (psiD p N (s + 1) (by omega) h2)) _
      ((piHom p N s hs1 hsp).comm_F 1) k z
  refine ext_single fun x => ?_
  obtain ⟨b, j, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  cases b
  · rw [single_false]
    change (piHom p N s hs1 hsp).toLin (iota (psiD p N (s + 1) (by omega) h2)
      (aV p j (Pi.single i 1))) = 0
    rw [iota_aV _ j.isLt, hF, pi_alpha s hs1 hsp hn, map_zero]
  · rw [single_true]
    change (piHom p N s hs1 hsp).toLin (iota (psiD p N (s + 1) (by omega) h2)
      (cV p j (Pi.single i 1))) = 0
    rw [iota_cV _ j.isLt hn, hF, pi_gamma s hs1 hsp hn, map_zero]

/-- (S5) `π_r ∘ ι_{r+1} = 0` for `r = s + 1`, `2 ≤ r ≤ p − 2`. -/
theorem pi_comp_iota (hsp3 : s + 3 ≤ p) :
    (piHom p N s hs1 hsp).toLin ∘ₗ (iotaHom p N (s + 1) (by omega) hsp3).toLin = 0 :=
  pi_comp_iotaL s hs1 hsp

end ColouredSand.OddTwist
