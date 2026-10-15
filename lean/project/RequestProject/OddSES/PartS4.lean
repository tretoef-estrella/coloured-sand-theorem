module

public import RequestProject.OddSES.SESTools

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S4) — `π_r` and `π_1` are surjective

`π_r` (`piHom`) and `π_1` (`pi1Hom`) are `Hom`s by construction (composites of morphisms).
Surjectivity is proved modulo `p` and lifted by Nakayama (`surj_of_modP`):

* for `π_r`: `π_r(b̂_1 ⊗ A_j n) ≡ −A'_j n`, `π_r(b̂_1 ⊗ C_j n) ≡ −C'_{j+1} n` and
  `π_r(b̂_0 ⊗ C_0 n) ≡ A'_{r−1} n + r·C'_0 n` (CSI3's `iota_aV_modP`, `iota_cV_modP`), with `r` a
  unit;
* for `π_1` (exactly, via `κ`): `π_1(b̂_1 ⊗ C_{k−1} n) = (0, −2 b_k n)`,
  `π_1(b̂_0 ⊗ C_0 n) + π_1(b̂_1 ⊗ A_0 n) = (0, −2H b_0 n) ≡ (0, 2 b_0 n)` and
  `π_1(b̂_0 ⊗ C_j n) = (b_j n, −H b_j n)`; here `p ≠ 2` is used (`2` is a unit).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-- If `π v ≡ y` modulo `p`, then `y ∈ range π + p • _`. -/
lemma mem_range_sup_of_modP {X Y : DPLattice ℤ_[p]} (f : Hom X Y) (v : X.ι → ℤ_[p])
    {y : Y.ι → ℤ_[p]} (h : ModP p (f.toLin v) y) :
    y ∈ LinearMap.range f.toLin ⊔ pSub p (Y.ι → ℤ_[p]) :=
  ModP.mem_sup h.symm (Submodule.mem_sup_left ⟨v, rfl⟩)

lemma mem_of_unit_smul_mem {X : Type*} [AddCommGroup X] [Module ℤ_[p] X] {W : Submodule ℤ_[p] X}
    {c : ℤ_[p]} (hc : IsUnit c) {x : X} (h : c • x ∈ W) : x ∈ W := by
  obtain ⟨u, rfl⟩ := hc
  have := W.smul_mem (↑u⁻¹ : ℤ_[p]) h
  rwa [smul_smul, Units.inv_mul, one_smul] at this

section pir

variable (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)

lemma piHom_tv (e : Fin 2) (x : (psi p N (s + 1) (by omega) (by omega)).ι → ℤ_[p]) :
    (piHom p N s hs1 hsp).toLin (tv e x) =
      (contrHom (psi p N s hs1 (by omega))).toLin (tv e (iota (psiD p N s hs1 (by omega)) x)) := by
  simp only [piHom, WeylFilt.Hom.comp, LinearMap.comp_apply]
  rw [kronHom_id_tv]
  rfl

lemma piHom_tv_modP (e : Fin 2) (x : (psi p N (s + 1) (by omega) (by omega)).ι → ℤ_[p])
    (z : (Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))).ι → ℤ_[p])
    (h : ModP p (iota (psiD p N s hs1 (by omega)) x) z) :
    ModP p ((piHom p N s hs1 hsp).toLin (tv e x))
      ((contrHom (psi p N s hs1 (by omega))).toLin (tv e z)) := by
  rw [piHom_tv]
  exact h.map ((contrHom (psi p N s hs1 (by omega))).toLin ∘ₗ tv e)

/-- (S4) **`π_r` is surjective**, `r = s + 1`, `2 ≤ r ≤ p − 1`. -/
theorem S4_pi : Function.Surjective (piHom p N s hs1 hsp).toLin := by
  have h2 : s ≤ p - 1 := by omega
  apply surj_of_modP
  rintro ⟨b, j, i⟩
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  have hA : ∀ j : ℕ, j < p → aV p j (Pi.single i 1) ∈
      LinearMap.range (piHom p N s hs1 hsp).toLin ⊔
        pSub p ((psi p N s hs1 h2).ι → ℤ_[p]) := by
    intro j hj
    have h0 : ModP p (iota (psiD p N s hs1 h2) (aV p j (Pi.single i 1)))
        (tv (ι := (psi p N s hs1 h2).ι) 0 (aV p j (Pi.single i 1)) +
          (j : ℤ_[p]) • tv (ι := (psi p N s hs1 h2).ι) 1
            (aV p (j - 1) (Pi.single i 1))) :=
      iota_aV_modP (psiD p N s hs1 h2) hj (Pi.single i 1)
    have h := piHom_tv_modP s hs1 hsp 1 _ _ h0
    rw [map_add, map_smul, map_add, map_smul, contr_tv10, contr_tv11, smul_zero, add_zero] at h
    simpa using neg_mem (mem_range_sup_of_modP _ _ h)
  cases b
  · rw [single_false]; exact hA j j.isLt
  · rw [single_true]
    obtain ⟨j, hj⟩ := j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have h0 : ModP p (iota (psiD p N s hs1 h2) (cV p 0 (Pi.single i 1)))
          (tv (ι := (psi p N s hs1 h2).ι) 0 (cV p (0 + 1) (Pi.single i 1)) +
            ((0 : ℕ) : ℤ_[p]) • tv (ι := (psi p N s hs1 h2).ι) 1 (cV p 0 (Pi.single i 1)) +
            tv (ι := (psi p N s hs1 h2).ι) 1 (aV p (s + 0) (Pi.single i 1)) +
            ((s : ℤ_[p]) + 1) • tv (ι := (psi p N s hs1 h2).ι) 1
              (cV p 0 (Pi.single i 1))) :=
        iota_cV_modP (psiD p N s hs1 h2) (j := 0) (Fact.out : p.Prime).pos hn
      have h := piHom_tv_modP s hs1 hsp 0 _ _ h0
      simp only [map_add, map_smul, contr_tv00, contr_tv01] at h
      have h' := mem_range_sup_of_modP _ _ h
      have hsum := Submodule.sub_mem _ h' (hA (s + 0) (by omega))
      simp only [smul_zero, zero_add, Nat.cast_zero, zero_smul, add_sub_cancel_left] at hsum
      refine mem_of_unit_smul_mem (c := (s : ℤ_[p]) + 1) ?_ hsum
      have := isUnit_natCast_of_not_dvd p (n := s + 1)
        (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
      simpa using this
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have h0 : ModP p (iota (psiD p N s hs1 h2) (cV p k (Pi.single i 1)))
          (tv (ι := (psi p N s hs1 h2).ι) 0 (cV p (k + 1) (Pi.single i 1)) +
            (k : ℤ_[p]) • tv (ι := (psi p N s hs1 h2).ι) 1 (cV p k (Pi.single i 1)) +
            tv (ι := (psi p N s hs1 h2).ι) 1 (aV p (s + k) (Pi.single i 1)) +
            ((s : ℤ_[p]) + 1) • tv (ι := (psi p N s hs1 h2).ι) 1
              (cV p k (Pi.single i 1))) :=
        iota_cV_modP (psiD p N s hs1 h2) (j := k) (by omega) hn
      have h := piHom_tv_modP s hs1 hsp 1 _ _ h0
      simp only [map_add, map_smul, contr_tv10, contr_tv11, smul_zero, add_zero] at h
      simpa using neg_mem (mem_range_sup_of_modP _ _ h)

end pir

end ColouredSand.OddTwist
