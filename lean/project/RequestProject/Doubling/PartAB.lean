module

public import RequestProject.Doubling.PhiOps

/-!
# `C20_the_doubling_functor.md`: Part A (A1) and Part B

`phi N : DPLattice A` is `Φ(N)` (basis `Fin 2 × N.ι`, weights `phiWt N`, divided powers `phiFd N`,
`phiEd N` given by the closed formulas of the Setting). A vector `n` "of weight `w`" of `N` is
encoded by C18's `InWt N.wt w n` (all coordinates outside the weight `w` vanish).
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset Polynomial

variable {A : Type*} [CommRing A] (N : DPLattice A)

lemma fin_two_cases (e : Fin 2) : e = 0 ∨ e = 1 := by fin_cases e <;> simp

/-! ### The single operators -/

lemma F1_b0 (n : N.ι → A) : phiFd N 1 (bvec 0 n) = bvec 1 n := by
  have h := phiFdL_odd0 N 0 n
  simp only [Nat.mul_zero, zero_add, dfi_one, one_smul, N.isDP.P0_F, Module.End.one_apply] at h
  rw [phiFd_bvec, h]

lemma F1_b1 (n : N.ι → A) : phiFd N 1 (bvec 1 n) = (2 : A) • bvec 0 (N.Fd 1 n) := by
  have h := phiFdL_odd1 N 0 n
  simp only [Nat.mul_zero, zero_add, dfi_one, mul_one] at h
  rw [phiFd_bvec, h]; norm_num

lemma E1_b0 (n : N.ι → A) : phiEd N 1 (bvec 0 n) = (2 : A) • bvec 1 (N.Ed 1 n) := by
  have : phiEd N 1 ∘ₗ bvec 0 = (2 : A) • (bvec 1 ∘ₗ N.Ed 1) := by
    refine ext_single fun i => ?_
    rw [LinearMap.comp_apply, ← single_eq_bvec, phiEd_single, phiEdB]
    have h := phiEdL_odd0 N 0 (N.wt i) (Pi.single i 1)
    simp only [Nat.mul_zero, zero_add, dfi_one, mul_one] at h
    rw [h]
    simp [piOp]
  exact LinearMap.congr_fun this n

lemma E1_b1 {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    phiEd N 1 (bvec 1 x) = bvec 0 (aeval (N.Fd 1 * N.Ed 1) (4 * X + C ((2 * μ + 1 : ℤ) : A)) x) := by
  have h := phiEdL_odd1 N 0 μ x
  simp only [Nat.mul_zero, zero_add, dfi_one, one_smul, N.isDP.P0_E, Module.End.one_apply] at h
  rw [phiEd_bvec_of_inWt N 1 1 hx, h, piOp, range_one, prod_singleton]
  congr 5
  simp [cE]; ring

lemma E1_b1' {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    phiEd N 1 (bvec 1 x) = bvec 0 ((4 : A) • N.Fd 1 (N.Ed 1 x) + ((2 * μ + 1 : ℤ) : A) • x) := by
  rw [E1_b1 N hx, aeval_lin_apply]

/-! ### The recursions of the divided powers on `Φ(N)` -/

section rec

variable [OddUnits A]

/-- (B2, proof) `F^{(1)} F^{(r)} = (r+1) F^{(r+1)}` on `Φ(N)`. -/
theorem phi_rec_F (r : ℕ) (x : Fin 2 × N.ι → A) :
    phiFd N 1 (phiFd N r x) = ((r : A) + 1) • phiFd N (r + 1) x := by
  have : phiFd N 1 ∘ₗ phiFd N r = ((r : A) + 1) • phiFd N (r + 1) := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    rw [LinearMap.comp_apply, LinearMap.smul_apply, single_eq_bvec]
    have hd := odd_mul_dfi_succ (A := A)
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rcases fin_two_cases e with rfl | rfl
      · rw [phiFd_bvec, phiFdL_even, map_smul, F1_b0, phiFd_bvec, phiFdL_odd0, smul_smul]
        congr 1
        have := hd s; push_cast at this ⊢
        linear_combination (-1 : A) * this
      · rw [phiFd_bvec, phiFdL_even, map_smul, F1_b1, dp_rec_F, phiFd_bvec, phiFdL_odd1]
        simp only [map_smul, smul_smul]
        congr 1
        have := hd s; push_cast at this ⊢
        linear_combination (-(2 * (s : A) + 2)) * this
    · rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring]
      rcases fin_two_cases e with rfl | rfl
      · rw [phiFd_bvec, phiFdL_odd0, map_smul, F1_b1, dp_rec_F, phiFd_bvec, phiFdL_even]
        simp only [map_smul, smul_smul]
        congr 1
        push_cast; ring
      · rw [phiFd_bvec, phiFdL_odd1, map_smul, F1_b0, phiFd_bvec, phiFdL_even]
        simp only [smul_smul]
        congr 1
        push_cast; ring
  exact LinearMap.congr_fun this x

/-- (B2, proof) `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` on `Φ(N)`. -/
theorem phi_rec_E (r : ℕ) (x : Fin 2 × N.ι → A) :
    phiEd N 1 (phiEd N r x) = ((r : A) + 1) • phiEd N (r + 1) x := by
  have : phiEd N 1 ∘ₗ phiEd N r = ((r : A) + 1) • phiEd N (r + 1) := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    rw [LinearMap.comp_apply, LinearMap.smul_apply, single_eq_bvec]
    have hd := odd_mul_dfi_succ (A := A)
    have hδ := inWt_single (A := A) N.wt i
    set w := N.wt i with hw
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rcases fin_two_cases e with rfl | rfl
      · -- `r = 2s`, `b_0`
        rw [phiEd_bvec_of_inWt N _ 0 hδ, phiEd_bvec_of_inWt N _ 0 hδ, phiEdL_even0, phiEdL_odd0,
          map_smul, E1_b0, Ed_piOp N _ _ (N.isDP.inWt_Ed s hδ), dp_rec_E]
        have hc : (fun j => 4 * (w + 2 * (s : ℕ) + 2) + cE w s j) = cE w (s + 1) := by
          funext j; simp only [cE]; push_cast; ring
        rw [hc]
        simp only [map_smul, smul_smul]
        congr 1
        have := hd s; push_cast at this ⊢
        linear_combination (-(2 * (s : A) + 2)) * this
      · -- `r = 2s`, `b_1`
        rw [phiEd_bvec_of_inWt N _ 1 hδ, phiEd_bvec_of_inWt N _ 1 hδ, phiEdL_even1, phiEdL_odd1,
          map_smul, E1_b1 N (inWt_piOp N _ _ (N.isDP.inWt_Ed s hδ)),
          aeval_piOp_range N s _ _ (by simp only [cE]; ring)]
        simp only [smul_smul]
        congr 1
        have := hd s; push_cast at this ⊢
        linear_combination (-1 : A) * this
    · rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring]
      rcases fin_two_cases e with rfl | rfl
      · -- `r = 2s + 1`, `b_0`
        rw [phiEd_bvec_of_inWt N _ 0 hδ, phiEd_bvec_of_inWt N _ 0 hδ, phiEdL_odd0, phiEdL_even0,
          map_smul, E1_b1 N (inWt_piOp N _ _ (N.isDP.inWt_Ed (s + 1) hδ)),
          aeval_piOp_Icc N s _ _ (by simp only [cE]; push_cast; ring)]
        simp only [smul_smul]
        congr 1
        push_cast; ring
      · -- `r = 2s + 1`, `b_1`
        rw [phiEd_bvec_of_inWt N _ 1 hδ, phiEd_bvec_of_inWt N _ 1 hδ, phiEdL_odd1, phiEdL_even1,
          map_smul, E1_b0, Ed_piOp N _ _ (N.isDP.inWt_Ed s hδ), dp_rec_E]
        have hc : (fun j => 4 * (w + 2 * (s : ℕ) + 2) + cE w s j) = cE w (s + 1) := by
          funext j; simp only [cE]; push_cast; ring
        rw [hc]
        simp only [map_smul, smul_smul]
        congr 1
        push_cast; ring
  exact LinearMap.congr_fun this x

end rec

/-- (A1, proof) The Lie relation `[E, F] = H` on `Φ(N)`. -/
theorem phi_lie (x : Fin 2 × N.ι → A) :
    phiEd N 1 (phiFd N 1 x) = phiFd N 1 (phiEd N 1 x) + Hop (phiWt N) x := by
  have : phiEd N 1 ∘ₗ phiFd N 1 = phiFd N 1 ∘ₗ phiEd N 1 + Hop (phiWt N) := by
    refine ext_single fun p => ?_
    obtain ⟨e, i⟩ := p
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [single_eq_bvec]
    have hδ := inWt_single (A := A) N.wt i
    rcases fin_two_cases e with rfl | rfl
    · rw [F1_b0, E1_b1' N hδ, E1_b0, map_smul, F1_b1, Hop_of_inWt (inWt_bvec N 0 hδ)]
      simp only [map_add, map_smul, smul_smul, wtV_zero]
      push_cast; module
    · rw [F1_b1, map_smul, E1_b0, dp_lie, E1_b1' N hδ, F1_b0, Hop_of_inWt (inWt_bvec N 1 hδ)]
      dsimp only [H]
      rw [Hop_of_inWt hδ]
      simp only [map_add, map_smul, smul_smul, wtV_one]
      push_cast; module
  exact LinearMap.congr_fun this x

/-! ### (W) and (P0) on `Φ(N)` -/

lemma phi_W_F (p : Fin 2 × N.ι) (r : ℕ) (j : Fin 2 × N.ι)
    (hj : phiWt N j ≠ phiWt N p - 2 * r) : phiFd N r (Pi.single p 1) j = 0 := by
  obtain ⟨e, i⟩ := p
  have hδ := inWt_single (A := A) N.wt i
  have key : InWt (phiWt N) (phiWt N (e, i) - 2 * r) (phiFd N r (Pi.single (e, i) 1)) := by
    rw [single_eq_bvec, phiFd_bvec]
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rw [phiFdL_even]
      exact inWt_smul _ (inWt_congr (by simp only [phiWt]; push_cast; ring)
        (inWt_bvec N e (N.isDP.inWt_Fd s hδ)))
    · rcases fin_two_cases e with rfl | rfl
      · rw [phiFdL_odd0]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_zero, wtV_one]; push_cast; ring)
          (inWt_bvec N 1 (N.isDP.inWt_Fd s hδ)))
      · rw [phiFdL_odd1]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_zero, wtV_one]; push_cast; ring)
          (inWt_bvec N 0 (N.isDP.inWt_Fd (s + 1) hδ)))
  exact key j hj

lemma phi_W_E (p : Fin 2 × N.ι) (r : ℕ) (j : Fin 2 × N.ι)
    (hj : phiWt N j ≠ phiWt N p + 2 * r) : phiEd N r (Pi.single p 1) j = 0 := by
  obtain ⟨e, i⟩ := p
  have hδ := inWt_single (A := A) N.wt i
  have key : InWt (phiWt N) (phiWt N (e, i) + 2 * r) (phiEd N r (Pi.single (e, i) 1)) := by
    rw [phiEd_single, phiEdB]
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rcases fin_two_cases e with rfl | rfl
      · rw [phiEdL_even0]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_zero]; push_cast; ring)
          (inWt_bvec N 0 (inWt_piOp N _ _ (N.isDP.inWt_Ed s hδ))))
      · rw [phiEdL_even1]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_one]; push_cast; ring)
          (inWt_bvec N 1 (inWt_piOp N _ _ (N.isDP.inWt_Ed s hδ))))
    · rcases fin_two_cases e with rfl | rfl
      · rw [phiEdL_odd0]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_zero, wtV_one]; push_cast; ring)
          (inWt_bvec N 1 (inWt_piOp N _ _ (N.isDP.inWt_Ed (s + 1) hδ))))
      · rw [phiEdL_odd1]
        exact inWt_smul _ (inWt_congr (by simp only [phiWt, wtV_zero, wtV_one]; push_cast; ring)
          (inWt_bvec N 0 (inWt_piOp N _ _ (N.isDP.inWt_Ed s hδ))))
  exact key j hj

lemma phi_P0_F : phiFd N 0 = 1 := by
  refine ext_single fun p => ?_
  obtain ⟨e, i⟩ := p
  rw [single_eq_bvec, phiFd_bvec]
  have h := phiFdL_even N 0 e (Pi.single i 1)
  simp only [Nat.mul_zero, dfi_zero, one_smul, N.isDP.P0_F, Module.End.one_apply] at h
  rw [h]; rfl

lemma phi_P0_E : phiEd N 0 = 1 := by
  refine ext_single fun p => ?_
  obtain ⟨e, i⟩ := p
  rw [phiEd_single, phiEdB, single_eq_bvec]
  rcases fin_two_cases e with rfl | rfl
  · have h := phiEdL_even0 N 0 (N.wt i) (Pi.single i 1)
    simp only [Nat.mul_zero, dfi_zero, one_smul, N.isDP.P0_E, Module.End.one_apply] at h
    rw [h]; simp [piOp]
  · have h := phiEdL_even1 N 0 (N.wt i) (Pi.single i 1)
    simp only [Nat.mul_zero, dfi_zero, one_smul, N.isDP.P0_E, Module.End.one_apply] at h
    rw [h]; simp [piOp]

/-! ### `Φ(N)` -/

section phi

variable [IsDomain A] [CharZero A] [OddUnits A]

omit [IsDomain A] [CharZero A] in
lemma phi_recData : RecData (phiWt N) (phiFd N) (phiEd N) :=
  ⟨phi_W_F N, phi_W_E N, phi_P0_F N, phi_P0_E N, phi_rec_F N, phi_rec_E N, phi_lie N⟩

/-- (A1) `Φ(N)` as a DP-lattice: basis `Fin 2 × N.ι`, weights `wt(0,i) = 2w_i + 1`,
`wt(1,i) = 2w_i − 1`, and `F^{(r)}`, `E^{(r)}` given by the closed formulas of the Setting. -/
def phi (N : DPLattice A) : DPLattice A where
  ι := Fin 2 × N.ι
  wt := phiWt N
  Fd := phiFd N
  Ed := phiEd N
  isDP := isDP_of_rec (phi_recData N)

/-- (A1) The data of `Φ(N)` (weights `phiWt N`, closed formulas `phiFd N`, `phiEd N`) satisfy
`IsDP`: (W) for `F` and `E`, (P0), (P1) for `F` and `E`, and (K). -/
theorem A1 : IsDP (phiWt N) (phiFd N) (phiEd N) := isDP_of_rec (phi_recData N)

/-- (A1) `phi N` is the DP-lattice `Φ(N)` with the data of the Setting. -/
theorem phi_data : (phi N).ι = (Fin 2 × N.ι) ∧ (phi N).wt = phiWt N ∧ (phi N).Fd = phiFd N ∧
    (phi N).Ed = phiEd N := ⟨rfl, rfl, rfl, rfl⟩

/-- (B1) The single operators of `Φ(N)`: `F(b_0 n) = b_1 n`, `F(b_1 n) = 2 b_0 F n`,
`E(b_0 n) = 2 b_1 E n` (for every vector `n`), and, for `n` of weight `w`,
`E(b_1 n) = b_0 (4FE + 2w + 1) n`, `H(b_0 n) = (2w+1) b_0 n`, `H(b_1 n) = (2w−1) b_1 n`. -/
theorem B1 :
    (∀ n : N.ι → A, (phi N).Fd 1 (bvec 0 n) = bvec 1 n) ∧
    (∀ n : N.ι → A, (phi N).Fd 1 (bvec 1 n) = (2 : A) • bvec 0 (N.Fd 1 n)) ∧
    (∀ n : N.ι → A, (phi N).Ed 1 (bvec 0 n) = (2 : A) • bvec 1 (N.Ed 1 n)) ∧
    (∀ (w : ℤ) (n : N.ι → A), InWt N.wt w n →
      (phi N).Ed 1 (bvec 1 n) = bvec 0 ((4 : A) • N.Fd 1 (N.Ed 1 n) + ((2 * w + 1 : ℤ) : A) • n)) ∧
    (∀ (w : ℤ) (n : N.ι → A), InWt N.wt w n →
      H (phi N) (bvec 0 n) = ((2 * w + 1 : ℤ) : A) • bvec 0 n) ∧
    (∀ (w : ℤ) (n : N.ι → A), InWt N.wt w n →
      H (phi N) (bvec 1 n) = ((2 * w - 1 : ℤ) : A) • bvec 1 n) := by
  refine ⟨F1_b0 N, F1_b1 N, E1_b0 N, fun w n hn => E1_b1' N hn, fun w n hn => ?_,
    fun w n hn => ?_⟩
  · have := Hop_of_inWt (inWt_bvec N 0 hn)
    simpa using this
  · have := Hop_of_inWt (inWt_bvec N 1 hn)
    simp only [wtV_one] at this
    rw [show 2 * w + -1 = 2 * w - 1 by ring] at this
    exact this

/-- (B2) On `Φ(N)`, `r! • F^{(r)} = (F^{(1)})^r` and `r! • E^{(r)} = (E^{(1)})^r` for every `r`. -/
theorem B2 (r : ℕ) :
    ((r.factorial : ℕ) : A) • (phi N).Fd r = (phi N).Fd 1 ^ r ∧
    ((r.factorial : ℕ) : A) • (phi N).Ed r = (phi N).Ed 1 ^ r :=
  ⟨factorial_smul_of_rec _ (phi_P0_F N) (phi_rec_F N) r,
    factorial_smul_of_rec _ (phi_P0_E N) (phi_rec_E N) r⟩

/-- (B3) The `F`-formulas of Prop. 3.1 (b), for every vector `n` of `N` and every `s ≥ 0`:
`F^{(2s)}(b_e n) = ⅟(2s−1)!! · b_e F^{(s)} n`, `F^{(2s+1)}(b_0 n) = ⅟(2s+1)!! · b_1 F^{(s)} n`,
`F^{(2s+1)}(b_1 n) = (2s+2)·⅟(2s+1)!! · b_0 F^{(s+1)} n`. -/
theorem B3 (s : ℕ) (n : N.ι → A) :
    (∀ e : Fin 2, (phi N).Fd (2 * s) (bvec e n) = dfi (A := A) s • bvec e (N.Fd s n)) ∧
    (phi N).Fd (2 * s + 1) (bvec 0 n) = dfi (A := A) (s + 1) • bvec 1 (N.Fd s n) ∧
    (phi N).Fd (2 * s + 1) (bvec 1 n) =
      (((2 * s + 2 : ℕ) : A) * dfi (s + 1)) • bvec 0 (N.Fd (s + 1) n) :=
  ⟨fun e => (phiFd_bvec N _ e n).trans (phiFdL_even N s e n),
    (phiFd_bvec N _ 0 n).trans (phiFdL_odd0 N s n),
    (phiFd_bvec N _ 1 n).trans (phiFdL_odd1 N s n)⟩

end phi

end Doubling
