module

public import RequestProject.OddSplit.Retract

/-!
# `CSI3_the_split.md`: Part B — `Ψ_1(N) ≅ V ⊗ Φ_p(N)` (the map `κ`)

Encodings: `W = Tensor2.tensor (V ℤ_[p]) (twist p N)` (basis `Fin 2 × (Fin p × N.ι)`), with
`b̂_e ⊗ b_j n = tv e (bv p j n)`; `WF p N`, `WE p N` are `W.Fd 1`, `W.Ed 1` on
`Fin 2 × (Fin p × N.ι) → ℤ_[p]`.

* `kappa p N` is `κ`: the linear extension of `κ(A_j e_i) = b̂_0 ⊗ b_j e_i + j·b̂_1 ⊗ b_{j−1} e_i`
  (the second term is `0` for `j = 0`), `κ(C_j e_i) = b̂_1 ⊗ b_j e_i` (`kappa_aV`, `kappa_cV`).
* `kappaInv p N` is its inverse: `b̂_1 ⊗ b_j n ↦ C_j n`, `b̂_0 ⊗ b_j n ↦ A_j n − j·C_{j−1} n`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- Part B: `W = V ⊗ Φ_p(N)`. -/
abbrev Wt : DPLattice ℤ_[p] := Tensor2.tensor (V ℤ_[p]) (twist p N)

/-- Part B: `F = W.Fd 1` on `Fin 2 × (Fin p × N.ι) → ℤ_[p]`. -/
def WF : Module.End ℤ_[p] (Fin 2 × (Fin p × N.ι) → ℤ_[p]) := (Wt p N).Fd 1

/-- Part B: `E = W.Ed 1` on `Fin 2 × (Fin p × N.ι) → ℤ_[p]`. -/
def WE : Module.End ℤ_[p] (Fin 2 × (Fin p × N.ι) → ℤ_[p]) := (Wt p N).Ed 1

/-- (B1) `κ(A_j n) = b̂_0 ⊗ b_j n + j·b̂_1 ⊗ b_{j−1} n` as a linear map of `n`. -/
def kapA (j : ℕ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Fin p × N.ι) → ℤ_[p]) :=
  tv 0 ∘ₗ bv p j + (j : ℤ_[p]) • (tv 1 ∘ₗ bv p (j - 1))

/-- (B1) `κ(C_j n) = b̂_1 ⊗ b_j n` as a linear map of `n`. -/
def kapC (j : ℕ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Fin p × N.ι) → ℤ_[p]) := tv 1 ∘ₗ bv p j

/-- (B1) the map `κ : Ψ_1(N) → V ⊗ Φ_p(N)`. -/
def kappa : (Bool × Fin p × N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Fin p × N.ι) → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Bool × Fin p × N.ι)).constr ℤ_[p]
    (fun x => if x.1 then kapC p N x.2.1 (Pi.single x.2.2 1) else kapA p N x.2.1 (Pi.single x.2.2 1))

/-- (B2) the inverse of `κ`: `b̂_1 ⊗ b_j n ↦ C_j n`, `b̂_0 ⊗ b_j n ↦ A_j n − j·C_{j−1} n`. -/
def kappaInv : (Fin 2 × (Fin p × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Fin 2 × (Fin p × N.ι))).constr ℤ_[p]
    (fun x => if x.1 = 0 then aV p x.2.1 (Pi.single x.2.2 1) -
        ((x.2.1 : ℕ) : ℤ_[p]) • cV p ((x.2.1 : ℕ) - 1) (Pi.single x.2.2 1)
      else cV p x.2.1 (Pi.single x.2.2 1))

variable {p N}

lemma kappa_aV {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    kappa p N (aV p j n) = tv 0 (bv p j n) + (j : ℤ_[p]) • tv 1 (bv p (j - 1) n) := by
  have : kappa p N ∘ₗ aV p j = kapA p N j := ext_single fun i => by
    rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_false, kappa,
      ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]; rfl
  have h := LinearMap.congr_fun this n
  rw [LinearMap.comp_apply] at h
  rw [h]; rfl

lemma kappa_cV {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    kappa p N (cV p j n) = tv 1 (bv p j n) := by
  have : kappa p N ∘ₗ cV p j = kapC p N j := ext_single fun i => by
    rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_true, kappa,
      ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]; rfl
  exact LinearMap.congr_fun this n

lemma single_W (e : Fin 2) (j : Fin p) (i : N.ι) :
    (Pi.single (e, (j, i)) (1 : ℤ_[p]) : Fin 2 × (Fin p × N.ι) → ℤ_[p]) =
      tv e (bv p j (Pi.single i 1)) := by
  rw [Tensor2.single_prod_eq_tprod, single_eq_bv]; rfl

lemma kappaInv_tv0 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    kappaInv p N (tv 0 (bv p j n)) = aV p j n - (j : ℤ_[p]) • cV p (j - 1) n := by
  have : kappaInv p N ∘ₗ tv 0 ∘ₗ bv p j = aV p j - (j : ℤ_[p]) • cV p (j - 1) :=
    ext_single fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl,
        ← single_W, kappaInv, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]; rfl
  exact LinearMap.congr_fun this n

lemma kappaInv_tv1 {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    kappaInv p N (tv 1 (bv p j n)) = cV p j n := by
  have : kappaInv p N ∘ₗ tv 1 ∘ₗ bv p j = cV p j :=
    ext_single fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl,
        ← single_W, kappaInv, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]; rfl
  exact LinearMap.congr_fun this n

/-- (B2) `κ⁻¹ ∘ κ = id`. -/
theorem kappaInv_kappa : kappaInv p N ∘ₗ kappa p N = LinearMap.id := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [kappa_aV hj, map_add, map_smul, kappaInv_tv0 hj, kappaInv_tv1 (by omega)]
    abel
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [kappa_cV hj, kappaInv_tv1 hj]

/-- (B2) `κ ∘ κ⁻¹ = id`. -/
theorem kappa_kappaInv : kappa p N ∘ₗ kappaInv p N = LinearMap.id := by
  refine ext_single fun x => ?_
  obtain ⟨e, j, i⟩ := x
  rw [single_W, LinearMap.comp_apply, LinearMap.id_apply]
  rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with rfl | rfl
  · rw [kappaInv_tv0 j.isLt, map_sub, map_smul, kappa_aV j.isLt, kappa_cV (by omega)]
    abel
  · rw [kappaInv_tv1 j.isLt, kappa_cV j.isLt]

/-! ### (B3) intertwining -/

lemma WF_tv0 (x : Fin p × N.ι → ℤ_[p]) : WF p N (tv 0 x) = tv 1 x + tv 0 (twFd p N 1 x) :=
  tensorV_Fd1_tv0 (twist p N) x

lemma WF_tv1 (x : Fin p × N.ι → ℤ_[p]) : WF p N (tv 1 x) = tv 1 (twFd p N 1 x) :=
  tensorV_Fd1_tv1 (twist p N) x

lemma WE_tv0 (x : Fin p × N.ι → ℤ_[p]) : WE p N (tv 0 x) = tv 0 (twEd p N 1 x) :=
  tensorV_Ed1_tv0 (twist p N) x

lemma WE_tv1 (x : Fin p × N.ι → ℤ_[p]) : WE p N (tv 1 x) = tv 0 x + tv 1 (twEd p N 1 x) :=
  tensorV_Ed1_tv1 (twist p N) x

/-! The single operators of `Φ_p(N)`, from CSI1's `B1`. -/

lemma tF_lt {j : ℕ} (hj : j + 1 < p) (n : N.ι → ℤ_[p]) : twFd p N 1 (bv p j n) = bv p (j + 1) n :=
  (B1 p N).1 j n hj

lemma tF_last (n : N.ι → ℤ_[p]) :
    twFd p N 1 (bv p (p - 1) n) = (-(p : ℤ_[p])) • bv p 0 (N.Fd 1 n) := (B1 p N).2.1 n

lemma tE_pos {j : ℕ} (h1 : 1 ≤ j) (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    twEd p N 1 (bv p j n) = bv p (j - 1)
      ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) + (((j : ℤ) * (p * w + p - j) : ℤ) : ℤ_[p]) • n) :=
  (B1 p N).2.2.1 j w n h1 hj hn

lemma tE_zero (n : N.ι → ℤ_[p]) :
    twEd p N 1 (bv p 0 n) = (-(p : ℤ_[p])) • bv p (p - 1) (N.Ed 1 n) := (B1 p N).2.2.2.1 n

/-- (B3) `κ ∘ psiF p 1 N = W.Fd 1 ∘ κ`. The key line is
`F(b̂_0 ⊗ b_{p−1} n + (p−1) b̂_1 ⊗ b_{p−2} n) = −p·b̂_0 ⊗ b_0 Fn + p·b̂_1 ⊗ b_{p−1} n`. -/
theorem kappa_F : kappa p N ∘ₗ psiF p N 1 = WF p N ∘ₗ kappa p N := by
  have hp := two_le_p' (p := p)
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_A_lt 1 hl, kappa_aV hl, kappa_aV hj, Nat.add_sub_cancel]
      simp only [map_add, map_smul, WF_tv0, WF_tv1, tF_lt hl]
      rcases j with _ | j
      · simp; abel
      · rw [show j + 1 - 1 = j by omega, tF_lt (N := N) (j := j) (by omega)]
        push_cast; module
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_A_last, kappa_aV hj, map_add, map_smul, map_smul,
        kappa_aV (N := N) (j := 0) (by omega), kappa_cV (N := N) (j := p - 1) (by omega)]
      simp only [map_add, map_smul, WF_tv0, WF_tv1, tF_last,
        tF_lt (N := N) (j := p - 1 - 1) (by omega), show p - 1 - 1 + 1 = p - 1 by omega,
        Nat.cast_zero, zero_smul, add_zero, smul_add]
      push_cast [hc1]
      module
  · simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_C_lt 1 hl, kappa_cV hl, kappa_cV hj, WF_tv1, tF_lt hl]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_C_last, map_smul, kappa_cV (N := N) (j := 0) (by omega), kappa_cV hj, WF_tv1,
        tF_last, map_smul]

/-- (B3) `κ ∘ psiE p 1 N = W.Ed 1 ∘ κ`. -/
theorem kappa_E : kappa p N ∘ₗ psiE p N 1 = WE p N ∘ₗ kappa p N := by
  have hp := two_le_p' (p := p)
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [psiE_A_zero 1 hn, kappa_aV hj, map_add, map_smul, map_smul,
          kappa_aV (N := N) (j := p - 1) (by omega), kappa_cV (N := N) (j := p - 1 - 1) (by omega)]
        simp only [map_add, map_smul, WE_tv0, WE_tv1, tE_zero, Nat.cast_zero, zero_smul,
          add_zero, smul_add, show p - 1 - 1 = p - 1 - 1 from rfl]
        push_cast [hc1]
        module
      · rw [psiE_A_low 1 le_rfl le_rfl hj hn, kappa_aV hj, map_sub, map_smul,
          kappa_aV (N := N) (j := 1 - 1) (by omega), kappa_cV (N := N) (j := p + 1 - 1 - 1) (by omega)]
        simp only [map_add, map_smul, WE_tv0, WE_tv1, tE_zero, tE_pos le_rfl hj hn, Nat.sub_self,
          Nat.cast_zero, zero_smul, add_zero, smul_add, show p + 1 - 1 - 1 = p - 1 by omega]
        push_cast
        module
    · have hcj : ((j - 1 : ℕ) : ℤ_[p]) = j - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [psiE_A_high 1 (by omega) hj hn, kappa_aV hj, map_add, map_smul,
        kappa_aV (N := N) (j := j - 1) (by omega), kappa_cV (N := N) (j := j - 1 - 1) (by omega)]
      simp only [map_add, map_smul, WE_tv0, WE_tv1, tE_pos (N := N) (j := j) (by omega) hj hn,
        tE_pos (N := N) (j := j - 1) (by omega) (by omega) hn, smul_add, hcj]
      push_cast [hcj]
      module
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [psiE_C_zero 1 hn, kappa_cV hj, map_sub, map_smul, map_smul,
        kappa_aV (N := N) (j := 1 - 1) (by omega), kappa_cV (N := N) (j := p - 1) (by omega)]
      simp only [map_add, map_smul, WE_tv1, tE_zero, Nat.sub_self, Nat.cast_zero, zero_smul,
        add_zero]
      push_cast
      module
    · rw [psiE_C_low 1 hpos (by omega) hj hn, kappa_cV hj, map_add, map_smul,
        kappa_cV (N := N) (j := j - 1) (by omega), kappa_aV (N := N) (j := j + 1 - 1) (by omega)]
      simp only [map_add, map_smul, WE_tv1, tE_pos hpos hj hn, show j + 1 - 1 = j by omega,
        smul_add]
      push_cast
      module

/-! ### (B3) weights -/

/-- (B3) `κ` is weight-preserving: `κ(δ_x)` has weight `psiWt p N 1 x`. -/
lemma kappa_single_inWt (x : Bool × Fin p × N.ι) :
    InWt (Wt p N).wt (psiWt p N 1 x) (kappa p N (Pi.single x 1)) := by
  obtain ⟨b, ⟨j, hj⟩, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  cases b
  · rw [single_false, kappa_aV hj]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [Nat.cast_zero, zero_smul, add_zero]
      exact Doubling.inWt_congr (by simp [psiWt]) (inWt_tv (twist p N) 0 (inWt_tw p N 0 hn))
    · refine Doubling.inWt_add (Doubling.inWt_congr ?_ (inWt_tv (twist p N) 0 (inWt_tw p N j hn)))
        (Doubling.inWt_smul _ (Doubling.inWt_congr ?_ (inWt_tv (twist p N) 1
          (inWt_tw p N (j - 1) hn))))
      · simp [psiWt]; ring
      · simp [psiWt]; push_cast [Nat.cast_sub (show 1 ≤ j by omega)]; ring
  · rw [single_true, kappa_cV hj]
    exact Doubling.inWt_congr (by simp [psiWt]; ring) (inWt_tv (twist p N) 1 (inWt_tw p N j hn))

/-- (B3) `κ` is weight-preserving (in the form used by C29's `Filt.sub`). -/
lemma kappa_wtPres (x : Bool × Fin p × N.ι) (z : Fin 2 × (Fin p × N.ι))
    (h : psiWt p N 1 x ≠ (Wt p N).wt z) : kappa p N (Pi.single x 1) z = 0 :=
  kappa_single_inWt x z (Ne.symm h)

/-- (B3) `κ ∘ H = H ∘ κ`. -/
lemma kappa_H : kappa p N ∘ₗ Hop (psiWt p N 1) = H (Wt p N) ∘ₗ kappa p N :=
  comm_Hop_of_wtPres (kappa p N) kappa_wtPres

/-- (B2) `κ⁻¹` is weight-preserving. -/
lemma kappaInv_wtPres (z : Fin 2 × (Fin p × N.ι)) (x : Bool × Fin p × N.ι)
    (h : (Wt p N).wt z ≠ psiWt p N 1 x) : kappaInv p N (Pi.single z 1) x = 0 := by
  have hH : kappaInv p N ∘ₗ H (Wt p N) = Hop (psiWt p N 1) ∘ₗ kappaInv p N := by
    calc kappaInv p N ∘ₗ H (Wt p N)
        = kappaInv p N ∘ₗ H (Wt p N) ∘ₗ (kappa p N ∘ₗ kappaInv p N) := by
          rw [kappa_kappaInv]; rfl
      _ = kappaInv p N ∘ₗ (kappa p N ∘ₗ Hop (psiWt p N 1)) ∘ₗ kappaInv p N := by
          rw [kappa_H]; rfl
      _ = (kappaInv p N ∘ₗ kappa p N) ∘ₗ Hop (psiWt p N 1) ∘ₗ kappaInv p N := rfl
      _ = Hop (psiWt p N 1) ∘ₗ kappaInv p N := by rw [kappaInv_kappa]; rfl
  exact wtPres_of_comm_Hop (kappaInv p N) hH z x h

end ColouredSand.OddTwist
