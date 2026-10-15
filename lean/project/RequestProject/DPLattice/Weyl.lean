module

public import RequestProject.DPLattice.Tensor

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: `V` and the Weyl lattices (Part T)

Encodings:
* `V A` is the natural module: `ι = Fin 2`, `wt 0 = 1`, `wt 1 = −1`, `F^{(0)} = E^{(0)} = 1`,
  `F^{(1)} b_0 = b_1`, `F^{(1)} b_1 = 0`, `E^{(1)} b_1 = b_0`, `E^{(1)} b_0 = 0`, and
  `F^{(r)} = E^{(r)} = 0` for `r ≥ 2` (the operators `F^{(1)}`, `E^{(1)}` are given by their
  matrices in the basis `(b_0, b_1)`).
* `nabla A l` is `∇_A(λ)` (`l = λ`) and `delta A l` is `Δ_A(λ)`: `ι = Fin (λ + 1)`,
  `wt r = λ − 2r`, and the operators are given by their matrices
  (`Matrix.toLin'`, column `r` = image of the basis vector `r`):
  `∇`: `F^{(t)} w_r = C(λ − r, t) w_{r+t}`, `E^{(s)} w_r = C(r, s) w_{r−s}`;
  `Δ`: `F^{(t)} e_r = C(r + t, t) e_{r+t}`, `E^{(s)} e_r = C(λ − r + s, s) e_{r−s}`,
  where a basis vector with index outside `[0, λ]` is `0`. Here `λ − r ≥ 0` and `λ − r + s ≥ 0`,
  so these binomials are ordinary `Nat.choose`; see `nabla_Fd_single`, …, `delta_Ed_single` for
  the formulas in the form of the file.

Proof strategy (not part of the statements): `∇_A(λ + 1)` is the image of `V ⊗ ∇_A(λ)` under the
surjective intertwiner `b_0 ⊗ w_r ↦ w_r`, `b_1 ⊗ w_r ↦ w_{r+1}`, so (T4) for `∇` follows from
(T2) by induction on `λ`; `Δ_A(λ)` is the transpose (dual) of `∇_A(λ)`, and the transpose of a
DP-lattice (with `F` and `E` exchanged) is a DP-lattice. `V` is `∇_A(1)` (T5).
-/

@[expose] public section

noncomputable section

namespace DPLattice

open Finset

variable {A : Type*} [CommRing A]

lemma toLin'_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (r m : ι) :
    Matrix.toLin' M (Pi.single r 1) m = M m r := by simp

/-! ### Transpose (dual) of a DP-lattice -/

section dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (T4, auxiliary) The transpose of an endomorphism of `ι → A` (in the basis `δ_i`). -/
def tr (f : Module.End A (ι → A)) : Module.End A (ι → A) :=
  Matrix.toLin' (LinearMap.toMatrix' f).transpose

lemma tr_single_apply (f : Module.End A (ι → A)) (i k : ι) :
    tr f (Pi.single i 1) k = f (Pi.single k 1) i := by
  simp [tr, LinearMap.toMatrix'_apply]

lemma tr_comp (f g : Module.End A (ι → A)) : tr (f ∘ₗ g) = tr g ∘ₗ tr f := by
  simp [tr, LinearMap.toMatrix'_comp, Matrix.transpose_mul, Matrix.toLin'_mul]

lemma tr_one : tr (1 : Module.End A (ι → A)) = 1 := by
  simp [tr, Module.End.one_eq_id, LinearMap.toMatrix'_id]

lemma tr_smul (c : A) (f : Module.End A (ι → A)) : tr (c • f) = c • tr f := by
  simp [tr]

lemma tr_toLin' (M : Matrix ι ι A) : tr (Matrix.toLin' M) = Matrix.toLin' M.transpose := by
  simp [tr]

lemma tr_comp_single_apply (f g : Module.End A (ι → A)) (i k : ι) :
    tr g (tr f (Pi.single i 1)) k = f (g (Pi.single k 1)) i := by
  rw [← LinearMap.comp_apply, ← tr_comp, tr_single_apply, LinearMap.comp_apply]

lemma choose_symm' (a b : ℕ) :
    Ring.choose ((a : ℤ) + b) a = Ring.choose ((b : ℤ) + a) b := by
  rw [choose_natAdd, choose_natAdd, add_comm b a, Nat.choose_symm_add]

/-- (T4, auxiliary) The transpose of a DP-lattice, with `F` and `E` exchanged (`F'^{(r)} = (E^{(r)})ᵀ`,
`E'^{(r)} = (F^{(r)})ᵀ`, same weights), is a DP-lattice. -/
theorem IsDP.dual {wt : ι → ℤ} {F E : ℕ → Module.End A (ι → A)} (h : IsDP wt F E) :
    IsDP wt (fun r => tr (E r)) (fun r => tr (F r)) where
  W_F i r j hj := by
    rw [tr_single_apply]; exact h.W_E j r i (by omega)
  W_E i r j hj := by
    rw [tr_single_apply]; exact h.W_F j r i (by omega)
  P0_F := by simp only [h.P0_E, tr_one]
  P0_E := by simp only [h.P0_F, tr_one]
  P1_F a b := by
    rw [← tr_comp, h.P1_E, tr_smul, choose_symm', add_comm b a]
  P1_E a b := by
    rw [← tr_comp, h.P1_F, tr_smul, choose_symm', add_comm b a]
  K i r s := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [tr_comp_single_apply, h.K k s r]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [min_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj
    rw [tr_comp_single_apply]
    by_cases hz : F (s - j) (E (r - j) (Pi.single k 1)) i = 0
    · rw [hz, mul_zero, mul_zero]
    · have hw := (h.inWt_Fd (s - j) (h.inWt_Ed (r - j) (inWt_single wt k))) i
      have hwi : wt i = wt k + 2 * ((r - j : ℕ) : ℤ) - 2 * ((s - j : ℕ) : ℤ) := by
        by_contra hc; exact hz (hw hc)
      congr 3
      push_cast [hj.1, hj.2] at hwi ⊢
      omega

end dual

/-! ### The dual Weyl lattice `∇_A(λ)` -/

section nabla

/-- (T4) the matrix of `F^{(t)}` on `∇_A(λ)`: `F^{(t)} w_r = C(λ − r, t) w_{r+t}`. -/
def nablaMatF (l t : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) A :=
  fun m r => if (m : ℕ) = r + t then ((l - r).choose t : A) else 0

/-- (T4) the matrix of `E^{(s)}` on `∇_A(λ)`: `E^{(s)} w_r = C(r, s) w_{r−s}`. -/
def nablaMatE (l s : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) A :=
  fun m r => if (m : ℕ) + s = r then ((r : ℕ).choose s : A) else 0

/-- (T4) the weight `wt(w_r) = λ − 2r` (also the weight of `e_r` in `Δ_A(λ)`). -/
def weylWt (l : ℕ) (r : Fin (l + 1)) : ℤ := l - 2 * (r : ℤ)

/-- (T4) `F^{(t)}` on `∇_A(λ)`. -/
def nablaF (l t : ℕ) : Module.End A (Fin (l + 1) → A) := Matrix.toLin' (nablaMatF l t)

/-- (T4) `E^{(s)}` on `∇_A(λ)`. -/
def nablaE (l s : ℕ) : Module.End A (Fin (l + 1) → A) := Matrix.toLin' (nablaMatE l s)

@[simp] lemma nablaF_single_apply (l t : ℕ) (r m : Fin (l + 1)) :
    nablaF (A := A) l t (Pi.single r 1) m = if (m : ℕ) = r + t then ((l - r).choose t : A) else 0 :=
  toLin'_single_apply _ _ _

@[simp] lemma nablaE_single_apply (l s : ℕ) (r m : Fin (l + 1)) :
    nablaE (A := A) l s (Pi.single r 1) m = if (m : ℕ) + s = r then ((r : ℕ).choose s : A) else 0 :=
  toLin'_single_apply _ _ _

lemma nabla_W_F (l : ℕ) : ∀ (i : Fin (l + 1)) (r : ℕ) (j : Fin (l + 1)),
    weylWt l j ≠ weylWt l i - 2 * r → nablaF (A := A) l r (Pi.single i 1) j = 0 := by
  intro i r j h
  rw [nablaF_single_apply, if_neg]
  intro hm; apply h; simp only [weylWt]; rw [hm]; push_cast; ring

lemma nabla_W_E (l : ℕ) : ∀ (i : Fin (l + 1)) (r : ℕ) (j : Fin (l + 1)),
    weylWt l j ≠ weylWt l i + 2 * r → nablaE (A := A) l r (Pi.single i 1) j = 0 := by
  intro i r j h
  rw [nablaE_single_apply, if_neg]
  intro hm; apply h; simp only [weylWt]; rw [← hm]; push_cast; ring

lemma nat_pascal' (n t : ℕ) : ((n.choose (t + 1) : A) + n.choose t) = ((n + 1).choose (t + 1) : A) := by
  rw [Nat.choose_succ_succ]; push_cast; ring

set_option hygiene false in
/-- (T4, auxiliary) Closing tactic for the finite case analyses of `nablaUp_F` and `nablaUp_E`. -/
local macro "weyl_close" : tactic => `(tactic| (
  simp only [if_true, Fin.val_castSucc, Fin.val_succ, if_false, add_zero, zero_add, one_ne_zero,
    zero_ne_one] at *
  split_ifs <;> first
    | rfl
    | omega
    | (simp; done)
    | exact nat_pascal' _ _
    | (rw [add_comm]; exact nat_pascal' _ _)
    | (rw [show s = (r : ℕ) by omega]; simp)
    | (rw [show l + 1 - (r : ℕ) = (l - r) + 1 by omega]; exact nat_pascal' _ _)
    | (rw [show l - (r : ℕ) = t by omega, show l + 1 - (r : ℕ) = t + 1 by omega]; simp)))

/-- (T4, auxiliary) The surjective intertwiner `V ⊗ ∇_A(λ) → ∇_A(λ+1)`,
`b_0 ⊗ w_r ↦ w_r`, `b_1 ⊗ w_r ↦ w_{r+1}`. -/
def nablaUp (l : ℕ) : (Fin 2 × Fin (l + 1) → A) →ₗ[A] (Fin (l + 2) → A) where
  toFun z m := (if h : (m : ℕ) ≤ l then z (0, ⟨m, by omega⟩) else 0) +
    (if h : 1 ≤ (m : ℕ) then z (1, ⟨m - 1, by omega⟩) else 0)
  map_add' z z' := by
    funext m; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c z := by
    funext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma nablaUp_apply (l : ℕ) (z : Fin 2 × Fin (l + 1) → A) (m : Fin (l + 2)) :
    nablaUp l z m = (if h : (m : ℕ) ≤ l then z (0, ⟨m, by omega⟩) else 0) +
      (if h : 1 ≤ (m : ℕ) then z (1, ⟨m - 1, by omega⟩) else 0) := rfl

lemma nablaUp_b0 (l : ℕ) (r : Fin (l + 1)) :
    nablaUp (A := A) l (bvec 0 (Pi.single r 1)) = Pi.single r.castSucc 1 := by
  funext m
  simp only [nablaUp_apply, bvec_apply, Pi.single_apply, Fin.ext_iff, Fin.val_castSucc]
  split_ifs <;> simp_all; omega

lemma nablaUp_b1 (l : ℕ) (r : Fin (l + 1)) :
    nablaUp (A := A) l (bvec 1 (Pi.single r 1)) = Pi.single r.succ 1 := by
  funext m
  simp only [nablaUp_apply, bvec_apply, Pi.single_apply, Fin.ext_iff, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

lemma nablaUp_F (l t : ℕ) :
    nablaUp (A := A) l ∘ₗ tensorFd (nablaF l) t = nablaF (l + 1) t ∘ₗ nablaUp l := by
  refine ext_single fun p => ?_
  obtain ⟨e, r⟩ := p
  rw [single_eq_bvec, LinearMap.comp_apply, LinearMap.comp_apply]
  funext m
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  · rw [tensorFd_bvec0, nablaUp_b0, nablaF_single_apply, nablaUp_apply]
    rcases t with _ | t
    · simp only [pred_zero, LinearMap.zero_apply, bvec_apply, Pi.add_apply, nablaF_single_apply]
      weyl_close
    · simp only [pred_succ, bvec_apply, Pi.add_apply, nablaF_single_apply]
      weyl_close
  · rw [tensorFd_bvec1, nablaUp_b1, nablaF_single_apply, nablaUp_apply]
    simp only [bvec_apply, nablaF_single_apply]
    weyl_close

lemma nablaUp_E (l s : ℕ) :
    nablaUp (A := A) l ∘ₗ tensorEd (nablaE l) s = nablaE (l + 1) s ∘ₗ nablaUp l := by
  refine ext_single fun p => ?_
  obtain ⟨e, r⟩ := p
  rw [single_eq_bvec, LinearMap.comp_apply, LinearMap.comp_apply]
  funext m
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  · rw [tensorEd_bvec0, nablaUp_b0, nablaE_single_apply, nablaUp_apply]
    simp only [bvec_apply, nablaE_single_apply]
    weyl_close
  · rw [tensorEd_bvec1, nablaUp_b1, nablaE_single_apply, nablaUp_apply]
    rcases s with _ | s
    · simp only [pred_zero, LinearMap.zero_apply, bvec_apply, Pi.add_apply, nablaE_single_apply]
      weyl_close
    · simp only [pred_succ, bvec_apply, Pi.add_apply, nablaE_single_apply]
      weyl_close

/-- (T4, auxiliary) The identification `𝟙 → ∇_A(0)` (used for the base case of the induction). -/
def nablaZero : (Unit → A) →ₗ[A] (Fin 1 → A) where
  toFun z _ := z ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma nablaZero_single : nablaZero (A := A) (Pi.single () 1) = Pi.single 0 1 := by
  funext m; fin_cases m; simp [nablaZero]

lemma nablaZero_F (t : ℕ) : nablaZero (A := A) ∘ₗ oneFd A t = nablaF 0 t ∘ₗ nablaZero := by
  refine ext_single fun u => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, nablaZero_single]
  funext m; fin_cases m
  rcases t with _ | t
  · simp [oneFd, nablaZero]
  · simp [oneFd]

lemma nablaZero_E (t : ℕ) : nablaZero (A := A) ∘ₗ oneFd A t = nablaE 0 t ∘ₗ nablaZero := by
  refine ext_single fun u => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, nablaZero_single]
  funext m; fin_cases m
  rcases t with _ | t
  · simp [oneFd, nablaZero]
  · simp [oneFd]

/-- (T4) `∇_A(λ)` satisfies (W), (P0), (P1), (K). -/
theorem nabla_isDP (l : ℕ) : IsDP (A := A) (weylWt l) (nablaF l) (nablaE l) := by
  induction l with
  | zero =>
    refine one_isDP.of_surj (nabla_W_F 0) (nabla_W_E 0) nablaZero nablaZero_F nablaZero_E
      (fun k => ⟨(), ?_, ?_⟩)
    · rw [nablaZero_single]; congr; exact Subsingleton.elim _ _
    · fin_cases k; simp [weylWt]
  | succ l ih =>
    let M : DPLattice A := ⟨Fin (l + 1), weylWt l, nablaF l, nablaE l, ih⟩
    refine (tensorV M).isDP.of_surj (nabla_W_F (l + 1)) (nabla_W_E (l + 1)) (nablaUp l)
      (nablaUp_F l) (nablaUp_E l) (fun k => ?_)
    by_cases hk : (k : ℕ) = 0
    · refine ⟨(0, 0), ?_, ?_⟩
      · rw [single_eq_bvec]
        refine (nablaUp_b0 l 0).trans ?_
        congr 1; ext; simp [hk]
      · simp [tensorV, tensorWt, weylWt, hk, M]; ring
    · refine ⟨(1, ⟨k - 1, by omega⟩), ?_, ?_⟩
      · rw [single_eq_bvec]
        refine (nablaUp_b1 l _).trans ?_
        congr 1; ext; simp; omega
      · simp only [tensorV, tensorWt, weylWt, M, wtV_one]
        push_cast [Nat.one_le_iff_ne_zero.mpr hk]
        ring

/-- (T4) the dual Weyl lattice `∇_A(λ)`: basis `w_r` (`ι = Fin (λ + 1)`), `wt(w_r) = λ − 2r`,
`F^{(t)} w_r = C(λ − r, t) w_{r+t}`, `E^{(s)} w_r = C(r, s) w_{r−s}` (see `nabla_Fd_single`,
`nabla_Ed_single`). -/
def nabla (A : Type*) [CommRing A] (l : ℕ) : DPLattice A where
  ι := Fin (l + 1)
  wt := weylWt l
  Fd := nablaF l
  Ed := nablaE l
  isDP := nabla_isDP l

end nabla

/-! ### The Weyl lattice `Δ_A(λ)` -/

section delta

/-- (T4) the matrix of `F^{(t)}` on `Δ_A(λ)`: `F^{(t)} e_r = C(r + t, t) e_{r+t}`. -/
def deltaMatF (l t : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) A :=
  fun m r => if (m : ℕ) = r + t then (((r : ℕ) + t).choose t : A) else 0

/-- (T4) the matrix of `E^{(s)}` on `Δ_A(λ)`: `E^{(s)} e_r = C(λ − r + s, s) e_{r−s}`. -/
def deltaMatE (l s : ℕ) : Matrix (Fin (l + 1)) (Fin (l + 1)) A :=
  fun m r => if (m : ℕ) + s = r then ((l - r + s).choose s : A) else 0

/-- (T4) `F^{(t)}` on `Δ_A(λ)`. -/
def deltaF (l t : ℕ) : Module.End A (Fin (l + 1) → A) := Matrix.toLin' (deltaMatF l t)

/-- (T4) `E^{(s)}` on `Δ_A(λ)`. -/
def deltaE (l s : ℕ) : Module.End A (Fin (l + 1) → A) := Matrix.toLin' (deltaMatE l s)

@[simp] lemma deltaF_single_apply (l t : ℕ) (r m : Fin (l + 1)) :
    deltaF (A := A) l t (Pi.single r 1) m =
      if (m : ℕ) = r + t then (((r : ℕ) + t).choose t : A) else 0 :=
  toLin'_single_apply _ _ _

@[simp] lemma deltaE_single_apply (l s : ℕ) (r m : Fin (l + 1)) :
    deltaE (A := A) l s (Pi.single r 1) m =
      if (m : ℕ) + s = r then ((l - r + s).choose s : A) else 0 :=
  toLin'_single_apply _ _ _

lemma deltaF_eq (l t : ℕ) : deltaF (A := A) l t = tr (nablaE l t) := by
  rw [nablaE, tr_toLin', deltaF]
  congr 1
  ext m r
  simp only [deltaMatF, Matrix.transpose_apply, nablaMatE]
  by_cases h : (m : ℕ) = r + t
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma deltaE_eq (l s : ℕ) : deltaE (A := A) l s = tr (nablaF l s) := by
  rw [nablaF, tr_toLin', deltaE]
  congr 1
  ext m r
  simp only [deltaMatE, Matrix.transpose_apply, nablaMatF]
  by_cases h : (m : ℕ) + s = r
  · rw [if_pos h, if_pos h.symm]
    have := r.isLt
    congr 2; omega
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- (T4) `Δ_A(λ)` satisfies (W), (P0), (P1), (K). -/
theorem delta_isDP (l : ℕ) : IsDP (A := A) (weylWt l) (deltaF l) (deltaE l) := by
  have hF : deltaF (A := A) l = fun t => tr (nablaE l t) := funext (deltaF_eq l)
  have hE : deltaE (A := A) l = fun s => tr (nablaF l s) := funext (deltaE_eq l)
  rw [hF, hE]
  exact (nabla_isDP l).dual

/-- (T4) the Weyl lattice `Δ_A(λ)`: basis `e_r` (`ι = Fin (λ + 1)`), `wt(e_r) = λ − 2r`,
`F^{(t)} e_r = C(r + t, t) e_{r+t}`, `E^{(s)} e_r = C(λ − r + s, s) e_{r−s}` (see `delta_Fd_single`,
`delta_Ed_single`). -/
def delta (A : Type*) [CommRing A] (l : ℕ) : DPLattice A where
  ι := Fin (l + 1)
  wt := weylWt l
  Fd := deltaF l
  Ed := deltaE l
  isDP := delta_isDP l

end delta

end DPLattice
