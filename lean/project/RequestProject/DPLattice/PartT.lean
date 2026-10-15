module

public import RequestProject.DPLattice.Weyl

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: Part T

* (T1) `T1`: `𝟙` (`one A`) and `V` (`V A`) are DP-lattices; the defining formulas of `V` are
  `V_Fd_one_b0`, `V_Fd_one_b1`, `V_Ed_one_b1`, `V_Ed_one_b0`, `V_Fd_ge_two`, `V_Ed_ge_two`.
* (T2) `T2` (in `Tensor.lean`), with the coproduct formulas `tensorV_Fd_b0`, ….
* (T3) `T3` (in `Tensor.lean`), `tensorPow A n`.
* (T4) `T4`: `Δ_A(λ)` (`delta A l`) and `∇_A(λ)` (`nabla A l`) are DP-lattices; their formulas are
  `delta_Fd_single`, `delta_Ed_single`, `nabla_Fd_single`, `nabla_Ed_single`.
* (T5) `T5_delta_zero`, `T5_nabla_zero` (equal data as `𝟙` under `Fin 1 ≃ Unit`) and
  `T5_delta_one`, `T5_nabla_one` (`Δ_A(1) = V` and `∇_A(1) = V` as DP-lattices).
-/

@[expose] public section

noncomputable section

namespace DPLattice

open Finset

variable {A : Type*} [CommRing A]

/-! ### The natural module `V` -/

/-- (T1) the matrix of `F^{(1)}` on `V` in the basis `(b_0, b_1)`: `b_0 ↦ b_1`, `b_1 ↦ 0`. -/
def VmatF : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- (T1) the matrix of `E^{(1)}` on `V` in the basis `(b_0, b_1)`: `b_1 ↦ b_0`, `b_0 ↦ 0`. -/
def VmatE : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- (T1) `F^{(r)}` on `V`: `1` for `r = 0`, `VmatF` for `r = 1`, `0` for `r ≥ 2`. -/
def VFd (r : ℕ) : Module.End A (Fin 2 → A) :=
  if r = 0 then 1 else if r = 1 then Matrix.toLin' VmatF else 0

/-- (T1) `E^{(r)}` on `V`: `1` for `r = 0`, `VmatE` for `r = 1`, `0` for `r ≥ 2`. -/
def VEd (r : ℕ) : Module.End A (Fin 2 → A) :=
  if r = 0 then 1 else if r = 1 then Matrix.toLin' VmatE else 0

lemma wtV_eq : wtV = weylWt 1 := by
  funext e; fin_cases e <;> simp [wtV, weylWt]

lemma VFd_eq : VFd (A := A) = nablaF 1 := by
  funext r
  refine ext_single fun i => ?_
  funext m
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases m <;> simp [VFd]
  · fin_cases i <;> fin_cases m <;> simp [VFd, VmatF]
  · fin_cases i <;> fin_cases m <;> simp [VFd]

lemma VEd_eq : VEd (A := A) = nablaE 1 := by
  funext r
  refine ext_single fun i => ?_
  funext m
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases m <;> simp [VEd]
  · fin_cases i <;> fin_cases m <;> simp [VEd, VmatE]
  · fin_cases i <;> fin_cases m <;> simp [VEd]

lemma V_isDP : IsDP (A := A) wtV VFd VEd := by
  rw [wtV_eq, VFd_eq, VEd_eq]; exact nabla_isDP 1

/-- (T1) the natural module `V`: `ι = Fin 2`, `wt 0 = 1`, `wt 1 = −1`, `F^{(1)} b_0 = b_1`,
`F^{(1)} b_1 = 0`, `E^{(1)} b_1 = b_0`, `E^{(1)} b_0 = 0`, `F^{(r)} = E^{(r)} = 0` for `r ≥ 2`
(and `F^{(0)} = E^{(0)} = 1`). -/
def V (A : Type*) [CommRing A] : DPLattice A where
  ι := Fin 2
  wt := wtV
  Fd := VFd
  Ed := VEd
  isDP := V_isDP

/-- (T1) the weights of `V`: `wt b_0 = 1`, `wt b_1 = −1`. -/
theorem V_wt : (V A).wt (0 : Fin 2) = 1 ∧ (V A).wt (1 : Fin 2) = -1 := ⟨rfl, rfl⟩

/-- (T1) `F^{(1)} b_0 = b_1` on `V`. -/
theorem V_Fd_one_b0 : (V A).Fd 1 (Pi.single (0 : Fin 2) 1) = Pi.single (1 : Fin 2) 1 := by
  funext m; fin_cases m <;> simp [V, VFd, VmatF]

/-- (T1) `F^{(1)} b_1 = 0` on `V`. -/
theorem V_Fd_one_b1 : (V A).Fd 1 (Pi.single (1 : Fin 2) 1) = 0 := by
  funext m; fin_cases m <;> simp [V, VFd, VmatF]

/-- (T1) `E^{(1)} b_1 = b_0` on `V`. -/
theorem V_Ed_one_b1 : (V A).Ed 1 (Pi.single (1 : Fin 2) 1) = Pi.single (0 : Fin 2) 1 := by
  funext m; fin_cases m <;> simp [V, VEd, VmatE]

/-- (T1) `E^{(1)} b_0 = 0` on `V`. -/
theorem V_Ed_one_b0 : (V A).Ed 1 (Pi.single (0 : Fin 2) 1) = 0 := by
  funext m; fin_cases m <;> simp [V, VEd, VmatE]

/-- (T1) `F^{(r)} = 0` on `V` for `r ≥ 2`. -/
theorem V_Fd_ge_two (r : ℕ) (hr : 2 ≤ r) : (V A).Fd r = 0 := by
  simp [V, VFd, show r ≠ 0 by omega, show r ≠ 1 by omega]

/-- (T1) `E^{(r)} = 0` on `V` for `r ≥ 2`. -/
theorem V_Ed_ge_two (r : ℕ) (hr : 2 ≤ r) : (V A).Ed r = 0 := by
  simp [V, VEd, show r ≠ 0 by omega, show r ≠ 1 by omega]

/-- (T1) `𝟙` and `V` are DP-lattices: their data satisfy (W), (P0), (P1) and (K). -/
theorem T1 : IsDP (one A).wt (one A).Fd (one A).Ed ∧ IsDP (V A).wt (V A).Fd (V A).Ed :=
  ⟨(one A).isDP, (V A).isDP⟩

/-! ### (T4) -/

/-- (T4) `Δ_A(λ)` and `∇_A(λ)` are DP-lattices for every `λ`: their data satisfy (W), (P0), (P1)
and (K). -/
theorem T4 (l : ℕ) : IsDP (delta A l).wt (delta A l).Fd (delta A l).Ed ∧
    IsDP (nabla A l).wt (nabla A l).Fd (nabla A l).Ed :=
  ⟨(delta A l).isDP, (nabla A l).isDP⟩

/-- (T4) the weights `wt(e_r) = wt(w_r) = λ − 2r`. -/
theorem weyl_wt (l : ℕ) (r : Fin (l + 1)) :
    (delta A l).wt r = l - 2 * (r : ℤ) ∧ (nabla A l).wt r = l - 2 * (r : ℤ) := ⟨rfl, rfl⟩

/-- (T4) on `Δ_A(λ)`: `F^{(t)} e_r = C(r + t, t) e_{r+t}` (`0` if `r + t > λ`). -/
theorem delta_Fd_single (l t : ℕ) (r : Fin (l + 1)) :
    (delta A l).Fd t (Pi.single r 1) = if h : (r : ℕ) + t ≤ l then
      (((r : ℕ) + t).choose t : A) • (Pi.single (⟨r + t, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 := by
  funext m
  simp only [delta, deltaF_single_apply]
  split_ifs with h1 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff]
  omega

/-- (T4) on `Δ_A(λ)`: `E^{(s)} e_r = C(λ − r + s, s) e_{r−s}` (`0` if `s > r`). -/
theorem delta_Ed_single (l s : ℕ) (r : Fin (l + 1)) :
    (delta A l).Ed s (Pi.single r 1) = if h : s ≤ (r : ℕ) then
      ((l - r + s).choose s : A) • (Pi.single (⟨r - s, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 := by
  funext m
  simp only [delta, deltaE_single_apply]
  split_ifs with h1 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff] <;> omega

/-- (T4) on `∇_A(λ)`: `F^{(t)} w_r = C(λ − r, t) w_{r+t}` (`0` if `r + t > λ`). -/
theorem nabla_Fd_single (l t : ℕ) (r : Fin (l + 1)) :
    (nabla A l).Fd t (Pi.single r 1) = if h : (r : ℕ) + t ≤ l then
      ((l - r).choose t : A) • (Pi.single (⟨r + t, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 := by
  funext m
  simp only [nabla, nablaF_single_apply]
  split_ifs with h1 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff]
  omega

/-- (T4) on `∇_A(λ)`: `E^{(s)} w_r = C(r, s) w_{r−s}` (`0` if `s > r`). -/
theorem nabla_Ed_single (l s : ℕ) (r : Fin (l + 1)) :
    (nabla A l).Ed s (Pi.single r 1) = if h : s ≤ (r : ℕ) then
      ((r : ℕ).choose s : A) • (Pi.single (⟨r - s, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 := by
  funext m
  simp only [nabla, nablaE_single_apply]
  split_ifs with h1 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff] <;> omega

/-! ### (T5) -/

/-- (T5) The bijection `Fin 1 ≃ Unit`. -/
def finOneEquivUnit : Fin 1 ≃ Unit := Equiv.equivPUnit (Fin 1)

/-- (T5) `Δ_A(0) = 𝟙`: equal data under `Fin 1 ≃ Unit`. -/
theorem T5_delta_zero : DataEquiv (delta A 0) (one A) finOneEquivUnit where
  wt_eq i := by fin_cases i; simp [delta, one, weylWt]
  Fd_eq r f := by
    funext u
    rcases r with _ | r
    · simp [one, oneFd, delta, deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        deltaMatF]
      exact congrArg f (Subsingleton.elim (α := Fin 1) _ _)
    · simp [one, oneFd, delta, deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        deltaMatF]
  Ed_eq r f := by
    funext u
    rcases r with _ | r
    · simp [one, oneFd, delta, deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        deltaMatE]
      exact congrArg f (Subsingleton.elim (α := Fin 1) _ _)
    · simp [one, oneFd, delta, deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        deltaMatE]

/-- (T5) `∇_A(0) = 𝟙`: equal data under `Fin 1 ≃ Unit`. -/
theorem T5_nabla_zero : DataEquiv (nabla A 0) (one A) finOneEquivUnit where
  wt_eq i := by fin_cases i; simp [nabla, one, weylWt]
  Fd_eq r f := by
    funext u
    rcases r with _ | r
    · simp [one, oneFd, nabla, nablaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        nablaMatF]
      exact congrArg f (Subsingleton.elim (α := Fin 1) _ _)
    · simp [one, oneFd, nabla, nablaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        nablaMatF]
  Ed_eq r f := by
    funext u
    rcases r with _ | r
    · simp [one, oneFd, nabla, nablaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        nablaMatE]
      exact congrArg f (Subsingleton.elim (α := Fin 1) _ _)
    · simp [one, oneFd, nabla, nablaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        nablaMatE]

/-- (T5) `∇_A(1) = V` (equal data, `Fin 2 = Fin 2`). -/
theorem T5_nabla_one : nabla A 1 = V A := by
  simp only [nabla, V, wtV_eq, VFd_eq, VEd_eq]

lemma deltaF_one : deltaF (A := A) 1 = nablaF 1 := by
  funext r
  refine ext_single fun i => ?_
  funext m
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases m <;> simp
  · fin_cases i <;> fin_cases m <;> simp
  · fin_cases i <;> fin_cases m <;> simp
    omega

lemma deltaE_one : deltaE (A := A) 1 = nablaE 1 := by
  funext r
  refine ext_single fun i => ?_
  funext m
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases m <;> simp
  · fin_cases i <;> fin_cases m <;> simp
  · fin_cases i <;> fin_cases m <;> simp

/-- (T5) `Δ_A(1) = V` (equal data, `Fin 2 = Fin 2`). -/
theorem T5_delta_one : delta A 1 = V A := by
  rw [← T5_nabla_one]
  simp only [delta, nabla, deltaF_one, deltaE_one]

end DPLattice
