module

public import RequestProject.OddSplit.PartD

/-!
# `CSI3_the_split.md`: Part I — (I1) the map `ι` and (I2) its intertwining property

Encodings:

* `PsiData p N r` bundles "a DP-lattice over `ℤ_[p]` with basis `Bool × Fin p × N.ι`, the weights
  `psiWt p N r` of Part D, and `F^{(1)} = psiF p N r`, `E^{(1)} = psiE p N r`": the families
  `Fd`, `Ed`, the axioms `IsDP`, and the two equalities. `L.lat` is the corresponding
  `DPLattice` (its basis type is `Bool × Fin p × N.ι` by definition).
* Part I is stated for `r = s + 1` with `1 ≤ s` and `s + 2 ≤ p` (i.e. `2 ≤ r ≤ p − 1`), and
  `M = L.lat` for some `L : PsiData p N s` (so `M` has the single operators of Part D for
  `r − 1 = s`). `Zs L = Tensor2.tensor (V ℤ_[p]) L.lat` is `Z = V ⊗ M` (basis
  `Fin 2 × (Bool × Fin p × N.ι)`), and `tv e (aV p j n)` is `b̂_e ⊗ A'_j n`.
* `alphaL p N s n = α(n) = b̂_0 ⊗ A'_0 n − p·b̂_1 ⊗ C'_{p−r}(En)` and
  `gammaL p N s w n = γ(n) = b̂_0 ⊗ C'_1 n + b̂_1 ⊗ A'_{r−1} n − (pw + p − r)·b̂_1 ⊗ C'_0 n`
  (for `n` of weight `w`), as linear maps of `n`.
* `iota L` is `ι`: the linear extension of `ι(A_j e_i) = F^j α(e_i)`,
  `ι(C_j e_i) = F^j γ(e_i)` (`F = Z.Fd 1`, `w = w_i`); on vectors: `iota_aV`, `iota_cV`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- Part I: a DP-lattice over `ℤ_[p]` with basis `Bool × Fin p × N.ι`, the weights of Part D for
`r`, and single operators `psiF p N r`, `psiE p N r`. -/
structure PsiData (r : ℕ) where
  /-- the divided powers `F^{(k)}` -/
  Fd : ℕ → Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p])
  /-- the divided powers `E^{(k)}` -/
  Ed : ℕ → Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p])
  isDP : IsDP (psiWt p N r) Fd Ed
  F1 : Fd 1 = psiF p N r
  E1 : Ed 1 = psiE p N r

variable {p N}

/-- Part I: the DP-lattice of a `PsiData`. -/
def PsiData.lat {r : ℕ} (L : PsiData p N r) : DPLattice ℤ_[p] :=
  ⟨Bool × Fin p × N.ι, psiWt p N r, L.Fd, L.Ed, L.isDP⟩

/-- Part I: `Z = V ⊗ M` for `M = L.lat`. -/
abbrev Zs {s : ℕ} (L : PsiData p N s) : DPLattice ℤ_[p] := Tensor2.tensor (V ℤ_[p]) L.lat

/-- Part I: the operator `F = Z.Fd 1` of `Z = V ⊗ M`, on `Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]`. -/
def ZF {s : ℕ} (L : PsiData p N s) : Module.End ℤ_[p] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  (Zs L).Fd 1

/-- Part I: the operator `E = Z.Ed 1` of `Z = V ⊗ M`. -/
def ZE {s : ℕ} (L : PsiData p N s) : Module.End ℤ_[p] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  (Zs L).Ed 1

variable (p N)

/-- (I1) `α(n) = b̂_0 ⊗ A'_0 n − p·b̂_1 ⊗ C'_{p−r}(En)`, `r = s + 1`. -/
def alphaL (s : ℕ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  tv 0 ∘ₗ aV p 0 - (p : ℤ_[p]) • (tv 1 ∘ₗ cV p (p - (s + 1)) ∘ₗ N.Ed 1)

/-- (I1) `γ(n) = b̂_0 ⊗ C'_1 n + b̂_1 ⊗ A'_{r−1} n − (pw + p − r)·b̂_1 ⊗ C'_0 n`, `r = s + 1`,
for `n` of weight `w`. -/
def gammaL (s : ℕ) (w : ℤ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  tv 0 ∘ₗ cV p 1 + tv 1 ∘ₗ aV p s - ((p : ℤ_[p]) * w + p - (s + 1)) • (tv 1 ∘ₗ cV p 0)

variable {p N}

/-- (I1) `ι` on the basis vector `(b, j, i)`. -/
def iotaB {s : ℕ} (L : PsiData p N s) (x : Bool × Fin p × N.ι) : Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p] :=
  (ZF L ^ (x.2.1 : ℕ))
    (if x.1 then gammaL p N s (N.wt x.2.2) (Pi.single x.2.2 1) else alphaL p N s (Pi.single x.2.2 1))

/-- (I1) the map `ι : Ψ_r(N) → V ⊗ M`, `ι(A_j n) = F^j α(n)`, `ι(C_j n) = F^j γ(n)`. -/
def iota {s : ℕ} (L : PsiData p N s) :
    (Bool × Fin p × N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Bool × Fin p × N.ι)).constr ℤ_[p] (iotaB L)

section basic

variable {s : ℕ} (L : PsiData p N s)

lemma iota_single (x : Bool × Fin p × N.ι) : iota L (Pi.single x 1) = iotaB L x := by
  rw [iota, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

/-- (I1) `ι(A_j n) = F^j α(n)`. -/
lemma iota_aV {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    iota L (aV p j n) = (ZF L ^ j) (alphaL p N s n) := by
  have : iota L ∘ₗ aV p j = (ZF L ^ j) ∘ₗ alphaL p N s := ext_single fun i => by
    rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_false,
      iota_single]; rfl
  exact LinearMap.congr_fun this n

/-- (I1) `ι(C_j n) = F^j γ(n)` for `n` of weight `w`. -/
lemma iota_cV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    iota L (cV p j n) = (ZF L ^ j) (gammaL p N s w n) :=
  Doubling.eq_on_inWt (iota L ∘ₗ cV p j) ((ZF L ^ j) ∘ₗ gammaL p N s w)
    (fun i hi => by
      rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_true,
        iota_single, iotaB]
      simp only [hi]; rfl) hn

lemma lat_Fd1 : L.lat.Fd 1 = psiF p N s := L.F1
lemma lat_Ed1 : L.lat.Ed 1 = psiE p N s := L.E1

lemma Zs_F_tv0 (x : Bool × Fin p × N.ι → ℤ_[p]) :
    ZF L (tv 0 x) = tv 1 x + tv 0 (psiF p N s x) := by
  have h := tensorV_Fd1_tv0 L.lat x
  rw [lat_Fd1] at h
  exact h

lemma Zs_F_tv1 (x : Bool × Fin p × N.ι → ℤ_[p]) :
    ZF L (tv 1 x) = tv 1 (psiF p N s x) := by
  have h := tensorV_Fd1_tv1 L.lat x
  rw [lat_Fd1] at h
  exact h

lemma Zs_E_tv0 (x : Bool × Fin p × N.ι → ℤ_[p]) :
    ZE L (tv 0 x) = tv 0 (psiE p N s x) := by
  have h := tensorV_Ed1_tv0 L.lat x
  rw [lat_Ed1] at h
  exact h

lemma Zs_E_tv1 (x : Bool × Fin p × N.ι → ℤ_[p]) :
    ZE L (tv 1 x) = tv 0 x + tv 1 (psiE p N s x) := by
  have h := tensorV_Ed1_tv1 L.lat x
  rw [lat_Ed1] at h
  exact h

lemma Zs_Fpow_tv0 (k : ℕ) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    (ZF L ^ k) (tv 0 x) =
      tv 0 ((psiF p N s ^ k) x) + (k : ℤ_[p]) • tv 1 ((psiF p N s ^ (k - 1)) x) := by
  have h := tensorV_Fpow_tv0 L.lat k x
  rw [lat_Fd1] at h
  exact h

lemma Zs_Fpow_tv1 (k : ℕ) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    (ZF L ^ k) (tv 1 x) = tv 1 ((psiF p N s ^ k) x) := by
  have h := tensorV_Fpow_tv1 L.lat k x
  rw [lat_Fd1] at h
  exact h

end basic

/-! ### Powers of `psiF` -/

section powers

variable (s : ℕ)

lemma psiF_pow_aV {j k : ℕ} (h : j + k < p) (n : N.ι → ℤ_[p]) :
    (psiF p N s ^ k) (aV p j n) = aV p (j + k) n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih (by omega), psiF_A_lt s (by omega)]; rfl

lemma psiF_pow_cV {j k : ℕ} (h : j + k < p) (n : N.ι → ℤ_[p]) :
    (psiF p N s ^ k) (cV p j n) = cV p (j + k) n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih (by omega), psiF_C_lt s (by omega)]; rfl

/-- `F^k C_j m = −p·C_t(Fm)` when `j + k = p + t`, `t < p`. -/
lemma psiF_pow_cV_wrap {j k t : ℕ} (hj : j < p) (h : j + k = p + t) (ht : t < p)
    (n : N.ι → ℤ_[p]) : (psiF p N s ^ k) (cV p j n) = (-(p : ℤ_[p])) • cV p t (N.Fd 1 n) := by
  rw [show k = t + (1 + (p - 1 - j)) by omega, pow_add, pow_add, Module.End.mul_apply,
    Module.End.mul_apply, psiF_pow_cV s (j := j) (k := p - 1 - j) (by omega), pow_one,
    show j + (p - 1 - j) = p - 1 by omega, psiF_C_last, map_smul,
    psiF_pow_cV s (j := 0) (k := t) (by omega), zero_add]

/-- `F^k A_j m = −p·A_t(Fm) + p·F^t C_{p−s}(m)` when `j + k = p + t`, `t < p`. -/
lemma psiF_pow_aV_wrap {j k t : ℕ} (hj : j < p) (h : j + k = p + t) (ht : t < p)
    (n : N.ι → ℤ_[p]) : (psiF p N s ^ k) (aV p j n) =
      (-(p : ℤ_[p])) • aV p t (N.Fd 1 n) + (p : ℤ_[p]) • (psiF p N s ^ t) (cV p (p - s) n) := by
  rw [show k = t + (1 + (p - 1 - j)) by omega, pow_add, pow_add, Module.End.mul_apply,
    Module.End.mul_apply, psiF_pow_aV s (j := j) (k := p - 1 - j) (by omega), pow_one,
    show j + (p - 1 - j) = p - 1 by omega, psiF_A_last, map_add, map_smul, map_smul,
    psiF_pow_aV s (j := 0) (k := t) (by omega), zero_add]

end powers


/-! ### (I2) the wrap computations -/

section wrap

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I2) `F^p γ(n) = −p·γ(Fn)` in `V ⊗ M` (`γ` for the weight `w` of `n`, resp. `w − 2`). -/
lemma Zs_Fpow_p_gamma (w : ℤ) (n : N.ι → ℤ_[p]) :
    (ZF L ^ p) (gammaL p N s w n) = (-(p : ℤ_[p])) • gammaL p N s (w - 2) (N.Fd 1 n) := by
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv1,
    psiF_pow_cV_wrap s (j := 1) (k := p) (t := 1) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap s (j := 1) (k := p - 1) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_aV_wrap s (j := s) (k := p) (t := s) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap s (j := p - s) (k := s) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap s (j := 0) (k := p) (t := 0) (by omega) (by omega) (by omega)]
  simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, smul_sub]
  push_cast
  module

/-- (I2) `F^p α(n) = −p·α(Fn) + p·F^{p−r} γ(n)` in `V ⊗ M`, for `n` of weight `w`. -/
lemma Zs_Fpow_p_alpha {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    (ZF L ^ p) (alphaL p N s n) = (-(p : ℤ_[p])) • alphaL p N s (N.Fd 1 n) +
      (p : ℤ_[p]) • (ZF L ^ (p - (s + 1))) (gammaL p N s w n) := by
  have hc : ((p - (s + 1) : ℕ) : ℤ_[p]) = p - (s + 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [alphaL, gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv1,
    psiF_pow_aV_wrap s (j := 0) (k := p) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_aV s (j := 0) (k := p - 1) (by omega),
    psiF_pow_cV_wrap s (j := p - (s + 1)) (k := p) (t := p - (s + 1)) (by omega) (by omega)
      (by omega),
    psiF_pow_cV s (j := 1) (k := p - (s + 1)) (by omega),
    psiF_pow_cV s (j := 1) (k := p - (s + 1) - 1) (by omega),
    psiF_pow_aV s (j := s) (k := p - (s + 1)) (by omega),
    psiF_pow_cV s (j := 0) (k := p - (s + 1)) (by omega), lie_N hn, pow_zero,
    Module.End.one_apply, show 1 + (p - (s + 1)) = p - s by omega,
    show 1 + (p - (s + 1) - 1) = p - (s + 1) by omega, show s + (p - (s + 1)) = p - 1 by omega,
    zero_add, zero_add]
  simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, smul_sub, hc]
  module

end wrap


/-! ### (I2) `ι` and `F` -/

section intertwine

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I2) `ι ∘ psiF p r N = Z.Fd 1 ∘ ι` (`r = s + 1`). -/
theorem iota_F : iota L ∘ₗ psiF p N (s + 1) = ZF L ∘ₗ iota L := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_A_lt (s + 1) hl, iota_aV L hl, iota_aV L hj, pow_succ', Module.End.mul_apply]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_A_last, map_add, map_smul, map_smul, iota_aV L (by omega),
        iota_cV L (by omega) hn, iota_aV L hj, ← Module.End.mul_apply, ← pow_succ',
        show p - 1 + 1 = p by omega, Zs_Fpow_p_alpha L hs1 hsp hn, pow_zero,
        Module.End.one_apply]
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_C_lt (s + 1) hl, iota_cV L hl hn, iota_cV L hj hn, pow_succ',
        Module.End.mul_apply]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_C_last, map_smul, iota_cV L (by omega) (inWt_F hn), iota_cV L hj hn,
        ← Module.End.mul_apply, ← pow_succ', show p - 1 + 1 = p by omega,
        Zs_Fpow_p_gamma L hs1 hsp, pow_zero, Module.End.one_apply]

end intertwine

/-! ### (I2) weights -/

/-- A linear map sending basis vectors of weight `μ` to vectors of weight `μ` commutes with the
weight operators. -/
lemma comm_Hop_of_wtPres {A : Type*} [CommRing A] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {wt : ι → ℤ} {wt' : κ → ℤ} (f : (ι → A) →ₗ[A] (κ → A))
    (hf : ∀ i j, wt i ≠ wt' j → f (Pi.single i 1) j = 0) : f ∘ₗ Hop wt = Hop wt' ∘ₗ f := by
  refine ext_single fun i => ?_
  funext j
  have hs : Hop (A := A) wt (Pi.single i 1) = (wt i : A) • (Pi.single i 1 : ι → A) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp only [LinearMap.comp_apply, hs, map_smul, Pi.smul_apply, smul_eq_mul, Hop_apply]
  by_cases h : wt i = wt' j
  · rw [h]
  · rw [hf i j h, mul_zero, mul_zero]

section weights

variable {s : ℕ} (L : PsiData p N s)

lemma inWt_ZFpow (k : ℕ) {μ : ℤ} {v : Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]}
    (hv : InWt (Zs L).wt μ v) : InWt (Zs L).wt (μ - 2 * k) ((ZF L ^ k) v) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := (Zs L).isDP.inWt_Fd 1 ih
    exact Doubling.inWt_congr (by push_cast; ring) this

variable (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

omit hs1 in
lemma inWt_alpha {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    InWt (Zs L).wt (p * w + p - 1 + (s + 1 : ℕ)) (alphaL p N s n) := by
  simp only [alphaL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  refine inWt_sub' (Doubling.inWt_congr ?_ (inWt_tv L.lat 0 (inWt_aV s 0 hn)))
    (Doubling.inWt_smul _ (Doubling.inWt_congr ?_ (inWt_tv L.lat 1
      (inWt_cV s (p - (s + 1)) (inWt_E hn)))))
  · simp; ring
  · push_cast [Nat.cast_sub (show s + 1 ≤ p by omega)]; simp; ring

omit hs1 hsp in
lemma inWt_gamma {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    InWt (Zs L).wt (p * w + p - 1 - (s + 1 : ℕ)) (gammaL p N s w n) := by
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply]
  refine inWt_sub' (Doubling.inWt_add (Doubling.inWt_congr ?_ (inWt_tv L.lat 0 (inWt_cV s 1 hn)))
    (Doubling.inWt_congr ?_ (inWt_tv L.lat 1 (inWt_aV s s hn))))
    (Doubling.inWt_smul _ (Doubling.inWt_congr ?_ (inWt_tv L.lat 1 (inWt_cV s 0 hn))))
  · simp; ring
  · simp; ring
  · simp; ring

/-- (I2) `ι` is weight-preserving: `ι(δ_x)` has weight `psiWt p N r x`. -/
lemma iota_single_inWt (x : Bool × Fin p × N.ι) :
    InWt (Zs L).wt (psiWt p N (s + 1) x) (iota L (Pi.single x 1)) := by
  obtain ⟨b, ⟨j, hj⟩, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  cases b
  · rw [single_false, iota_aV L hj]
    exact Doubling.inWt_congr (by simp [psiWt]) (inWt_ZFpow L j (inWt_alpha L hsp hn))
  · rw [single_true, iota_cV L hj hn]
    exact Doubling.inWt_congr (by simp [psiWt]; ring) (inWt_ZFpow L j (inWt_gamma L hn))

/-- (I2) `ι` is weight-preserving (in the form used by C29's `Filt.sub`). -/
lemma iota_wtPres (x : Bool × Fin p × N.ι) (z : Fin 2 × (Bool × Fin p × N.ι))
    (h : psiWt p N (s + 1) x ≠ (Zs L).wt z) : iota L (Pi.single x 1) z = 0 :=
  iota_single_inWt L hs1 hsp x z (Ne.symm h)

/-- (I2) `ι ∘ H = H ∘ ι`. -/
lemma iota_H : iota L ∘ₗ Hop (psiWt p N (s + 1)) = H (Zs L) ∘ₗ iota L :=
  comm_Hop_of_wtPres (iota L) (iota_wtPres L hs1 hsp)

end weights

end ColouredSand.OddTwist
