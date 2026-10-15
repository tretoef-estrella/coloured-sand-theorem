module

public import RequestProject.TiltP.Tilt

/-!
# Weyl equals dual Weyl for the simple weights (CSG3, Part C, (C1)–(C2))

## Encoding

* `delta A l` (`F^{(t)} e_r = C(r + t, t) e_{r+t}`, `E^{(s)} e_r = C(l − r + s, s) e_{r−s}`) and
  `nabla A l` (`F^{(t)} w_r = C(l − r, t) w_{r+t}`, `E^{(s)} w_r = C(r, s) w_{r−s}`) are those of
  this project (C18).  With these conventions the isomorphism is `e_r ↦ C(l, r) w_r`
  (`deltaToNabla`, the diagonal map `v ↦ (r ↦ C(l, r) v r)`); its inverse is
  `w_r ↦ C(l, r)⁻¹ e_r`.
* (C1) `C1`: for every commutative ring `A` and every `l` such that every `C(l, i)` (`i ≤ l`) is a
  unit of `A`, `Nonempty (Iso (delta A l) (nabla A l))`.
* (C2) `C2_units`: for simple `l` (`IsSimpleWt p l`: `l ≤ p − 1`, or `p ∣ l + 1` and
  `l ≤ p² − 1`), every `C(l, i)`, `i ≤ l`, is a unit of `ℤ_[p]` (Lucas' theorem); `C2` gives
  `Nonempty (Iso (delta ℤ_[p] l) (nabla ℤ_[p] l))`.  (`p ≠ 2` is not needed.)
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Finset

section C1

variable {A : Type*} [CommRing A]

/-- The diagonal linear map `v ↦ (r ↦ d r * v r)`. -/
def diagL {ι : Type*} (d : ι → A) : (ι → A) →ₗ[A] (ι → A) where
  toFun v r := d r * v r
  map_add' v w := by funext r; simp [mul_add]
  map_smul' c v := by funext r; simp; ring

@[simp] lemma diagL_apply {ι : Type*} (d : ι → A) (v : ι → A) (r : ι) :
    diagL d v r = d r * v r := rfl

lemma diagL_single {ι : Type*} [DecidableEq ι] (d : ι → A) (r : ι) :
    diagL d (Pi.single r 1) = d r • (Pi.single r 1 : ι → A) := by
  funext k; by_cases hk : k = r
  · subst hk; simp
  · simp [hk]

lemma diagL_comp {ι : Type*} (d d' : ι → A) : diagL d ∘ₗ diagL d' = diagL (fun r => d r * d' r) := by
  refine LinearMap.ext fun v => funext fun r => ?_
  simp [mul_assoc]

/-- The binomial identity behind `F`: `C(l, r + t) C(r + t, t) = C(l, r) C(l − r, t)`. -/
lemma choose_F_id (l r t : ℕ) :
    l.choose (r + t) * (r + t).choose t = l.choose r * (l - r).choose t := by
  rw [← Nat.choose_symm_add, Nat.choose_mul (Nat.le_add_right r t), Nat.add_sub_cancel_left]

/-- The binomial identity behind `E`: for `m + s = r`, `C(l, m) C(l − r + s, s) = C(l, r) C(r, s)`.
-/
lemma choose_E_id (l m s : ℕ) (hr : m + s ≤ l) :
    l.choose m * (l - (m + s) + s).choose s = l.choose (m + s) * (m + s).choose s := by
  rw [← Nat.choose_symm_add (a := m), Nat.choose_mul (Nat.le_add_right m s),
    Nat.add_sub_cancel_left, show l - (m + s) + s = l - m by omega]

variable (A) in
/-- (C1) The morphism `Δ(l) → ∇(l)`, `e_r ↦ C(l, r) w_r`. -/
def deltaToNabla (l : ℕ) : Hom (delta A l) (nabla A l) where
  toLin := diagL fun r : Fin (l + 1) => ((l.choose r : ℕ) : A)
  comm_F t := by
    refine ext_single fun (r : Fin (l + 1)) => funext fun (m : Fin (l + 1)) => ?_
    show ((l.choose m : ℕ) : A) * deltaF l t (Pi.single r 1) m =
      nablaF l t (diagL (fun r : Fin (l + 1) => ((l.choose r : ℕ) : A)) (Pi.single r 1)) m
    rw [diagL_single, map_smul, Pi.smul_apply, deltaF_single_apply, nablaF_single_apply,
      smul_eq_mul]
    split_ifs with h
    · rw [h]; simpa only [Nat.cast_mul] using congrArg (Nat.cast (R := A)) (choose_F_id l r t)
    · simp
  comm_E s := by
    refine ext_single fun (r : Fin (l + 1)) => funext fun (m : Fin (l + 1)) => ?_
    show ((l.choose m : ℕ) : A) * deltaE l s (Pi.single r 1) m =
      nablaE l s (diagL (fun r : Fin (l + 1) => ((l.choose r : ℕ) : A)) (Pi.single r 1)) m
    rw [diagL_single, map_smul, Pi.smul_apply, deltaE_single_apply, nablaE_single_apply,
      smul_eq_mul]
    split_ifs with h
    · rw [← h]
      have := r.2
      simpa only [Nat.cast_mul] using congrArg (Nat.cast (R := A)) (choose_E_id l m s (by omega))
    · simp
  comm_H := comm_H_of_wtPres _ fun (i : Fin (l + 1)) (j : Fin (l + 1)) hij => by
    show ((l.choose (j : ℕ) : ℕ) : A) * (Pi.single i (1 : A) : Fin (l + 1) → A) j = 0
    rw [Pi.single_apply, if_neg (by rintro rfl; exact hij rfl), mul_zero]

/-- **(C1)** If every `C(l, i)` (`i ≤ l`) is a unit of the commutative ring `A`, then
`Δ_A(l) ≅ ∇_A(l)` (via `e_r ↦ C(l, r) w_r`). -/
theorem C1 (l : ℕ) (hu : ∀ i ≤ l, IsUnit ((l.choose i : ℕ) : A)) :
    Nonempty (Iso (delta A l) (nabla A l)) := by
  have hu' : ∀ r : Fin (l + 1), IsUnit ((l.choose r : ℕ) : A) :=
    fun r => hu r (Nat.le_of_lt_succ r.2)
  refine ⟨Iso.ofInverse (deltaToNabla A l) (diagL fun r => ↑(hu' r).unit⁻¹) ?_ ?_⟩
  · show diagL _ ∘ₗ diagL _ = _
    rw [diagL_comp]
    refine LinearMap.ext fun v => funext fun r => ?_
    simp [IsUnit.val_inv_mul]
  · show diagL _ ∘ₗ diagL _ = _
    rw [diagL_comp]
    refine LinearMap.ext fun v => funext fun r => ?_
    simp [IsUnit.mul_val_inv]

end C1

section C2

/-- `p ∤ C(m, j)` for `m < p`. -/
lemma not_dvd_choose_of_lt {p m j : ℕ} (hp : p.Prime) (hm : m < p) (hj : j ≤ m) :
    ¬ p ∣ m.choose j := by
  intro h
  have h1 : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hj, mul_assoc]
    exact dvd_mul_of_dvd_left h _
  rw [hp.dvd_factorial] at h1
  omega

/-- (C2, arithmetic) For simple `l`, `p ∤ C(l, i)` for every `i ≤ l` (Lucas). -/
theorem C2_not_dvd {p l : ℕ} (hp : p.Prime) (hl : IsSimpleWt p l) {i : ℕ} (hi : i ≤ l) :
    ¬ p ∣ l.choose i := by
  have hp2 := hp.two_le
  rcases hl with hl | ⟨hdvd, hle⟩
  · exact not_dvd_choose_of_lt hp (by omega) hi
  · haveI := Fact.mk hp
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk
      · exact h
    have hl' : l = (p - 1) + p * (k - 1) := by
      have : p * k = p * (k - 1) + p := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
      omega
    have hmod : l % p = p - 1 := by
      rw [hl', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : l / p = k - 1 := by
      rw [hl', Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
    have hkp : k ≤ p := by
      have h1 : p * k ≤ p * p := by
        have : p ^ 2 = p * p := by ring
        omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    rw [(Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)).dvd_iff dvd_rfl,
      hp.dvd_mul, hmod, hdiv]
    rintro (h | h)
    · exact not_dvd_choose_of_lt hp (by omega) (by have := Nat.mod_lt i (by omega : p > 0); omega) h
    · exact not_dvd_choose_of_lt hp (by omega)
        (by rw [← hdiv]; exact Nat.div_le_div_right hi) h

/-- **(C2)** For simple `l`, every `C(l, i)` (`i ≤ l`) is a unit of `ℤ_[p]`. -/
theorem C2_units (p : ℕ) [Fact p.Prime] {l : ℕ} (hl : IsSimpleWt p l) :
    ∀ i ≤ l, IsUnit ((l.choose i : ℕ) : ℤ_[p]) := by
  intro i hi
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact C2_not_dvd Fact.out hl hi

/-- **(C2)** For every simple `l`, `Δ_{ℤ_[p]}(l) ≅ ∇_{ℤ_[p]}(l)`. -/
theorem C2 (p : ℕ) [Fact p.Prime] {l : ℕ} (hl : IsSimpleWt p l) :
    Nonempty (Iso (delta ℤ_[p] l) (nabla ℤ_[p] l)) :=
  C1 l (C2_units p hl)

end C2

end ColouredSand.TiltP
