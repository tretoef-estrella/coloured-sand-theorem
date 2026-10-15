module

public import RequestProject.LemmaW.Dual

/-!
# `C25_lemma_W_and_ext.md`: Part W — Lemma 3.2 (Lemma W)

Encodings (namespace `LemmaW`):

* The extension is a short exact sequence `f : Hom N X`, `g : Hom X (delta A l)` (C19's
  `ShortExact`), with `f.toLin`, `g.toLin` weight-preserving (`IsWtPres`) and
  `−l ≤ N.wt i ≤ l` for every `i : N.ι`.
* `δ_0 = e_0` is `Pi.single 0 1 : Fin (l + 1) → A`, the highest weight vector of `Δ_A(l)`.
* "`x` has weight `l`" is `HasWt X l x`, i.e. `pr X l x = x`.
* `sW x : (Fin (l + 1) → A) →ₗ[A] (X.ι → A)` is `z ↦ Σ_r z_r • F^{(r)} x`, so that
  `sW x (δ_r) = F^{(r)} x` (`sW_single`); `sWHom` is the same linear map packaged as a
  `Hom (delta A l) X`.
-/

@[expose] public section

noncomputable section

namespace LemmaW

open DPLattice WeylFilt Doubling Finset

variable {A : Type*} [CommRing A]

/-! ### (K) on a weight vector -/

/-- (W3, auxiliary) Kostant's formula (K) extended linearly to a vector `v` all of whose
coordinates have weight `w`:
`E^{(s)} F^{(r)} v = Σ_{j=0}^{min(r,s)} C(w + s − r, j) · F^{(r−j)} E^{(s−j)} v`. -/
lemma K_vec (M : DPLattice A) {w : ℤ} {v : M.ι → A} (hv : InWt M.wt w v) (r s : ℕ) :
    M.Ed s (M.Fd r v) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (w + s - r) j : ℤ) : A) • M.Fd (r - j) (M.Ed (s - j) v) := by
  have hv' : v = ∑ i, v i • (Pi.single i (1 : A) : M.ι → A) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ i, v i • M.Ed s (M.Fd r (Pi.single i 1)) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (w + s - r) j : ℤ) : A) • (v i • M.Fd (r - j) (M.Ed (s - j)
        (Pi.single i 1))) := by
    intro i
    by_cases hi : M.wt i = w
    · rw [M.isDP.K, hi, Finset.smul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [smul_comm]
    · rw [hv i hi]; simp
  conv_lhs => rw [hv']
  conv_rhs => rw [hv']
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]

/-! ### The section `sW x` -/

/-- (W3) The linear map `sW x : (Fin (l + 1) → A) →ₗ[A] (X.ι → A)`, `z ↦ Σ_r z_r • F^{(r)} x`,
so that `sW x (δ_r) = F^{(r)} x`. -/
def sW {X : DPLattice A} {l : ℕ} (x : X.ι → A) : (Fin (l + 1) → A) →ₗ[A] (X.ι → A) where
  toFun z := ∑ r, z r • X.Fd r x
  map_add' z z' := by simp [add_smul, sum_add_distrib]
  map_smul' c z := by simp [smul_sum, mul_smul]

lemma sW_apply {X : DPLattice A} {l : ℕ} (x : X.ι → A) (z : Fin (l + 1) → A) :
    sW x z = ∑ r, z r • X.Fd r x := rfl

/-- (W3) `sW x (δ_r) = F^{(r)} x`. -/
theorem sW_single {X : DPLattice A} {l : ℕ} (x : X.ι → A) (r : Fin (l + 1)) :
    sW x (Pi.single r 1) = X.Fd r x := by
  rw [sW_apply, Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma sum_ite_fin {V : Type*} [AddCommGroup V] [Module A V] (l n : ℕ) (c : A) (Fx : ℕ → V)
    (h : ∀ m, l < m → Fx m = 0) :
    ∑ m : Fin (l + 1), (if (m : ℕ) = n then c else 0) • Fx m = c • Fx n := by
  by_cases hn : n < l + 1
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro b _ hb
      rw [if_neg, zero_smul]
      intro h'; apply hb; ext; exact h'
    · simp
  · rw [h n (by omega), smul_zero]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg, zero_smul]
    have := m.isLt; omega

/-! ### Computations on `Δ_A(l)` in the basis `Fin (l + 1)` -/

lemma prW_delta_single_zero (l : ℕ) :
    prW (A := A) (weylWt l) (l : ℤ) (Pi.single (0 : Fin (l + 1)) 1) = Pi.single 0 1 := by
  funext m
  rw [prW_apply]
  by_cases hm : m = 0
  · subst hm; simp [weylWt]
  · have : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
    rw [if_neg (by simp only [weylWt]; omega)]
    simp [hm]

lemma deltaF_single_zero (l : ℕ) (r : Fin (l + 1)) :
    deltaF (A := A) l r (Pi.single (0 : Fin (l + 1)) 1) = Pi.single r 1 := by
  funext m
  rw [deltaF_single_apply]
  by_cases hm : m = r
  · subst hm; simp
  · have : (m : ℕ) ≠ (r : ℕ) := fun h => hm (Fin.ext h)
    simp [hm, this]

lemma Hop_weylWt_single (l : ℕ) (r : Fin (l + 1)) :
    Hop (A := A) (weylWt l) (Pi.single r 1) = ((weylWt l r : ℤ) : A) • (Pi.single r 1 : Fin (l + 1) → A) := by
  funext k
  rw [Hop_apply]
  by_cases hk : k = r
  · subst hk; simp
  · simp [hk]

section sWcomm

variable {X : DPLattice A} {l : ℕ} (x : X.ι → A)

lemma sW_deltaF (hF : ∀ r : ℕ, l < r → X.Fd r x = 0) (t : ℕ) (r : Fin (l + 1)) :
    sW x (deltaF l t (Pi.single r 1)) = X.Fd t (sW x (Pi.single r 1)) := by
  rw [sW_single, sW_apply]
  simp_rw [deltaF_single_apply]
  rw [sum_ite_fin l ((r : ℕ) + t) _ (fun m => X.Fd m x) hF]
  have hP := LinearMap.congr_fun (X.isDP.P1_F t r) x
  rw [LinearMap.comp_apply] at hP
  rw [hP, LinearMap.smul_apply, choose_natAdd, add_comm t (r : ℕ)]
  push_cast; rfl

lemma sW_deltaE (hx : HasWt X l x) (hE : ∀ s : ℕ, 1 ≤ s → X.Ed s x = 0)
    (hF : ∀ r : ℕ, l < r → X.Fd r x = 0) (s : ℕ) (r : Fin (l + 1)) :
    sW x (deltaE l s (Pi.single r 1)) = X.Ed s (sW x (Pi.single r 1)) := by
  rw [sW_single, sW_apply]
  have hxw : InWt X.wt l x := (hasWt_iff_inWt X l x).mp hx
  rw [K_vec X hxw]
  simp_rw [deltaE_single_apply]
  have hr := r.isLt
  by_cases hsr : s ≤ (r : ℕ)
  · have hc : ∀ m : Fin (l + 1), ((m : ℕ) + s = r) ↔ ((m : ℕ) = r - s) := fun m => by omega
    simp_rw [hc]
    rw [sum_ite_fin l ((r : ℕ) - s) _ (fun m => X.Fd m x) hF, min_eq_right hsr,
      Finset.sum_eq_single s]
    · rw [Nat.sub_self, X.isDP.P0_E, Module.End.one_apply]
      congr 1
      rw [show (l : ℤ) + s - (r : ℕ) = ((l - r + s : ℕ) : ℤ) by push_cast [hr.le]; omega,
        Ring.choose_natCast]
      push_cast; rfl
    · intro j hj hjs
      simp only [mem_range] at hj
      rw [hE (s - j) (by omega), map_zero, smul_zero]
    · intro h; simp at h
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro j hj
      simp only [mem_range] at hj
      rw [hE (s - j) (by omega), map_zero, smul_zero]
    · intro m _
      rw [if_neg (by omega), zero_smul]

lemma sW_H (hx : HasWt X l x) (r : Fin (l + 1)) :
    sW x (Hop (weylWt l) (Pi.single r 1)) = Hop X.wt (sW x (Pi.single r 1)) := by
  rw [Hop_weylWt_single, map_smul, sW_single]
  have hxw : InWt X.wt l x := (hasWt_iff_inWt X l x).mp hx
  have hw := X.isDP.inWt_Fd r hxw
  funext k
  rw [Hop_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : X.wt k = (l : ℤ) - 2 * ((r : ℕ) : ℤ)
  · rw [hk]; rfl
  · rw [hw k hk, mul_zero, mul_zero]

end sWcomm

/-! ### Part W -/

section partW

variable {l : ℕ} {N X : DPLattice A} {f : Hom N X} {g : Hom X (delta A l)}

lemma delta_wt_bound (l : ℕ) (k : (delta A l).ι) :
    -(l : ℤ) ≤ (delta A l).wt k ∧ (delta A l).wt k ≤ l := by
  change -(l : ℤ) ≤ weylWt l k ∧ weylWt l k ≤ l
  have := (k : Fin (l + 1)).isLt
  simp only [weylWt]; omega

/-- (W1) There is `x : X.ι → A` of weight `l` with `g.toLin x = δ_0`. -/
theorem W1 (hfg : ShortExact f g) (hg : IsWtPres g.toLin) :
    ∃ x : X.ι → A, HasWt X l x ∧ g.toLin x = Pi.single (0 : Fin (l + 1)) 1 := by
  obtain ⟨y, hy⟩ := hfg.surj (Pi.single (0 : Fin (l + 1)) 1)
  refine ⟨pr X l y, hasWt_pr X l y, ?_⟩
  rw [← LinearMap.comp_apply, P2_wtPres hg, LinearMap.comp_apply, hy]
  exact prW_delta_single_zero l

/-- (W2) For every `x` of weight `l`: `X.Ed s x = 0` for `s ≥ 1`, and `X.Fd r x = 0` for
`r > l`. -/
theorem W2 (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) (x : X.ι → A) (hx : HasWt X l x) :
    (∀ s : ℕ, 1 ≤ s → X.Ed s x = 0) ∧ (∀ r : ℕ, l < r → X.Fd r x = 0) := by
  constructor
  · intro s hs
    have h0 := P3 hfg hf hg ((l : ℤ) + 2 * s) (fun i => by have := hN i; omega)
      (fun k => by have := delta_wt_bound (A := A) l k; omega)
    have : pr X ((l : ℤ) + 2 * s) (X.Ed s x) = X.Ed s x := by
      rw [← LinearMap.comp_apply, ← P2_E, LinearMap.comp_apply, hx]
    rw [← this, h0, LinearMap.zero_apply]
  · intro r hr
    have h0 := P3 hfg hf hg ((l : ℤ) - 2 * r) (fun i => by have := hN i; omega)
      (fun k => by have := delta_wt_bound (A := A) l k; omega)
    have : pr X ((l : ℤ) - 2 * r) (X.Fd r x) = X.Fd r x := by
      rw [← LinearMap.comp_apply, ← P2_F, LinearMap.comp_apply, hx]
    rw [← this, h0, LinearMap.zero_apply]

/-- (W3, auxiliary) `sW x` is a morphism `Hom (delta A l) X` as soon as `x` has weight `l`,
`E^{(s)} x = 0` for `s ≥ 1` and `F^{(r)} x = 0` for `r > l`. -/
def sWHom' (x : X.ι → A) (hx : HasWt X l x) (hE : ∀ s : ℕ, 1 ≤ s → X.Ed s x = 0)
    (hF : ∀ r : ℕ, l < r → X.Fd r x = 0) : Hom (delta A l) X where
  toLin := sW x
  comm_F t := ext_single fun r => sW_deltaF x hF t r
  comm_E s := ext_single fun r => sW_deltaE x hx hE hF s r
  comm_H := ext_single fun r => sW_H x hx r

/-- (W3) The morphism `Hom (delta A l) X` with underlying linear map `sW x`, for `x` of weight
`l` (in the setting of Part W). -/
def sWHom (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) (x : X.ι → A) (hx : HasWt X l x) :
    Hom (delta A l) X :=
  sWHom' x hx (W2 hfg hf hg hN x hx).1 (W2 hfg hf hg hN x hx).2

/-- (W3) For `x` as in (W1) (weight `l`, `g.toLin x = δ_0`), the linear map `sW x` with
`sW x (δ_r) = F^{(r)} x` is (the underlying map of) a `Hom (delta A l) X`, and
`Hom.comp g (sW x) = Hom.id (delta A l)`. -/
theorem W3 (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) (x : X.ι → A) (hx : HasWt X l x)
    (hgx : g.toLin x = Pi.single (0 : Fin (l + 1)) 1) :
    (sWHom hfg hf hg hN x hx).toLin = sW x ∧
    (∀ r : Fin (l + 1), sW x (Pi.single r 1) = X.Fd r x) ∧
    Hom.comp g (sWHom hfg hf hg hN x hx) = Hom.id (delta A l) := by
  refine ⟨rfl, fun r => sW_single x r, Hom.ext' ?_⟩
  refine ext_single fun r => ?_
  change g.toLin (sW x (Pi.single r 1)) = Pi.single r 1
  rw [sW_single, ← LinearMap.comp_apply, g.comm_F, LinearMap.comp_apply, hgx]
  exact deltaF_single_zero l r

/-- (W4) **Lemma 3.2 (Lemma W).** Let `f : Hom N X`, `g : Hom X (delta A l)` be short exact, with
`f.toLin`, `g.toLin` weight-preserving and `−l ≤ N.wt i ≤ l` for every `i`. Then the extension
splits: `∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l)`. -/
theorem W4 (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) :
    ∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l) := by
  obtain ⟨x, hx, hgx⟩ := W1 hfg hg
  exact ⟨_, (W3 hfg hf hg hN x hx hgx).2.2⟩

/-- (W5) Over a domain of characteristic zero, (W4) holds without the weight-preservation
hypotheses (they follow from (P1)). -/
theorem W5 [IsDomain A] [CharZero A] (hfg : ShortExact f g)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) :
    ∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l) :=
  W4 hfg (P1 f) (P1 g) hN

end partW

end LemmaW
