module

public import RequestProject.Blocks.Segment

/-!
# Chains whose links are all `ϖ · unit` (CSG1, §3 "Elimination", the `p I_{2a}` step)

After contracting the unit links (`RequestProject/Blocks/Segment.lean`), the reduced chains of
§3 of `CSG1_lemma_8_the_blocks.md` have relations `p^{α_t} g_t + p g_{t+1}` (up to units).
The paper divides by `p` and clears the unit links of `M'`, splitting off `p I`.  Here this
is done by an explicit change of generators: with
`g'_{t+1} = w_t g_{t+1} + P_t g_t` (where the link is `ϖ P_t g_t + ϖ w_t g_{t+1}`),
the link becomes `ϖ g'_{t+1}`, and `g_t` is rewritten in terms of `g_0` and the `g'`.

## Encoding

* `ϖ : R` is the element by which all links are divisible (`p` in the application).
* `pcCoef P w t = ∏_{s<t} (−P_s / w_s)` (the coefficient of `g_0` in `g_t`);
  `pcImg t ∈ R^a × R` is the image of `g_t` (coordinates `g'_1,…,g'_a` and `g_0`).
* `piSpan a ϖ = (ϖ R)^a ⊆ R^a`, whose quotient is `(R ⧸ ϖ)^a`.
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

variable {R : Type*} [CommRing R]

/-- `κ_t = ∏_{s<t} (−P_s / w_s)`. -/
noncomputable def pcCoef (P w : ℕ → R) : ℕ → R
  | 0 => 1
  | t + 1 => -(P t) * Ring.inverse (w t) * pcCoef P w t

/-- The image of `g_t` in `R^a × R` (new generators `g'_1, …, g'_a` and `g_0`). -/
noncomputable def pcImg (a : ℕ) (P w : ℕ → R) : ℕ → (Fin a → R) × R
  | 0 => (0, 1)
  | t + 1 => Ring.inverse (w t) • ((ev t : Fin a → R), (0 : R)) -
      (P t * Ring.inverse (w t)) • pcImg a P w t

/-- The change of generators `R^{a+1} → R^a × R`. -/
noncomputable def pcPi (a : ℕ) (P w : ℕ → R) : (Fin (a + 1) → R) →ₗ[R] (Fin a → R) × R :=
  linOfFun (pcImg a P w)

/-- Its inverse. -/
noncomputable def pcSig (a : ℕ) (P w : ℕ → R) : (Fin a → R) × R →ₗ[R] (Fin (a + 1) → R) :=
  (linOfFun (fun s => w s • (ev (s + 1) : Fin (a + 1) → R) + P s • ev s)).coprod
    (LinearMap.toSpanSingleton R _ (ev 0))

/-- The submodule `(ϖ R)^a` of `R^a`. -/
def piSpan (a : ℕ) (ϖ : R) : Submodule R (Fin a → R) :=
  Submodule.pi Set.univ (fun _ => (Ideal.span {ϖ} : Submodule R R))

variable {a : ℕ} {P w : ℕ → R}

lemma pcImg_snd (t : ℕ) : (pcImg a P w t).2 = pcCoef P w t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [pcImg, pcCoef, ih]

lemma pcPi_ev {j : ℕ} (hj : j ≤ a) : pcPi a P w (ev j) = pcImg a P w j := by
  unfold pcPi; rw [linOfFun_ev _ (by omega)]

lemma pcSig_ev {s : ℕ} (hs : s < a) :
    pcSig a P w (ev s, 0) = w s • (ev (s + 1) : Fin (a + 1) → R) + P s • ev s := by
  simp [pcSig, linOfFun_ev _ hs]

lemma pcSig_one (r : R) : pcSig a P w (0, r) = r • (ev 0 : Fin (a + 1) → R) := by
  simp [pcSig]

lemma pcPi_pcSig (hw : ∀ t < a, IsUnit (w t)) (y : (Fin a → R) × R) :
    pcPi a P w (pcSig a P w y) = y := by
  have : (pcPi a P w).comp (pcSig a P w) = LinearMap.id := by
    apply LinearMap.prod_ext
    · apply ext_ev
      intro s hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
        LinearMap.id_apply]
      rw [pcSig_ev hs, map_add, map_smul, map_smul, pcPi_ev (by omega), pcPi_ev (by omega),
        pcImg]
      have h1 : w s * Ring.inverse (w s) = 1 := Ring.mul_inverse_cancel _ (hw s hs)
      linear_combination (norm := module) h1 • ((ev s : Fin a → R), (0 : R)) -
        (P s * h1) • pcImg a P w s
    · apply LinearMap.ext_ring
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [pcSig_one, one_smul, pcPi_ev (Nat.zero_le a)]
      rfl
  exact congrArg (fun f => f y) this

lemma pcSig_pcImg (hw : ∀ t < a, IsUnit (w t)) {j : ℕ} (hj : j ≤ a) :
    pcSig a P w (pcImg a P w j) = ev j := by
  induction j with
  | zero => simp [pcImg, pcSig_one]
  | succ t ih =>
    rw [pcImg]
    simp only [map_sub, map_smul]
    rw [pcSig_ev (by omega), ih (by omega)]
    have h1 : Ring.inverse (w t) * w t = 1 := Ring.inverse_mul_cancel _ (hw t (by omega))
    linear_combination (norm := module) h1 • (ev (t + 1) : Fin (a + 1) → R)

lemma pcSig_pcPi (hw : ∀ t < a, IsUnit (w t)) (x : Fin (a + 1) → R) :
    pcSig a P w (pcPi a P w x) = x := by
  have : (pcSig a P w).comp (pcPi a P w) = LinearMap.id := by
    apply ext_ev
    intro j hj
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    rw [pcPi_ev (by omega), pcSig_pcImg hw (by omega)]
  exact congrArg (fun f => f x) this

lemma pcPi_link (hw : ∀ t < a, IsUnit (w t)) (ϖ : R) {t : ℕ} (ht : t < a) :
    pcPi a P w ((ϖ * P t) • ev t + (ϖ * w t) • ev (t + 1)) =
      ϖ • ((ev t : Fin a → R), (0 : R)) := by
  rw [map_add, map_smul, map_smul, pcPi_ev (by omega), pcPi_ev (by omega), pcImg]
  have h1 : w t * Ring.inverse (w t) = 1 := Ring.mul_inverse_cancel _ (hw t ht)
  linear_combination (norm := module) (ϖ * h1) • ((ev t : Fin a → R), (0 : R)) -
    (ϖ * P t * h1) • pcImg a P w t

lemma smul_ev_mem_piSpan (ϖ : R) (t : ℕ) : ϖ • (ev t : Fin a → R) ∈ piSpan a ϖ := by
  intro i _
  simp only [Pi.smul_apply, ev_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs
  · exact Ideal.subset_span rfl
  · exact zero_mem _

lemma smul_mem_piSpan {ϖ x : R} (hx : ϖ ∣ x) (v : Fin a → R) : x • v ∈ piSpan a ϖ := by
  intro i _
  obtain ⟨c, rfl⟩ := hx
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma piSpan_le_span (ϖ : R) :
    piSpan a ϖ ≤ span R (Set.range fun t : Fin a => ϖ • (ev t : Fin a → R)) := by
  intro z hz
  have hx : z = ∑ t : Fin a, z t • (ev t : Fin a → R) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, ev_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg]; intro h'; exact hb (Fin.ext h'.symm)
    · simp
  rw [hx]
  refine Submodule.sum_mem _ (fun t _ => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hz t (Set.mem_univ _))
  rw [← hc, ← smul_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨t, rfl⟩)

/-- **The `ϖ`-chain lemma (one chain).**  If all links of a chain on `R^{a+1}` are of the
form `ϖ P_t e_t + ϖ w_t e_{t+1}` with `w_t` units, and `ϖ ∣ D_a`, then its cokernel is
`(R ⧸ ϖ)^a × R ⧸ (D_a κ_a)`, `κ_a = ∏_{t<a} (−P_t/w_t)`. -/
noncomputable def pchainEquiv (ϖ : R) (D S : ℕ → R) (hD : ∀ t < a, D t = ϖ * P t)
    (hS : ∀ t < a, S t = ϖ * w t) (hw : ∀ t < a, IsUnit (w t)) (hDa : ϖ ∣ D a) :
    ((Fin (a + 1) → R) ⧸ chainRel a D S) ≃ₗ[R]
      ((Fin a → R) ⧸ piSpan a ϖ) × (R ⧸ (Ideal.span {D a * pcCoef P w a} : Submodule R R)) := by
  refine (quotEquivOfSection _ ((piSpan a ϖ).prod (Ideal.span {D a * pcCoef P w a}))
    (pcPi a P w) (pcSig a P w) (pcPi_pcSig hw) (fun v => by simp [pcSig_pcPi hw]) ?_).trans
    (quotProdEquiv _ _)
  have hcol : ∀ t : Fin (a + 1), pcPi a P w (chainCol a D S t) =
      if (t : ℕ) < a then ϖ • ((ev t : Fin a → R), (0 : R))
      else (D a • (pcImg a P w a).1, D a * pcCoef P w a) := by
    intro t
    split_ifs with ht
    · rw [chainCol, hD t ht, hS t ht, pcPi_link hw ϖ ht]
    · have : (t : ℕ) = a := by omega
      rw [chainCol, this, ev_eq_zero (show a + 1 ≤ a + 1 from le_rfl), smul_zero, add_zero,
        map_smul, pcPi_ev le_rfl]
      ext <;> simp [pcImg_snd]
  rw [chainRel, map_span_range]
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨t, rfl⟩
    simp only [Function.comp_apply, hcol]
    split_ifs
    · rw [Prod.smul_mk, smul_zero]; exact ⟨smul_ev_mem_piSpan ϖ _, zero_mem _⟩
    · exact ⟨smul_mem_piSpan hDa _, Ideal.subset_span rfl⟩
  · rintro ⟨y, r⟩ ⟨hy, hr⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : ((y - (c * D a) • (pcImg a P w a).1, (0 : R)) : (Fin a → R) × R) ∈
        span R (Set.range (pcPi a P w ∘ fun t : Fin (a + 1) => chainCol a D S t)) := by
      have hy' : y - (c * D a) • (pcImg a P w a).1 ∈ piSpan a ϖ :=
        sub_mem hy (smul_mem_piSpan (dvd_mul_of_dvd_right hDa c) _)
      have := piSpan_le_span ϖ hy'
      have hmap : span R (Set.range fun t : Fin a => ϖ • (ev t : Fin a → R)) ≤
          (span R (Set.range (pcPi a P w ∘ fun t : Fin (a + 1) => chainCol a D S t))).comap
            (LinearMap.inl R _ _) := by
        rw [span_le]
        rintro _ ⟨t, rfl⟩
        refine subset_span ⟨⟨t, by omega⟩, ?_⟩
        rw [Function.comp_apply, hcol, if_pos t.2]
        simp
      exact hmap this
    have h2 : ((c * D a) • (pcImg a P w a).1, c * (D a * pcCoef P w a)) ∈
        span R (Set.range (pcPi a P w ∘ fun t : Fin (a + 1) => chainCol a D S t)) := by
      have : (D a • (pcImg a P w a).1, D a * pcCoef P w a) ∈
          span R (Set.range (pcPi a P w ∘ fun t : Fin (a + 1) => chainCol a D S t)) := by
        refine subset_span ⟨⟨a, by omega⟩, ?_⟩
        have h := hcol ⟨a, by omega⟩
        simp only [lt_irrefl, if_false] at h
        exact h
      convert Submodule.smul_mem _ c this using 1
      ext <;> simp [smul_smul, mul_assoc]
    convert add_mem h1 h2 using 1
    ext <;> simp

end ColouredSand.Blocks
