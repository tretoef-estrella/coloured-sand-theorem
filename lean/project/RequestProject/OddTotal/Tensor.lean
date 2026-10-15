module

public import RequestProject.OddTotal.Block
public import RequestProject.OddDance.All

/-!
# `CSI19_theorem_TOTAL.md`, Part T — every tensor power

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

## Encodings

* `V^{⊗m} ⊗ ℤ_p` is `Filt.tpow ℤ_[p] m`; CSI6's list `LL p m` of the weights of `V^{⊗m}` (each
  `λ` repeated `n_λ(m)` times) and **(R3)** `tpow_danceL` (`V^{⊗m} ≅ ⊕_{λ ∈ LL p m} danceL p λ`)
  are reused.
* The summands are indexed by the positions `t : Fin (LL p m).length`, `λ_t = (LL p m).get t`; the
  product `Π_t Y_p(λ_t, c + (m − λ_t)/2, e)` is the dependent function type over these positions.
* `e = v_p(q)` is `padicValNat p q`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.BlockOp ColouredSand.Splitting Families

variable {p : ℕ} [Fact p.Prime]

/-- Part T of `CSI19_theorem_TOTAL.md`, auxiliary: for odd `p`, every weight of `VdotL p λ` has
the parity of `λ + 1`. -/
theorem oddTotal_parity_VdotL (hp2 : p ≠ 2) (l : ℕ) : ∀ μ ∈ VdotL p l, μ % 2 = (l + 1) % 2 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hodd : p % 2 = 1 := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp2)
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro μ hμ
  by_cases h0 : l = 0
  · subst h0; rw [VdotL_zero] at hμ; simp at hμ; omega
  by_cases h1 : l + 1 < p
  · rw [VdotL_small (by omega) (by omega)] at hμ; simp at hμ; omega
  have hl' : p - 1 ≤ l := by omega
  have hk := succ_eq_d0_b (by omega : 1 ≤ p) hl'
  have hdp : (l + 1) % p < p := Nat.mod_lt _ (by omega)
  by_cases hd0 : (l + 1) % p = 0
  · rw [VdotL_d0_zero hp hl' hd0] at hμ; simp at hμ; omega
  by_cases hd1 : (l + 1) % p = 1
  · rw [VdotL_d0_one hp hl' hd1] at hμ; simp at hμ; omega
  by_cases hdm : (l + 1) % p ≤ p - 2
  · rw [VdotL_d0_mid hl' (by omega) hdm] at hμ; simp at hμ; omega
  have hp3 : 3 ≤ p := by omega
  rw [VdotL_d0_top hp3 hl' (by omega)] at hμ
  simp only [List.mem_cons, List.mem_map] at hμ
  rcases hμ with rfl | ⟨a, ha, rfl⟩
  · omega
  · have ha2 := ih _ (b_lt hp (by omega)) a ha
    set b := (l + 1) / p - 1
    have hd : (l + 1) % p = p - 1 := by omega
    -- `l + 1 = (p − 1) + p (b + 1)` and `p` is odd
    have e1 : (p * a + p - 1) % 2 = a % 2 := by
      have : p * a + p - 1 = p * a + (p - 1) := by omega
      rw [this, Nat.add_mod, Nat.mul_mod, hodd]
      omega
    have e2 : (l + 1) % 2 = (b + 1) % 2 := by
      rw [hk, hd, Nat.add_mod, Nat.mul_mod, hodd]
      omega
    omega

/-- Part T of `CSI19_theorem_TOTAL.md`, auxiliary: for odd `p`, every weight `λ ∈ LL p m`
satisfies `λ ≤ m` and `λ ≡ m (mod 2)`. -/
theorem oddTotal_mem_LL (hp2 : p ≠ 2) (m : ℕ) : ∀ l ∈ LL p m, l ≤ m ∧ l % 2 = m % 2 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  intro l hl
  refine ⟨le_of_mem_LL hp m l hl, ?_⟩
  induction m generalizing l with
  | zero => simp [LL_zero] at hl; omega
  | succ m ih =>
    rw [LL_succ, List.mem_flatMap] at hl
    obtain ⟨a, ha, hla⟩ := hl
    have := ih a ha
    have := oddTotal_parity_VdotL hp2 a l hla
    omega

/-- The decomposition of the cokernel along `V^{⊗m} ≅ ⊕_{λ ∈ LL p m} danceL p λ` (Part T of
`CSI19_theorem_TOTAL.md`, from CSI6 (R3) and CSG6 `K3a`, `K3b`; as CSG6 `K4equiv`): for every
`q`, `cokT p (V^{⊗m}) m q c ≃ₗ Π_t cokT p (danceL p λ_t) m q c`. -/
theorem oddTotal_cokT_tpow (hp2 : p ≠ 2) (m q c : ℕ) :
    Nonempty (cokT p (Filt.tpow ℤ_[p] m) m q c ≃ₗ[ℤ_[p]]
      ((t : Fin (LL p m).length) → cokT p (danceL p ((LL p m).get t)) m q c)) := by
  obtain ⟨u⟩ := tpow_danceL p hp2 m
  let Θ := (isoEquiv u).trans (dsumTheta p (danceL p) (LL p m))
  let Gt : ∀ t : Fin (LL p m).length,
      Module.End ℤ_[p] ((danceL p ((LL p m).get t)).ι → ℤ_[p]) :=
    fun t => opT p (danceL p ((LL p m).get t)) m q c
  have hΘ : ∀ f, (LinearMap.pi fun t => Gt t ∘ₗ LinearMap.proj t) (Θ f) =
      Θ (opT p (Filt.tpow ℤ_[p] m) m q c f) := fun f => by
    have h3 := LinearMap.congr_fun (K3a u m q c) f
    have h4 := LinearMap.congr_fun (K3b (danceL p) (LL p m) m q c) (isoEquiv u f)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h3 h4
    simp only [Θ, LinearEquiv.trans_apply, h3, h4]
    rfl
  exact ⟨(cokerEquivOfConj _ _ Θ Θ hΘ).trans
    ((Submodule.quotEquivOfEq _ _ (range_pi_comp_proj Gt)).trans (Submodule.quotientPi _))⟩

/-- **(T1)** of `CSI19_theorem_TOTAL.md`: for an odd prime `p`, every `m` (no bound), every `c`
and every `q ≠ 0` (the file's `q ≥ 2`, `p ∣ q`; neither is needed here: more general),
`cokT p (V^{⊗m}) m q c ≃ₗ[ℤ_[p]] Π_{t < (LL p m).length} Y_p(λ_t, c + (m − λ_t)/2, e)` with
`λ_t = (LL p m).get t` and `e = v_p(q)`.  From CSI6 (R3) with `K3a`, `K3b`, then (U1), (B1). -/
theorem oddTotal_T1 (hp2 : p ≠ 2) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (cokT p (Filt.tpow ℤ_[p] m) m q c ≃ₗ[ℤ_[p]]
      ((t : Fin (LL p m).length) →
        Yp p ((LL p m).get t) (c + (m - (LL p m).get t) / 2) (padicValNat p q))) := by
  obtain ⟨E⟩ := oddTotal_cokT_tpow hp2 m q c
  have hfac : ∀ t : Fin (LL p m).length, Nonempty (cokT p (danceL p ((LL p m).get t)) m q c ≃ₗ[ℤ_[p]]
      Yp p ((LL p m).get t) (c + (m - (LL p m).get t) / 2) (padicValNat p q)) := fun t => by
    obtain ⟨h1, h2⟩ := oddTotal_mem_LL hp2 m _ (List.get_mem _ _)
    obtain ⟨u1⟩ := oddTotal_U1 (danceL p ((LL p m).get t)) m c hq
    obtain ⟨b1⟩ := oddTotal_B1 hp2 h1 h2 (padicValNat p q) c
    exact ⟨u1.trans b1⟩
  exact ⟨E.trans (LinearEquiv.piCongrRight fun t => (hfac t).some)⟩

end ColouredSand.OddTwist
