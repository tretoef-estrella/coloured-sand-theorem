import RequestProject.OddHouses.All

/-!
# CheckCSI15 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI15 (`CSI15_houses_at_p.md`): the definitions written out (digits, r_u,
R_H, J_H, x_H, ĉ_H, c_u, car_t, θ, κ, sat, type, τ, firing, d_1) and the agreement with CSI13's
ruler; Part A (A0–A3) with R_H, J_H, r_k written out; Part B (B1–B6); Part C (C1–C7).
Then `#print axioms`.
-/

namespace CheckCSI15

open ColouredSand.OddTwist Finset

theorem hDefs (p k ℓ u x t c : ℕ) (I E a b D₀ : Finset ℕ) (dg : ℕ → ℕ) (e : ℤ) :
    digP p u x = x / p ^ u % p ∧
    rP p u x = padicValNat p (x / p ^ u + 1) ∧
    RHP p k I dg ℓ e E = ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t)
        - kappaP p ℓ (∑ t ∈ E, dg t * p ^ t) ∧
    JHP p k dg ℓ E = (if p ^ k ≤ ℓ + ∑ t ∈ E, dg t * p ^ t then 1 else 0) ∧
    xHP p k I dg ℓ e E = RHP p k I dg ℓ e E - RHP p k I dg ℓ e (I \ E) ∧
    cHatHP p k I dg ℓ e a b = RHP p k I dg ℓ e a - RHP p k I dg ℓ e b
        + (Rulers.gamma k I (a \ b) : ℤ) ∧
    cinP p dg ℓ u E =
      (if p ^ u ≤ ℓ % p ^ u + (∑ t ∈ E, dg t * p ^ t) % p ^ u then 1 else 0) ∧
    carP p k I dg ℓ t E =
      ((Ico t (Rulers.next k I t)).filter (fun v => cinP p dg ℓ (v + 1) E = 1)).card ∧
    thetaP p ℓ t = p - (ℓ / p ^ t % p) ∧
    kapP p k I ℓ t = 1 + min (padicValNat p (ℓ / p ^ (t + 1) + 1)) (Rulers.h k I t - 1) ∧
    satP p k I ℓ t = (if kapP p k I ℓ t = Rulers.h k I t then 1 else 0) ∧
    typP p dg ℓ t = (if thetaP p ℓ t = 1 then .OR
      else if thetaP p ℓ t ≤ dg t then .DIG
      else if thetaP p ℓ t = dg t + 1 then .AND else .NEV) ∧
    tauP p k I dg ℓ e t = (Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t -
      (if typP p dg ℓ t = .OR ∨ typP p dg ℓ t = .DIG then (kapP p k I ℓ t : ℤ) else 0) ∧
    d1P p k I dg ℓ e c D₀ = -tauP p k I dg ℓ e c
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀
      + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHP p c dg (ℓ % p ^ c) (I.erase c \ D₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The four firing conditions of (B2), case by case. -/
theorem hFires (p ℓ t : ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) :
    (typP p dg ℓ t = .OR → (firesP p dg ℓ t E ↔ t ∈ E ∨ cinP p dg ℓ t E = 1)) ∧
    (typP p dg ℓ t = .DIG → (firesP p dg ℓ t E ↔ t ∈ E)) ∧
    (typP p dg ℓ t = .AND → (firesP p dg ℓ t E ↔ t ∈ E ∧ cinP p dg ℓ t E = 1)) ∧
    (typP p dg ℓ t = .NEV → ¬ firesP p dg ℓ t E) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [firesP, h]

theorem hRuler (p k ℓ e : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) :
    RHP p k I dg ℓ (e : ℤ) E = rulerP p e k I dg ℓ E := RHP_eq_rulerP p k I dg ℓ e E

theorem hrP {p : ℕ} [Fact p.Prime] (u x j : ℕ) :
    j ≤ rP p u x ↔ ∀ i < j, x / p ^ (u + i) % p = p - 1 := rP_spec u x j

/-- (A0)–(A3), with `R_μ`, `J_H`, `r_k` written out in (A1). -/
theorem hA {p : ℕ} [Fact p.Prime] {k : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (ℓ μ dk m : ℕ)
    (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1) {D E F a b : Finset ℕ} (hD : D ⊆ I) (hE : E ⊆ I)
    (ha : a ⊆ I) (hb : b ⊆ I) :
    xHP p k I dg ℓ e (I \ D) = -xHP p k I dg ℓ e D ∧
    (oW p dg E ≤ oW p dg F → JHP p k dg ℓ E ≤ JHP p k dg ℓ F) ∧
    (∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p μ (∑ t ∈ E, dg t * p ^ t)
      = (∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t)
          - kappaP p (μ % p ^ k) (∑ t ∈ E, dg t * p ^ t))
        - (padicValNat p (μ / p ^ k + 1) : ℤ) *
          ((if p ^ k ≤ μ % p ^ k + ∑ t ∈ E, dg t * p ^ t then 1 else 0 : ℕ) : ℤ)) ∧
    (m + dk * p ^ k) % p ^ k = m % p ^ k ∧
    (rP p k m = 0 ∨ rP p k (m + dk * p ^ k) = 0) ∧
    RHP p k I dg m e a - RHP p k I dg (m + dk * p ^ k) e b + Rulers.gamma k I (a \ b) =
      cHatHP p k I dg (m % p ^ k) e a b - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) a
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) b ∧
    RHP p k I dg m e D - RHP p k I dg (m + dk * p ^ k) e (I \ D) =
      xHP p k I dg (m % p ^ k) e D - (rP p k m : ℤ) * JHP p k dg (m % p ^ k) D
        + (rP p k (m + dk * p ^ k) : ℤ) * JHP p k dg (m % p ^ k) (I \ D) :=
  ⟨houseP_A0_antisymm (p := p) (k := k) (dg := dg) ℓ e hD, fun h => houseP_A0_upset ℓ h,
    houseP_A1 hI hd e μ hE, houseP_A2_residue p k dk m, houseP_A2_at_most_one k dk m hdk1 hdk,
    houseP_A3_cost hI hd e dk m ha hb, houseP_A3_clock hI hd e dk m hD⟩

theorem hA2rem (k m : ℕ) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    Xor' (rP 2 k m = 0) (rP 2 k (m + 1 * 2 ^ k) = 0) ∧
    (rP p k 0 = 0 ∧ rP p k (0 + 1 * p ^ k) = 0) :=
  ⟨houseP_A2_two k m, houseP_A2_both_zero hp3 k⟩

open Classical in
/-- (B1)–(B6). -/
theorem hB {p : ℕ} [Fact p.Prime] {k ℓ : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (e : ℤ)
    {E : Finset ℕ} (hE : E ⊆ I) {t : ℕ} (ht : t ∈ I) :
    (∀ hne : I.Nonempty, cinP p dg ℓ (I.min' hne) E = 0) ∧
    carP p k I dg ℓ t E = (if firesP p dg ℓ t E then kapP p k I ℓ t else 0) ∧
    (firesP p dg ℓ t E ↔ thetaP p ℓ t ≤ (if t ∈ E then 1 else 0) * dg t + cinP p dg ℓ t E) ∧
    (cinP p dg ℓ (Rulers.next k I t) E = 1 ↔ 0 < carP p k I dg ℓ t E ∧ satP p k I ℓ t = 1) ∧
    kappaP p ℓ (∑ s ∈ E, dg s * p ^ s) = ∑ s ∈ I, (carP p k I dg ℓ s E : ℤ) ∧
    RHP p k I dg ℓ e E = ∑ s ∈ E, tauP p k I dg ℓ e s
      - ∑ s ∈ I, (kapP p k I ℓ s : ℤ) * (cinP p dg ℓ s E : ℤ) *
          (if (typP p dg ℓ s = .OR ∧ s ∉ E) ∨ (typP p dg ℓ s = .AND ∧ s ∈ E) then 1 else 0) ∧
    JHP p k dg ℓ E = cinP p dg ℓ k E :=
  ⟨fun hne => houseP_B1 hd hne hE, houseP_B2 hI hd hE ht, houseP_B2_fires_iff hd ht,
    houseP_B3 hI hd hE ht, houseP_B4 hI hd hℓ hE, houseP_B5 hI hd hℓ e hE, houseP_B6 hI hd hℓ hE⟩

/-- (C1)–(C7), `c = max I`, `H' = (I ∖ {c}, c, ℓ mod p^c, e, d)`. -/
theorem hC {p : ℕ} [Fact p.Prime] {k ℓ c : ℕ} {I : Finset ℕ} {dg : ℕ → ℕ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (e : ℤ)
    (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ Δ : Finset ℕ} (hD : D₀ ⊆ I.erase c)
    (hΔ : Δ ⊆ I) (hcΔ : c ∉ Δ) (hΔne : Δ ≠ ∅) :
    RHP p k I dg ℓ e D₀ = RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀ ∧
    RHP p k I dg ℓ e (D₀ ∪ {c}) = tauP p k I dg ℓ e c + RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀ ∧
    JHP p k dg ℓ D₀ =
      (if typP p dg ℓ c = .OR then 1 else 0) * satP p k I ℓ c * JHP p c dg (ℓ % p ^ c) D₀ ∧
    JHP p k dg ℓ (D₀ ∪ {c}) = satP p k I ℓ c *
      ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then 1 else 0) +
        (if typP p dg ℓ c = .AND then 1 else 0) * JHP p c dg (ℓ % p ^ c) D₀) ∧
    Rulers.gamma k I Δ = Rulers.gamma c (I.erase c) Δ + (k - c) ∧
    Rulers.gamma k I (D₀ ∪ {c}) = Rulers.gamma c (I.erase c) D₀ ∧
    xHP p k I dg ℓ e D₀ = xHP p c (I.erase c) dg (ℓ % p ^ c) e D₀ + d1P p k I dg ℓ e c D₀ ∧
    xHP p k I dg ℓ e (D₀ ∪ {c}) =
      -(xHP p c (I.erase c) dg (ℓ % p ^ c) e (I.erase c \ D₀) +
        d1P p k I dg ℓ e c (I.erase c \ D₀)) :=
  ⟨houseP_C1 hI hd hℓ e hne hc hD, houseP_C2 hI hd hℓ e hne hc hD, houseP_C3 hI hd hℓ hne hc hD,
    houseP_C4 hI hd hℓ hne hc hD, houseP_C5_not_mem hI hne hc hΔ hcΔ hΔne,
    houseP_C5_mem hI hne hc hD, houseP_C6 hI hd hℓ e hne hc hD, houseP_C7 hI hd hℓ e hne hc hD⟩

end CheckCSI15

#print axioms CheckCSI15.hDefs
#print axioms CheckCSI15.hFires
#print axioms CheckCSI15.hRuler
#print axioms CheckCSI15.hrP
#print axioms CheckCSI15.hA
#print axioms CheckCSI15.hA2rem
#print axioms CheckCSI15.hB
#print axioms CheckCSI15.hC
