module

public import RequestProject.OddDeficit.Polynomials
public import RequestProject.Deficit.DeficitLaw

/-!
# `CSI11_the_odd_deficit_law.md` — **Part D**: the deficit law (Lemma 4.2 of «the odd dance»)

Namespace `ColouredSand.OddTwist`.  The encoding is explained in `OddDeficit/Basic.lean`.
Throughout, `p` is an odd prime (`hp : p.Prime`, `hodd : Odd p`), and every digit is `< p`
(`hds : ∀ d ∈ ds, d < p`).  The oddness of `p` is used at one place only, in the step
`q_{t+1} = q_t^p` (`pow_p_sub_small_two`): there we need `p ∣ C(p,2)`.

* **(D2)** `D2`: for `Δ ⊆ I` non-empty with `t > max Δ`, `aP t Δ ≠ 0` and
  `v_p(aP t Δ) = t − |Δ| − min Δ`.
* **(D1)** `D1`: for `1 ≤ d_k ≤ p − 1`, `(starPow (aP k) d_k)(∅) = 1`, and for every
  non-empty `Δ ⊆ I`, the coefficient `(starPow (aP k) d_k)(Δ)` is non-zero with
  `v_p = k − |Δ| − min Δ`.
* `D1_delta`: (D1) written with C3's deficit `Rulers.delta k Δ`, for every `Δ ⊆ I`
  (including `Δ = ∅`).  This is the exact form of C10's `Deficit.lemma_4_5`.
* `D1_indep`: the valuation is independent of the digits and of `p`.  It equals
  `v_2(a_k(Δ))` of C10, for the same set `I`.

**Proof.** The power expansion of `OddDeficit/Algebra.lean` is used in place of the
set-partition formula:
* `f^N ≡ 1 + N (f − 1)` modulo «deficit `+ 1`»;
* `f^p ≡ 1 + p (f − 1)` modulo «deficit `+ 2`» for odd `p`.

The induction on `t` is `aP_exact`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Deficit

/-! ### Exact divisibility -/

/-- `ExactDvd q e x`: `q^e ∣ x` but `q^{e+1} ∤ x`. -/
def ExactDvd (q : ℤ) (e : ℕ) (x : ℤ) : Prop := q ^ e ∣ x ∧ ¬ q ^ (e + 1) ∣ x

lemma ExactDvd.add {q : ℤ} {e : ℕ} {x y : ℤ} (hx : ExactDvd q e x) (hy : q ^ (e + 1) ∣ y) :
    ExactDvd q e (x + y) :=
  ⟨dvd_add hx.1 ((pow_dvd_pow _ (Nat.le_succ e)).trans hy),
    fun h => hx.2 (by simpa using dvd_sub h hy)⟩

lemma ExactDvd.neg {q : ℤ} {e : ℕ} {x : ℤ} (hx : ExactDvd q e x) : ExactDvd q e (-x) :=
  ⟨(dvd_neg).2 hx.1, fun h => hx.2 ((dvd_neg).1 h)⟩

lemma ExactDvd.mul_self {q : ℤ} (hq : q ≠ 0) {e : ℕ} {x : ℤ} (hx : ExactDvd q e x) :
    ExactDvd q (e + 1) (q * x) := by
  refine ⟨?_, fun h => hx.2 ?_⟩
  · rw [pow_succ, mul_comm]; exact mul_dvd_mul_left q hx.1
  · rw [pow_succ _ (e + 1), mul_comm] at h
    exact (mul_dvd_mul_iff_left hq).1 h

lemma ExactDvd.mul_coprime {q : ℤ} (hq : Prime q) {N : ℤ} (hN : ¬ q ∣ N) {e : ℕ} {x : ℤ}
    (hx : ExactDvd q e x) : ExactDvd q e (N * x) :=
  ⟨Dvd.dvd.mul_left hx.1 N, fun h => hx.2 (hq.pow_dvd_of_dvd_mul_left _ hN h)⟩

lemma ExactDvd.valuation {p : ℕ} (hp : p.Prime) {e : ℕ} {x : ℤ}
    (hx : ExactDvd (p : ℤ) e x) : x ≠ 0 ∧ padicValInt p x = e := by
  haveI := Fact.mk hp
  have hx0 : x ≠ 0 := by rintro rfl; exact hx.2 (dvd_zero _)
  refine ⟨hx0, ?_⟩
  have h1 := (padicValInt_dvd_iff e x).1 hx.1
  have h2 : ¬ (x = 0 ∨ e + 1 ≤ padicValInt p x) := fun h => hx.2 ((padicValInt_dvd_iff _ x).2 h)
  rcases h1 with h1 | h1
  · exact absurd h1 hx0
  · push_neg at h2; omega

/-! ### The induction (D2) -/

variable {p : ℕ} {ds : List ℕ}

/-- `I ∩ [0, t)`. -/
abbrev Sb (ds : List ℕ) (t : ℕ) : Finset ℕ := (Iod ds).filter (· < t)

lemma Sb_lt (ds : List ℕ) (t : ℕ) : ∀ s ∈ Sb ds t, s < t := fun _ hs => (mem_filter.1 hs).2

lemma unitF_of_nonempty {Γ : Finset ℕ} (h : Γ.Nonempty) : unitF Γ = 0 := by
  simp [unitF, h.ne_empty]

/-- `q_t − 1` is small of order `0`, given the divisibility half of the deficit law at `t`. -/
lemma aP_small (p : ℕ) (ds : List ℕ) (t : ℕ)
    (hdvd : ∀ Γ (hΓ : Γ.Nonempty), Γ ⊆ Sb ds t →
      (p : ℤ) ^ (t - Γ.card - Γ.min' hΓ) ∣ aP p ds t Γ) :
    Small p (Sb ds t) t 0 (aP p ds t - unitF) := by
  refine ⟨by simp [Q2_const, unitF], fun Γ hΓ => ?_, fun Γ hΓ hS => ?_⟩
  · have hne : Γ.Nonempty := nonempty_iff_ne_empty.2 (by rintro rfl; exact hΓ (empty_subset _))
    simp [aP_support p ds t Γ hΓ, unitF_of_nonempty hne]
  · simpa [unitF_of_nonempty hΓ] using hdvd Γ hΓ hS

/-- **The deficit law along the recursion** (the induction behind (D2) and (D1) of
`CSI11_the_odd_deficit_law.md`): for every non-empty `Γ ⊆ I ∩ [0, t)`, `aP t Γ` is divisible by
exactly `p^{t − |Γ| − min Γ}`. -/
theorem aP_exact (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p) (t : ℕ) :
    ∀ Γ (hΓ : Γ.Nonempty), Γ ⊆ Sb ds t →
      ExactDvd (p : ℤ) (t - Γ.card - Γ.min' hΓ) (aP p ds t Γ) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction t with
  | zero =>
    intro Γ hΓ hS
    obtain ⟨x, hx⟩ := hΓ
    exact absurd (Sb_lt ds 0 x (hS hx)) (Nat.not_lt_zero _)
  | succ t ih =>
    intro Γ hΓ hS
    set f := aP p ds t with hfdef
    have hsm : Small p (Sb ds t) t 0 (f - unitF) := aP_small p ds t (fun Γ hΓ h => (ih Γ hΓ h).1)
    have hSt := Sb_lt ds t
    rw [Q0_succ_I]
    by_cases htΓ : t ∈ Γ
    · -- the new variable `y_t` occurs: `[q_{t+1}]_Γ = −[q_t^{p − d_t}]_{Γ ∖ {t}}`
      have htI : t ∈ Iod ds := (mem_filter.1 (hS htΓ)).1
      have hnot : ¬ Γ ⊆ Sb ds t := fun h => lt_irrefl t (hSt t (h htΓ))
      rw [starPow_support (aP_support p ds t) p Γ hnot, if_pos htI, if_pos htΓ]
      set d := ds.getD t 0 with hd
      have hdI := (mem_Iod_iff ds t).1 htI
      have hdp : d < p := hds d (by
        rw [hd, List.getD_eq_getElem _ _ hdI.1]; exact List.getElem_mem _)
      have hd0 : d ≠ 0 := hdI.2
      rcases (Γ \ {t}).eq_empty_or_nonempty with h' | h'
      · have hΓt : Γ = {t} := by
          ext x; constructor
          · intro hx; by_contra hxt
            have : x ∈ Γ \ {t} := mem_sdiff.2 ⟨hx, by simpa using hxt⟩
            rw [h'] at this; simp at this
          · intro hx; rw [mem_singleton.1 hx]; exact htΓ
        subst hΓt
        rw [h', Q3_const]
        simp only [card_singleton, min'_singleton]
        refine ⟨by simp, ?_⟩
        rw [show t + 1 - 1 - t + 1 = 1 by omega, pow_one]
        simpa using hpz.not_dvd_one
      · have hS' : Γ \ {t} ⊆ Sb ds t := by
          intro x hx
          obtain ⟨hxΓ, hxt⟩ := mem_sdiff.1 hx
          have := mem_filter.1 (hS hxΓ)
          exact mem_filter.2 ⟨this.1, by simp at hxt; omega⟩
        set N := p - d with hN
        have hE := pow_sub_small_one hSt hsm N
        have hX : starPow f N (Γ \ {t}) = (N : ℤ) * f (Γ \ {t}) +
            (starPow f N - unitF - (N : ℤ) • (f - unitF)) (Γ \ {t}) := by
          simp [unitF_of_nonempty h']
        have hEd := hE.2.2 _ h' hS'
        have hNp : ¬ (p : ℤ) ∣ (N : ℤ) := by
          rw [Int.natCast_dvd_natCast]
          intro h; have := Nat.le_of_dvd (by omega) h; omega
        have hEd' : (p : ℤ) ^ (t - (Γ \ {t}).card - (Γ \ {t}).min' h' + 1) ∣
            (starPow f N - unitF - (N : ℤ) • (f - unitF)) (Γ \ {t}) := by
          rw [show t - (Γ \ {t}).card - (Γ \ {t}).min' h' + 1 =
            t + 1 - (Γ \ {t}).card - (Γ \ {t}).min' h' by
              have := card_add_min'_le _ h' (fun x hx => hSt x (hS' hx)); omega]
          exact hEd
        have key := ((ih _ h' hS').mul_coprime hpz hNp).add hEd'
        have hcard : (Γ \ {t}).card + 1 = Γ.card := by
          rw [card_sdiff_of_subset (singleton_subset_iff.2 htΓ), card_singleton]
          have := card_pos.2 hΓ; omega
        have hmin : Γ.min' hΓ = (Γ \ {t}).min' h' := by
          apply le_antisymm (min'_subset _ sdiff_subset)
          by_cases hm : Γ.min' hΓ = t
          · exfalso
            obtain ⟨x, hx⟩ := h'
            have h1 := hSt x (hS' hx)
            have h2 := min'_le Γ x (mem_sdiff.1 hx).1
            omega
          · exact min'_le _ _ (mem_sdiff.2 ⟨min'_mem Γ hΓ, by simpa using hm⟩)
        have hexp : t + 1 - Γ.card - Γ.min' hΓ = t - (Γ \ {t}).card - (Γ \ {t}).min' h' := by
          rw [hmin]; omega
        rw [hexp, hX]
        simpa using key.neg
    · -- no new variable: `[q_{t+1}]_Γ = [q_t^p]_Γ`
      have hS' : Γ ⊆ Sb ds t := by
        intro x hx
        have := mem_filter.1 (hS hx)
        refine mem_filter.2 ⟨this.1, ?_⟩
        have : x ≠ t := fun h => htΓ (h ▸ hx)
        omega
      simp only [if_neg htΓ, mul_zero, zero_mul, sub_zero]
      have hD := pow_p_sub_small_two hp hodd hSt hsm
      have hX : starPow f p Γ = (p : ℤ) * f Γ +
          (starPow f p - unitF - (p : ℤ) • (f - unitF)) Γ := by
        simp [unitF_of_nonempty hΓ]
      have hle := card_add_min'_le Γ hΓ (fun s hs => hSt s (hS' hs))
      have hDd := hD.2.2 Γ hΓ hS'
      have hDd' : (p : ℤ) ^ (t - Γ.card - Γ.min' hΓ + 1 + 1) ∣
          (starPow f p - unitF - (p : ℤ) • (f - unitF)) Γ := by
        rw [show t - Γ.card - Γ.min' hΓ + 1 + 1 = t + 2 - Γ.card - Γ.min' hΓ by omega]
        exact hDd
      have key := ((ih Γ hΓ hS').mul_self hp0).add hDd'
      rw [show t + 1 - Γ.card - Γ.min' hΓ = t - Γ.card - Γ.min' hΓ + 1 by omega, hX]
      exact key

/-- **(D2)** of `CSI11_the_odd_deficit_law.md` (the intermediate statement of the induction):
`p` an odd prime, every digit `< p`.  For a non-empty `Δ ⊆ I` and `t > max Δ`, the coefficient
`aP t Δ` is non-zero and `v_p(aP t Δ) = t − |Δ| − min Δ`. -/
theorem oddDef_D2 (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p) (t : ℕ) (Δ : Finset ℕ)
    (h : Δ.Nonempty) (hΔI : Δ ⊆ Iod ds) (ht : Δ.max' h < t) :
    aP p ds t Δ ≠ 0 ∧ padicValInt p (aP p ds t Δ) = t - Δ.card - Δ.min' h := by
  have hS : Δ ⊆ Sb ds t := fun x hx =>
    mem_filter.2 ⟨hΔI hx, lt_of_le_of_lt (le_max' Δ x hx) ht⟩
  exact (aP_exact hp hodd hds t Δ h hS).valuation hp

lemma Sb_length (ds : List ℕ) : Sb ds ds.length = Iod ds := by
  ext x; simp only [mem_filter, and_iff_left_iff_imp]
  intro hx; exact ((mem_Iod_iff ds x).1 hx).1

/-- **(D1)** of `CSI11_the_odd_deficit_law.md` (Lemma 4.2, the odd deficit law): `p` an odd
prime, every digit `< p`, `k = ds.length`, and the top digit `d_k` with `1 ≤ d_k ≤ p − 1`.
Then `(starPow (aP k) d_k)(∅) = 1`, and for every non-empty `Δ ⊆ I` the coefficient
`(starPow (aP k) d_k)(Δ)` is non-zero with `v_p = k − |Δ| − min Δ`. -/
theorem oddDef_D1 (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p) (dk : ℕ) (hdk1 : 1 ≤ dk)
    (hdkp : dk ≤ p - 1) :
    starPow (aP p ds ds.length) dk ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iod ds →
        starPow (aP p ds ds.length) dk Δ ≠ 0 ∧
          padicValInt p (starPow (aP p ds ds.length) dk Δ) = ds.length - Δ.card - Δ.min' h := by
  refine ⟨Q3_const p ds _ dk, fun Δ h hΔI => ?_⟩
  set k := ds.length
  set f := aP p ds k
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hS : Δ ⊆ Sb ds k := by rw [Sb_length]; exact hΔI
  have hSt := Sb_lt ds k
  have hsm : Small p (Sb ds k) k 0 (f - unitF) :=
    aP_small p ds k (fun Γ hΓ h => (aP_exact hp hodd hds k Γ hΓ h).1)
  have hE := (pow_sub_small_one hSt hsm dk).2.2 Δ h hS
  have hX : starPow f dk Δ = (dk : ℤ) * f Δ +
      (starPow f dk - unitF - (dk : ℤ) • (f - unitF)) Δ := by
    simp [unitF_of_nonempty h]
  have hle := card_add_min'_le Δ h (fun x hx => hSt x (hS hx))
  have hE' : (p : ℤ) ^ (k - Δ.card - Δ.min' h + 1) ∣
      (starPow f dk - unitF - (dk : ℤ) • (f - unitF)) Δ := by
    rw [show k - Δ.card - Δ.min' h + 1 = k + 1 - Δ.card - Δ.min' h by omega]; exact hE
  have hNp : ¬ (p : ℤ) ∣ (dk : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  have key := ((aP_exact hp hodd hds k Δ h hS).mul_coprime hpz hNp).add hE'
  rw [hX]
  exact key.valuation hp

/-- **(D1)** of `CSI11_the_odd_deficit_law.md`, written with C3's deficit
`δ(Δ) = Rulers.delta k Δ` (`= 0` for `Δ = ∅`, `= k − |Δ| − min Δ` otherwise), for **every**
`Δ ⊆ I`: the coefficient is non-zero and `v_p = δ(Δ)` as integers.  This is the exact form of
C10's `Deficit.lemma_4_5`. -/
theorem D1_delta (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p) (dk : ℕ) (hdk1 : 1 ≤ dk)
    (hdkp : dk ≤ p - 1) {Δ : Finset ℕ} (hΔ : Δ ⊆ Iod ds) :
    starPow (aP p ds ds.length) dk Δ ≠ 0 ∧
      (padicValInt p (starPow (aP p ds ds.length) dk Δ) : ℤ) = Rulers.delta ds.length Δ := by
  obtain ⟨h0, hD⟩ := oddDef_D1 hp hodd hds dk hdk1 hdkp
  rcases Δ.eq_empty_or_nonempty with rfl | h
  · rw [h0]; simp [Rulers.delta]
  · obtain ⟨hne, hv⟩ := hD Δ h hΔ
    refine ⟨hne, ?_⟩
    have hle := card_add_min'_le Δ h (fun x hx => ((mem_Iod_iff ds x).1 (hΔ hx)).1)
    rw [hv, Rulers.delta, if_neg h.ne_empty, Rulers.minOr, dif_pos h]
    omega

/-- **(D1)**, «the same law as C10's `lemma_4_5`, independent of the digits»
(`CSI11_the_odd_deficit_law.md`, Part D): for `k ≥ 1` and `Δ ⊆ I`, the `p`-adic valuation of
`[q_k^{d_k}]_Δ` equals the `2`-adic valuation of C10's coefficient `Deficit.a I k Δ`, for the
same set `I = I(ds)`.  So it depends only on `k` and `Δ`, not on `p` or on the digits. -/
theorem D1_indep (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p) (dk : ℕ) (hdk1 : 1 ≤ dk)
    (hdkp : dk ≤ p - 1) (hk : 1 ≤ ds.length) {Δ : Finset ℕ} (hΔ : Δ ⊆ Iod ds) :
    padicValInt p (starPow (aP p ds ds.length) dk Δ) =
      padicValInt 2 (Deficit.a (Iod ds) ds.length Δ) := by
  have h1 := (D1_delta hp hodd hds dk hdk1 hdkp hΔ).2
  have h2 := (Deficit.lemma_4_5 hk (fun t ht => ((mem_Iod_iff ds t).1 ht).1) hΔ).2
  exact_mod_cast h1.trans h2.symm

end ColouredSand.OddTwist
