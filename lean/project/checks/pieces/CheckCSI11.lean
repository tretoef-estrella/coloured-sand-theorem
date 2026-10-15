import RequestProject.OddDeficit.All

/-!
# CheckCSI11 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI11 (`CSI11_the_odd_deficit_law.md`): the powers and `I(ds)` written out,
(Q0) with `starMul` unfolded, (Q1)–(Q3), (D2), (D1) with the valuation `k − |Δ| − min Δ`
written out, its `δ`-form, its agreement with C10, and (D1) for `λ`. Then `#print axioms`.
-/

namespace CheckCSI11

open ColouredSand.OddTwist Finset

/-- Powers and `I(ds)` written out. -/
theorem hDefs (f : Finset ℕ → ℤ) (n : ℕ) (Δ : Finset ℕ) (ds : List ℕ) :
    starPow f 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    starPow f (n + 1) Δ = ∑ Δ₁ ∈ Δ.powerset, f Δ₁ * starPow f n (Δ \ Δ₁) ∧
    Iod ds = (range ds.length).filter (fun t => ds.getD t 0 ≠ 0) :=
  ⟨rfl, rfl, rfl⟩

/-- (Q0) written out: `q_0 = 1`, `q_{t+1} = q_t^p − [t < k ∧ d_t ≠ 0][t ∈ Δ] q_t^{p−d_t}`. -/
theorem hQ0 (p : ℕ) (ds : List ℕ) (t : ℕ) (Δ : Finset ℕ) :
    aP p ds 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    aP p ds (t + 1) Δ = starPow (aP p ds t) p Δ -
      (if t < ds.length ∧ ds.getD t 0 ≠ 0 then 1 else 0) * (if t ∈ Δ then 1 else 0) *
        starPow (aP p ds t) (p - ds.getD t 0) (Δ \ {t}) :=
  ⟨rfl, rfl⟩

/-- (Q1), (Q2), (Q3) for every `p` and every digit list. -/
theorem hQ (p : ℕ) (ds : List ℕ) (t N : ℕ) :
    (∀ Δ, aP p ds t Δ ≠ 0 → Δ ⊆ (Iod ds).filter (· < t)) ∧
    aP p ds t ∅ = 1 ∧ starPow (aP p ds t) N ∅ = 1 ∧
    ∀ Γ, starPow (aP p ds t) N Γ =
      ∑ P ∈ setPartitions Γ, (N.descFactorial P.card : ℤ) * ∏ B ∈ P, aP p ds t B :=
  ⟨fun Δ h => Q1_support p ds t Δ h, Q2_const p ds t, Q3_const p ds t N,
    fun Γ => Q3_partition p ds t N Γ⟩

/-- The partitions are the set partitions. -/
theorem hPart (Γ : Finset ℕ) :
    setPartitions Γ = Γ.powerset.powerset.filter (fun P =>
      (∀ B ∈ P, B.Nonempty) ∧ (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧ P.sup id = Γ) :=
  rfl

/-- (D2). -/
theorem hD2 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (t : ℕ) (Δ : Finset ℕ) (h : Δ.Nonempty) (hΔI : Δ ⊆ Iod ds) (ht : Δ.max' h < t) :
    aP p ds t Δ ≠ 0 ∧ padicValInt p (aP p ds t Δ) = t - Δ.card - Δ.min' h :=
  oddDef_D2 hp hodd hds t Δ h hΔI ht

/-- (D1), the odd deficit law (Lemma 4.2). -/
theorem hD1 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (dk : ℕ) (h1 : 1 ≤ dk) (h2 : dk ≤ p - 1) :
    starPow (aP p ds ds.length) dk ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iod ds →
        starPow (aP p ds ds.length) dk Δ ≠ 0 ∧
          padicValInt p (starPow (aP p ds ds.length) dk Δ) = ds.length - Δ.card - Δ.min' h :=
  oddDef_D1 hp hodd hds dk h1 h2

/-- (D1) with C3's `δ`, and the same valuation as C10's `a` at the prime `2`. -/
theorem hD1C10 {p : ℕ} {ds : List ℕ} (hp : p.Prime) (hodd : Odd p) (hds : ∀ d ∈ ds, d < p)
    (dk : ℕ) (h1 : 1 ≤ dk) (h2 : dk ≤ p - 1) (hk : 1 ≤ ds.length) {Δ : Finset ℕ}
    (hΔ : Δ ⊆ Iod ds) :
    (padicValInt p (starPow (aP p ds ds.length) dk Δ) : ℤ) = Rulers.delta ds.length Δ ∧
    padicValInt p (starPow (aP p ds ds.length) dk Δ) =
      padicValInt 2 (Deficit.a (Iod ds) ds.length Δ) :=
  ⟨(D1_delta hp hodd hds dk h1 h2 hΔ).2, D1_indep hp hodd hds dk h1 h2 hk hΔ⟩

/-- (D1) for `λ`, digits of `λ + 1` from CSI10. -/
theorem hD1lam {p : ℕ} (hp : p.Prime) (hodd : Odd p) (l : ℕ) :
    dsL p l = (Nat.digits p (l + 1)).take (kTop p l) ∧ Iod (dsL p l) = Iset p l ∧
    (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) ∅ = 1 ∧
      ∀ Δ (h : Δ.Nonempty), Δ ⊆ Iset p l →
        starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ ≠ 0 ∧
          padicValInt p (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ) =
            kTop p l - Δ.card - Δ.min' h) :=
  ⟨rfl, Iod_lambda p l, D1_lambda hp hodd l⟩

end CheckCSI11

#print axioms CheckCSI11.hDefs
#print axioms CheckCSI11.hQ0
#print axioms CheckCSI11.hQ
#print axioms CheckCSI11.hPart
#print axioms CheckCSI11.hD2
#print axioms CheckCSI11.hD1
#print axioms CheckCSI11.hD1C10
#print axioms CheckCSI11.hD1lam
#print axioms ColouredSand.OddTwist.Q3_partition
