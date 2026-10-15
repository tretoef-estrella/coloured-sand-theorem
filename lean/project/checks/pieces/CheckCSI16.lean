import RequestProject.OddPotential.All

/-!
# CheckCSI16 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI16 (`CSI16_theorem_F_at_p.md`): the definitions written out (the base-p
sequences on dancers, the walk, (Λ_p), (Cut), ŷ, ĉ, the potential, X_1, v', the flat); Theorem
F1_p with x_H written out; (P4) with its two bounds; Lemma N; Theorem F_p and Corollary F′_p;
Part Δ step 1; and the three long statements (F0, Lemma P, Lemma F) by name. Then `#print axioms`.
-/

namespace CheckCSI16

open ColouredSand.OddTwist Finset AntitonicFit TheoremF

theorem hDefs (p k ℓ c q q' f : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (e cF : ℤ) (V' : ℕ → ℤ) :
    xHseqP p k I dg ℓ e q = xHP p k I dg ℓ e (dancer I q) ∧
    JHseqP p k I dg ℓ q = JHP p k dg ℓ (dancer I q) ∧
    dWalkP p k I dg ℓ e c q = d1P p k I dg ℓ e c (dancer (I.erase c) q) ∧
    yhatP p k I dg ℓ e = ifit (2 ^ #I) (xHseqP p k I dg ℓ e) ∧
    cHatSeqP p k I dg ℓ e q q' = cHatHP p k I dg ℓ e (dancer I q) (dancer I q') ∧
    X1P p k I dg ℓ e c q = yhatP p c (I.erase c) dg (ℓ % p ^ c) e q + dWalkP p k I dg ℓ e c q ∧
    vPrimeP p k I dg ℓ e c V' q = (if q < 2 ^ #(I.erase c) then
        V' q - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) q
      else tauP p k I dg ℓ e c + V' (q - 2 ^ #(I.erase c)) -
        (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) (q - 2 ^ #(I.erase c))) ∧
    flatVP p k I dg ℓ e c V' f cF q =
      (if f ≤ q ∧ q ≤ 2 ^ #I - 1 - f then cF else vPrimeP p k I dg ℓ e c V' q) ∧
    (LamPropP p k I dg ℓ e ↔
      ∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * (oW p dg I : ℤ)) ∧
    (CutPropP p k I dg ℓ e ↔ ∀ b < 2 ^ #I, JHseqP p k I dg ℓ b = 1 →
      (∀ q < b, JHseqP p k I dg ℓ q = 0) →
        IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b ∧
          IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (2 ^ #I - b)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, Iff.rfl⟩

theorem hPot (p k ℓ : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (e : ℤ) (V : ℕ → ℤ) :
    IsPotentialP p k I dg ℓ e V ↔
      (∀ q < 2 ^ #I, V q - V (2 ^ #I - 1 - q) = yhatP p k I dg ℓ e q) ∧
      (∀ q q', q ≤ q' → q' < 2 ^ #I → V q' ≤ V q) ∧
      (∀ q q', Potential.IsArrow I q q' → V q - V q' ≤
        cHatHP p k I dg ℓ e (dancer I q) (dancer I q')) :=
  ⟨fun h => ⟨h.E, h.M, h.G⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Theorem F1_p, with `x_H` written out on the dancers. -/
theorem hF1 {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, |ifit (2 ^ #I) (fun j => xHP p k I dg ℓ e (dancer I j)) q| ≤
        e * ((∑ t ∈ I, dg t * p ^ t : ℕ) : ℤ)) ∧
    (∀ b < 2 ^ #I, JHP p k dg ℓ (dancer I b) = 1 → (∀ q < b, JHP p k dg ℓ (dancer I q) = 0) →
      IsStrictCut (2 ^ #I) (fun j => (xHP p k I dg ℓ e (dancer I j) : ℝ)) b ∧
        IsStrictCut (2 ^ #I) (fun j => (xHP p k I dg ℓ e (dancer I j) : ℝ)) (2 ^ #I - b)) ∧
    (oW p dg I : ℤ) ≤ (p : ℤ) ^ k - 1 :=
  ⟨(oddF_theorem_F1 hI hd hℓ he).1, (oddF_theorem_F1 hI hd hℓ he).2,
    (oddF_F1_Lambda_pow hI hd hℓ he).1⟩

/-- (P4): the junction step and its two bounds `≤ h − e(d_c p^c − o_{I'}) ≤ h − e`. -/
theorem hP4 {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ c : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c)) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1) =
      -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ∧
    -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤
      ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ∧
    ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ≤
      ((k - c : ℕ) : ℤ) - e :=
  oddF_P4 hI hd he hne hc hV'

/-- Lemma N: no flat ⟹ `v'` is a potential. -/
theorem hN {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ c : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k)
    (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V')
    (hX : 0 < X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1)) :
    IsPotentialP p k I dg ℓ e (vPrimeP p k I dg ℓ e c V') :=
  oddF_lemma_N hI hd hℓ he hne hc hV' hX

/-- Theorem F_p and Corollary F′_p (subsets, base-p o-order). -/
theorem hT {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∃ V : ℕ → ℤ, IsPotentialP p k I dg ℓ e V) ∧
    ∃ W : Finset ℕ → ℤ,
      (∀ D, D ⊆ I → W D - W (I \ D) = yhatP p k I dg ℓ e (GoldenMatching.rank I D)) ∧
      (∀ E F, E ⊆ I → F ⊆ I → (∑ t ∈ E, dg t * p ^ t) ≤ (∑ t ∈ F, dg t * p ^ t) → W F ≤ W E) ∧
      (∀ a b, a ⊆ I → b ⊆ I → b ⊂ a → W a - W b ≤
        RHP p k I dg ℓ e a - RHP p k I dg ℓ e b + Rulers.gamma k I (a \ b)) :=
  ⟨oddF_theorem_F hI hd hℓ he, oddF_corollary_F' hI hd hℓ he⟩

/-- Part Δ step 1: `d_1 ≤ e d_c p^c` and `X_1 ≤ e·o_I`. -/
theorem hDelta {p : ℕ} [Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ}
    (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) (q : ℕ) (hq : q < 2 ^ #(I.erase c)) :
    dWalkP p k I dg ℓ e c q ≤ e * dg c * (p : ℤ) ^ c ∧
    X1P p k I dg ℓ e c q ≤ e * (oW p dg I : ℤ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := oddF_delta_step1 hI hd he hne hc q hq
  exact ⟨by linarith, by linarith⟩

end CheckCSI16

#check @ColouredSand.OddTwist.oddF_theorem_F0
#check @ColouredSand.OddTwist.oddF_lemma_P
#check @ColouredSand.OddTwist.oddF_lemma_X
#check @ColouredSand.OddTwist.oddF_lemma_F
#print axioms CheckCSI16.hDefs
#print axioms CheckCSI16.hPot
#print axioms CheckCSI16.hF1
#print axioms CheckCSI16.hP4
#print axioms CheckCSI16.hN
#print axioms CheckCSI16.hT
#print axioms CheckCSI16.hDelta
#print axioms ColouredSand.OddTwist.oddF_theorem_F0
#print axioms ColouredSand.OddTwist.oddF_lemma_P
#print axioms ColouredSand.OddTwist.oddF_lemma_X
#print axioms ColouredSand.OddTwist.oddF_lemma_F
