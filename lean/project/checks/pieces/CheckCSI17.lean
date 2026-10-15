import RequestProject.OddCellFloor.All

/-!
# CheckCSI17 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI17 (`CSI17_integrality_and_cell_floor_at_p.md`): the definitions written
out (clocks z, costs, v and w, x^♯, ŷ^♯, cost^♯, the cell and sharp arrows); Lemma 7.9_p (I1),
(I2), (I3); Part B (U1)–(U3) with v, w written out and the `theorem_U` consequence; Part C with
equality on the sharp loops; the Part C consequence. Then `#print axioms`.
-/

namespace CheckCSI17

open ColouredSand.OddTwist Finset AntitonicFit TheoremF SmithBounds CellFloor

variable {p : ℕ} [Fact p.Prime] {dg : ℕ → ℕ}

theorem hDefs (k ℓ : ℕ) (I : Finset ℕ) (e : ℤ) (Pr Pc q q' a b j : ℕ) (V : ℕ → ℤ) (P : ℕ) :
    oddCellClock p k I dg ℓ e Pr Pc q = xHseqP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
      (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ) ∧
    oddCellCost p k I dg ℓ e Pr Pc q q' = cHatSeqP p k I dg ℓ e q q' -
      (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) + (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ∧
    oddCellPenal V p k I dg ℓ P q = V q - (P : ℤ) * (JHseqP p k I dg ℓ q : ℤ) ∧
    oddCellXSharp p k I dg ℓ e j = xHseqP p k I dg ℓ e (j + 1) ∧
    oddCellYhatSharp p k I dg ℓ e = ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) ∧
    oddCellCostSharp p k I dg ℓ e a b = cHatSeqP p k I dg ℓ e (a + 1) b ∧
    (IsCellArrow I q q' ↔ q < 2 ^ #I ∧ q' < 2 ^ #I ∧ dancer I q' ⊆ dancer I q) ∧
    (IsSharpArrow I a b ↔ a < 2 ^ #I - 1 ∧ b < 2 ^ #I - 1 ∧ dancer I b ⊆ dancer I (a + 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, Iff.rfl⟩

/-- (I1): the real fit of x_H is the integer ŷ_H, and ŷ_H is non-increasing. -/
theorem hI1 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q = (yhatP p k I dg ℓ e q : ℝ)) ∧
      ∀ q q', q ≤ q' → q' < 2 ^ #I → yhatP p k I dg ℓ e q' ≤ yhatP p k I dg ℓ e q := by
  refine ⟨(oddCell_lemma_7_9_I1 hI hd hℓ he).1, ?_⟩
  have h := (oddCell_lemma_7_9_I1 hI hd hℓ he).2
  intro q q' hqq' hq'
  exact h.anti hqq' hq'

/-- (I2), every P_r, P_c: the integer fit of z is ŷ_H − P_r J_H(q) + P_c J_H(N−1−q), it equals
the real fit, and it is non-increasing. -/
theorem hI2 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) :
    (∀ q < 2 ^ #I, ifit (2 ^ #I) (fun q => xHseqP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
        (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) q =
      yhatP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
        (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) ∧
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (oddCellClock p k I dg ℓ e Pr Pc)) q =
      (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q : ℝ)) ∧
    NonIncrOn (2 ^ #I) (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc)) :=
  oddCell_lemma_7_9_I2 hI hd hℓ he Pr Pc

/-- (I3), ℓ = p^k − 1, I ≠ ∅. -/
theorem hI3 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) :
    (∀ t ∈ I, typP p dg ℓ t = .OR ∧ thetaP p ℓ t = 1) ∧
    (∀ q < 2 ^ #I, JHseqP p k I dg ℓ q = if q ≠ 0 then 1 else 0) ∧
    IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) 1 ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (fun j => xHseqP p k I dg ℓ e (j + 1))) j =
      fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) j =
      yhatP p k I dg ℓ e (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (fun j => xHseqP p k I dg ℓ e (j + 1))) j =
      (yhatP p k I dg ℓ e (j + 1) : ℝ)) :=
  oddCell_lemma_7_9_I3 hI hd hℓ' he hne

/-- Part B (U1)–(U3) with v(q) = V(q) − P_r J_H(q), w(q) = V(q) − P_c J_H(q) written out. -/
theorem hB {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ)
    {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (∀ q q', q ≤ q' → q' < 2 ^ #I →
      V q' - (Pr : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ≤ V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) ∧
    (∀ q q', q ≤ q' → q' < 2 ^ #I →
      V q' - (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ) ≤ V q - (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) ∧
    (∀ q < 2 ^ #I, (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) -
        (V (2 ^ #I - 1 - q) - (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) =
      ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q) ∧
    (∀ q q', q < 2 ^ #I → q' < 2 ^ #I → dancer I q' ⊆ dancer I q →
      (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) - (V q' - (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ)) ≤
        cHatSeqP p k I dg ℓ e q q' - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
          (Pc : ℤ) * (JHseqP p k I dg ℓ q' : ℤ)) ∧
    (∀ q < 2 ^ #I, (V q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) -
        (V q - (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) =
      cHatSeqP p k I dg ℓ e q q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
          (Pc : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := oddCell_theorem_B hI hd hℓ he Pr Pc hV
  exact ⟨fun q q' a b => h1.anti a b, fun q q' a b => h2.anti a b, h3,
    fun q q' a b c => h4 q q' ⟨a, b, c⟩, h5⟩

/-- Part B consequence: every r-matching of the cell arrows costs at least tailSum N r (ifit z);
the potential is supplied by Theorem F_p. -/
theorem hBfloor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) {r : ℕ}
    {Rows : Finset ℕ} {β : ℕ → ℕ} (hm : IsRMatching (2 ^ #I) (IsCellArrow I) r Rows β) :
    tailSum (2 ^ #I) r (fun j => (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) j : ℝ)) ≤
      ∑ a ∈ Rows, (oddCellCost p k I dg ℓ e Pr Pc a (β a) : ℝ) :=
  oddCell_theorem_B_floor hI hd hℓ he Pr Pc hm

/-- Part C, ℓ = p^k − 1, I ≠ ∅, with v(j) = V(j+1), w(j) = V(j), and equality on the sharp loops
`b = a + 1`. -/
theorem hC {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {V : ℕ → ℤ} (hV : IsPotentialP p k I dg ℓ e V) :
    (NonIncrOn (2 ^ #I - 1) (fun j => V (j + 1)) ∧ NonIncrOn (2 ^ #I - 1) V) ∧
    (∀ j < 2 ^ #I - 1, V (j + 1) - V (2 ^ #I - 2 - j) =
      ifit (2 ^ #I - 1) (fun j => xHseqP p k I dg ℓ e (j + 1)) j) ∧
    (∀ a b, a < 2 ^ #I - 1 → b < 2 ^ #I - 1 → dancer I b ⊆ dancer I (a + 1) →
      V (a + 1) - V b ≤ cHatSeqP p k I dg ℓ e (a + 1) b) ∧
    (∀ a, a + 1 < 2 ^ #I - 1 → V (a + 1) - V (a + 1) = cHatSeqP p k I dg ℓ e (a + 1) (a + 1)) := by
  obtain ⟨h1, h2, h3⟩ := oddCell_theorem_C hI hd hℓ' he hne hV
  refine ⟨h1, h2, fun a b ha hb hs => h3 a b ⟨ha, hb, hs⟩, fun a _ => ?_⟩
  rw [oddCell_cHat_self]; simp

/-- Part C consequence with N − 1 positions. -/
theorem hCfloor {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I - 1) (IsSharpArrow I) r Rows β) :
    tailSum (2 ^ #I - 1) r (fun j => (oddCellYhatSharp p k I dg ℓ e j : ℝ)) ≤
      ∑ a ∈ Rows, (cHatSeqP p k I dg ℓ e (a + 1) (β a) : ℝ) :=
  oddCell_theorem_C_floor hI hd hℓ' he hne hm

end CheckCSI17

#print axioms CheckCSI17.hDefs
#print axioms CheckCSI17.hI1
#print axioms CheckCSI17.hI2
#print axioms CheckCSI17.hI3
#print axioms CheckCSI17.hB
#print axioms CheckCSI17.hBfloor
#print axioms CheckCSI17.hC
#print axioms CheckCSI17.hCfloor
#print axioms ColouredSand.OddTwist.oddCell_theorem_B
#print axioms ColouredSand.OddTwist.oddCell_theorem_C
