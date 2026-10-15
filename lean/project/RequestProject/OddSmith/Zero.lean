module

public import RequestProject.OddSmith.Positive

/-!
# Part Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`: the case `i = 0`

## Encoding

* `oddSmithXSharp p l e q = R^♯(dancer_I (q+1)) − R^♯(I ∖ dancer_I (q+1))` is `x^♯ q` (CSI13's
  `rulerSharpP`, used for `q < N − 1`), and `oddSmithYhatSharp p l e = AntitonicFit.ifit (N − 1) x^♯`
  is `ŷ^♯`.
* "`I ≠ ∅`" is `(Iset p l).Nonempty`; the position `0` (the dancer `∅`) is `oddSmithZeroPos p l`.
* `R^♯ = R_{H^♯}` for the house `H^♯ = (I, k, p^k − 1, e, d)` (`oddSmith_rulerSharp_eq_RHP`, from
  CSI13 (L3) `kappaP_K_sub_one`: `κ_p(p^k − 1, o_E) = k − min E`, `= 0` for `E = ∅`).
* The floor uses CSI17 Part B for `H^♯` with zero penalties (it also covers the zero row of `∅`),
  and CSI17 (I3) to pass from `ŷ_{H^♯}` on `N` positions to `ŷ^♯` on `N − 1` positions. The ceiling
  is CSI14 (C1) with `R₁ = R₂ = R^♯` applied to `MZ` with its row `∅` replaced by
  `(p^{eK}, 0, …, 0)`, which does not change the rows `[N − r, N)` for `r ≤ N − 1`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset Matrix TheoremF AntitonicFit

variable (p : ℕ) [hp : Fact p.Prime]

/-- *Part Z* of `CSI18_theorem_4_4_smith_form_of_Mp.md`:
`x^♯ q := R^♯(dancer_I (q+1)) − R^♯(I ∖ dancer_I (q+1))` (CSI13's `R^♯`, for `q < N − 1`). -/
def oddSmithXSharp (l e : ℕ) : ℕ → ℤ := fun q =>
  rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (dancer (Iset p l) (q + 1)) -
    rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (Iset p l \ dancer (Iset p l) (q + 1))

/-- *Part Z* of `CSI18_theorem_4_4_smith_form_of_Mp.md`: `ŷ^♯ := ifit (N − 1) x^♯`. -/
def oddSmithYhatSharp (l e : ℕ) : ℕ → ℤ := ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e)

/-- The position `0` (the dancer `∅`) of the o-order (Part Z of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithZeroPos (l : ℕ) : Fin (2 ^ #(Iset p l)) := ⟨0, Nat.two_pow_pos _⟩

/-- `R^♯ = R_{H^♯}`, `H^♯ = (I, k, p^k − 1, e, d)` (CSI13 (L3); proof of Part Z of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
lemma oddSmith_rulerSharp_eq_RHP (l e : ℕ) {E : Finset ℕ} (hE : E ⊆ Iset p l) :
    rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) E =
      RHP p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1) (e : ℤ) E := by
  have hk := kappaP_K_sub_one (p := p) (k := kTop p l) (dk := 1) le_rfl
    (by have := hp.out.two_le; omega) (dg := digitL p l) (E := E)
    (fun t ht => Iset_lt p (hE ht)) (fun t ht => Iset_digit p (hE ht))
  rw [one_mul] at hk
  rw [RHP_eq_rulerP, rulerP, sum_h_sub_oW, hk, rulerSharpP_eq]

/-- **(Z1)** (Part Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for `i = 0` (and `e ≥ 1`), the row of
`∅` (position `0`) of `MZ` is zero, `det MZ = 0`, and if `I = ∅` (one slot) then `MZ = 0`. -/
theorem oddSmith_Z1 (l e : ℕ) (he : 1 ≤ e) :
    (∀ q', oddSmithMZ p l 0 e (oddSmithZeroPos p l) q' = 0) ∧ (oddSmithMZ p l 0 e).det = 0 ∧
      (Iset p l = ∅ → oddSmithMZ p l 0 e = 0) := by
  have hrow : ∀ q', oddSmithMZ p l 0 e (oddSmithZeroPos p l) q' = 0 := fun q' =>
    oddSmith_MZ_eq_zero_of (P2_zero_row p l e he _ _ (by
      rw [oddSmith_labL_slot]; exact dancer_zero _))
  refine ⟨hrow, det_eq_zero_of_row_eq_zero _ hrow, fun hI => ?_⟩
  ext q q'
  have hq : q = oddSmithZeroPos p l := by
    have h2 := q.2
    have h3 : 2 ^ #(Iset p l) = 1 := by rw [hI, card_empty, pow_zero]
    exact Fin.ext (by simp [oddSmithZeroPos]; omega)
  rw [hq, hrow]; rfl

/-- The entries for `i = 0` on nested pairs with `D ≠ ∅` (CSI13 (P2), `P2_zero`; proof of (Z2) of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
lemma oddSmith_Z_val (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (q q' : Fin (2 ^ #(Iset p l)))
    (hq : (q : ℕ) ≠ 0) (h : dancer (Iset p l) q' ⊆ dancer (Iset p l) q) :
    oddSmithMZ p l 0 e q q' ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (dancer (Iset p l) q) -
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (dancer (Iset p l) q') +
          Rulers.gamma (kTop p l) (Iset p l) (dancer (Iset p l) q \ dancer (Iset p l) q') ∧
        (p : ℤ) ^ n ∣ oddSmithMZ p l 0 e q q' ∧ ¬ (p : ℤ) ^ (n + 1) ∣ oddSmithMZ p l 0 e q q' := by
  have hba : labL p l 0 e (kTop p l) (oddSmithSlot p l 0 e q') ⊆
      labL p l 0 e (kTop p l) (oddSmithSlot p l 0 e q) := by
    rw [oddSmith_labL_slot, oddSmith_labL_slot]; exact h
  have hx : labL p l 0 e (kTop p l) (oddSmithSlot p l 0 e q) ≠ ∅ := by
    rw [oddSmith_labL_slot, Ne, DanceSmith.dancer_eq_empty_iff q.2]; exact hq
  obtain ⟨h0, hv⟩ := P2_zero p hodd l e he _ _ hx hba
  simp only [oddSmith_labL_slot] at hv
  rw [← oddSmith_MZ_cast] at h0 hv
  refine ⟨fun hz => h0 (by rw [hz, Int.cast_zero]), _, ?_, oddSmith_exact_of_valuation p h0⟩
  rw [hv, oddSmithK]

/-! ### Floor for `i = 0` -/

/-- The floor for `i = 0` (`SmithBounds.lemma_A1` with CSI17 Part B for `H^♯` with zero penalties;
proof of (Z2) of `CSI18_theorem_4_4_smith_form_of_Mp.md`): every `r × r` minor of `MZ` is divisible
by `p^{r e K + Σ_{[N − r, N)} ŷ_{H^♯}}`. -/
lemma oddSmith_Z_floor (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) {r : ℕ}
    (B D : Finset (Fin (2 ^ #(Iset p l)))) (hB : B.card = r) (hD : D.card = r) :
    (p : ℤ) ^ ((r : ℤ) * ((e : ℤ) * (oddSmithK p l : ℤ)) +
      ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)),
        yhatP p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1) (e : ℤ) j).toNat ∣
      Divisors.minor (oddSmithMZ p l 0 e) r B D := by
  have hℓ : p ^ (kTop p l) - 1 < p ^ (kTop p l) := by have := pow_pos hp.out.pos (kTop p l); omega
  refine oddSmith_floor_minor (oddSmithMZ p l 0 e) (CellFloor.IsCellArrow (Iset p l))
    (fun a b => cHatSeqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) a b)
    ((e : ℤ) * (oddSmithK p l : ℤ)) _ (fun a b h => ?_) (fun a b h => ?_) (fun Rows β hm => ?_)
    B D hB hD
  · exact oddSmith_MZ_off p l 0 e he a b (fun hsub => h ⟨a.2, b.2, hsub⟩)
  · by_cases ha : (a : ℕ) = 0
    · have ha' : a = oddSmithZeroPos p l := Fin.ext ha
      have hb : (b : ℕ) = 0 := by
        have h2 := h.2.2
        rw [ha, dancer_zero] at h2
        exact (DanceSmith.dancer_eq_empty_iff b.2).1 (subset_empty.1 h2)
      simp only [ha, hb, oddCell_cHat_self, add_zero]
      rw [ha', (oddSmith_Z1 p l e he).1]
      exact ⟨by positivity, dvd_zero _⟩
    · obtain ⟨-, n, hn, h1, -⟩ := oddSmith_Z_val p hodd l e he a b ha h.2.2
      have hc : (e : ℤ) * (oddSmithK p l : ℤ) +
          cHatSeqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) a b = n := by
        rw [hn, cHatSeqP, cHatHP, oddSmith_rulerSharp_eq_RHP p l e (lemma_0a _ _),
          oddSmith_rulerSharp_eq_RHP p l e (lemma_0a _ _)]
        ring
      show 0 ≤ (e : ℤ) * (oddSmithK p l : ℤ) +
          cHatSeqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) a b ∧ _
      rw [hc, Int.toNat_natCast]
      exact ⟨by positivity, h1⟩
  · have hfl := oddCell_theorem_B_floor (oddSmith_hI p l) (oddSmith_hd p l) hℓ (e := (e : ℤ))
      (by exact_mod_cast he) 0 0 hm
    have hcl : oddCellClock p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) 0 0 =
        xHseqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) := by
      funext q; simp [oddCellClock]
    have hco : ∀ a b, oddCellCost p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) 0 0 a b =
        cHatSeqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) a b := by
      intro a b; simp [oddCellCost]
    rw [hcl] at hfl
    simp only [hco] at hfl
    unfold SmithBounds.tailSum at hfl
    have h' : ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)),
        ifit (2 ^ #(Iset p l)) (xHseqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ)) j ≤
        ∑ a ∈ Rows, cHatSeqP p (kTop p l) (Iset p l) (digitL p l) (p ^ (kTop p l) - 1) (e : ℤ) a (β a) := by
      simp only at hfl
      exact_mod_cast hfl
    exact h'

/-! ### Ceiling for `i = 0` -/

lemma oddSmith_not_pow_succ_dvd_pow (n : ℕ) : ¬ (p : ℤ) ^ (n + 1) ∣ (p : ℤ) ^ n := fun h => by
  have h1 := Int.le_of_dvd (by have := hp.out.pos; positivity) h
  have h2 : (p : ℤ) ^ n < (p : ℤ) ^ (n + 1) :=
    pow_lt_pow_right₀ (by exact_mod_cast hp.out.one_lt) (by omega)
  linarith

/-- The ceiling for `i = 0` (CSI14 (C1) with `R₁ = R₂ = R^♯`, applied to `MZ` with the row `∅`
replaced by `(p^{eK}, 0, …, 0)`; proof of (Z2) of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for
`r ≤ N − 1`, the minor of `MZ` on the rows `[N − r, N)` and the columns `[0, r)` is non-zero of
`p`-valuation `r e K + Σ_{j ∈ [N − 1 − r, N − 1)} x^♯ j`. -/
lemma oddSmith_Z_ceil (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) {r : ℕ}
    (hr : r ≤ 2 ^ #(Iset p l) - 1) :
    Divisors.minor (oddSmithMZ p l 0 e) r (DanceSmith.lastSet _ r) (DanceSmith.firstSet _ r) ≠ 0 ∧
      (padicValInt p (Divisors.minor (oddSmithMZ p l 0 e) r (DanceSmith.lastSet _ r)
        (DanceSmith.firstSet _ r)) : ℤ) =
        r * ((e : ℤ) * (oddSmithK p l : ℤ)) +
          ∑ j ∈ Ico (2 ^ #(Iset p l) - 1 - r) (2 ^ #(Iset p l) - 1), oddSmithXSharp p l e j := by
  set N := 2 ^ #(Iset p l) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  set MZ := oddSmithMZ p l 0 e
  set Rs := rulerSharpP p e (kTop p l) (Iset p l) (digitL p l)
  set C : ℤ := (e : ℤ) * (oddSmithK p l : ℤ)
  have hC0 : 0 ≤ C := by positivity
  set Mo' : ℕ → ℕ → ℤ := fun a b => if h : a < N ∧ b < N then MZ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hMo' : ∀ a b : Fin N, Mo' a b = MZ a b := fun a b => by simp [Mo', a.2, b.2]
  set M' : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    if a = ∅ then (if b = ∅ then (p : ℤ) ^ C.toNat else 0)
    else Mo' (GoldenMatching.rank (Iset p l) a) (GoldenMatching.rank (Iset p l) b)
  have hrk : ∀ {a}, a ⊆ (Iset p l) → GoldenMatching.rank (Iset p l) a < N := fun ha => GoldenMatching.rank_lt ha
  have hM' : ∀ {a b} (ha : a ⊆ (Iset p l)) (hb : b ⊆ (Iset p l)), a ≠ ∅ →
      M' a b = MZ ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ := fun ha hb ha0 => by
    simp only [M', if_neg ha0]
    exact hMo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩
  obtain ⟨n, hn, h1, h2⟩ := oddSmith_ceiling hp.out (kTop p l) (oddSmith_hI p l) Rs Rs C M'
    (fun a b ha hb hab => by
      by_cases ha0 : a = ∅
      · have hb0 : b ≠ ∅ := by rintro rfl; exact hab (empty_subset _)
        simp [M', ha0, hb0]
      · rw [hM' ha hb ha0]
        exact oddSmith_MZ_off p l 0 e he _ _
          (by simp only; rw [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb]; exact hab))
    (fun a b hba ha => by
      have hb := hba.trans ha
      by_cases ha0 : a = ∅
      · subst ha0
        obtain rfl := subset_empty.1 hba
        refine ⟨C.toNat, by simp [cHatP, Rulers.gamma, Int.toNat_of_nonneg hC0], ?_, ?_⟩
        · simp [M']
        · simp only [M', if_pos rfl]; exact oddSmith_not_pow_succ_dvd_pow p _
      · have hq : GoldenMatching.rank (Iset p l) a ≠ 0 := by
          intro h0; apply ha0; rw [← DanceSmith.dancer_rank ha, h0, dancer_zero]
        rw [hM' ha hb ha0]
        obtain ⟨-, n, hn, h⟩ := oddSmith_Z_val p hodd l e he ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ hq
          (by simp only; rw [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb]; exact hba)
        simp only [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb] at hn
        exact ⟨n, by rw [hn, cHatP]; ring, h⟩)
    (r := r) (by omega)
  have hmat : (Matrix.of fun i' j : Fin r => M' (dancer (Iset p l) (N - r + i')) (dancer (Iset p l) j)) =
      Matrix.of fun i' j : Fin r => MZ ⟨N - r + i', by omega⟩ ⟨j, by omega⟩ := by
    ext i' j
    have hi' := i'.2
    have hj' := j.2
    have hq : N - r + i' < 2 ^ #(Iset p l) := by omega
    rw [Matrix.of_apply, Matrix.of_apply, hM' (lemma_0a _ _) (lemma_0a _ _)
      (by rw [Ne, DanceSmith.dancer_eq_empty_iff hq]; omega)]
    simp only [lemma_0c_rank hq, lemma_0c_rank (show (j : ℕ) < 2 ^ #(Iset p l) by omega)]
  rw [hmat] at h1 h2
  rw [DanceSmith.minor_last_first _ (by omega)]
  obtain ⟨h0, hv⟩ := oddSmith_padicValInt_eq_of_exact h1 h2
  refine ⟨h0, ?_⟩
  rw [hv, hn]
  congr 1
  simp only [oddSmithXSharp, xP]
  rw [sum_Ico_add' (fun j => Rs (dancer (Iset p l) j) - Rs ((Iset p l) \ dancer (Iset p l) j)),
    show N - 1 - r + 1 = N - r by omega, show N - 1 + 1 = N by omega]

/-! ### Conclusion for `i = 0` -/

/-- `ŷ^♯(j) = ŷ_{H^♯}(j + 1)` for `j < N − 1` and `I ≠ ∅` (CSI17 (I3); proof of (Z2) of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
lemma oddSmith_yhatSharp_succ (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) {j : ℕ}
    (hj : j < 2 ^ #(Iset p l) - 1) :
    oddSmithYhatSharp p l e j =
      yhatP p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1) (e : ℤ) (j + 1) := by
  have hx : oddSmithXSharp p l e =
      oddCellXSharp p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1) (e : ℤ) := by
    funext q
    simp only [oddSmithXSharp, oddCellXSharp, xHseqP, xHP]
    rw [oddSmith_rulerSharp_eq_RHP p l e (lemma_0a _ _),
      oddSmith_rulerSharp_eq_RHP p l e sdiff_subset]
  rw [oddSmithYhatSharp, hx]
  exact (oddCell_lemma_7_9_I3 (oddSmith_hI p l) (oddSmith_hd p l) rfl (e := (e : ℤ))
    (by exact_mod_cast he) hne).2.2.2.2.1 j hj

/-- The conclusion for `i = 0` (CSI14 (Q1), (Q2) and C5's `Divisors.theorem_B_without_M` on `N − 1`
positions; proof of (Z2) and (Z3) of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
theorem oddSmith_Z_main (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    (∀ r ≤ 2 ^ #(Iset p l) - 1, (ddP p (oddSmithMZ p l 0 e) r : ℤ) =
      r * ((e : ℤ) * (oddSmithK p l : ℤ)) +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - 1 - r) (2 ^ #(Iset p l) - 1), oddSmithYhatSharp p l e j) ∧
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
          (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
            oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 1 - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧ P * oddSmithMZ p l 0 e * Q =
          diagonal (fun j : Fin (2 ^ #(Iset p l)) =>
            if (j : ℕ) < 2 ^ #(Iset p l) - 1 then u j * (p : ℤ) ^ E j else 0) := by
  set N := 2 ^ #(Iset p l) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  refine oddSmith_smith_of_bounds hp.out (oddSmithMZ p l 0 e) (N' := N - 1) (by omega)
    (oddSmithXSharp p l e) ((e : ℤ) * (oddSmithK p l : ℤ))
    (fun r hr B D hB hD => ?_)
    (fun r hr => ⟨DanceSmith.lastSet _ r, DanceSmith.firstSet _ r, DanceSmith.card_lastSet (by omega),
      DanceSmith.card_firstSet (by omega), (oddSmith_Z_ceil p hodd l e he hr).1,
      (oddSmith_Z_ceil p hodd l e he hr).2.le⟩)
    (fun _ B D hB hD => ?_)
  · have hsum : ∑ j ∈ Ico (N - 1 - r) (N - 1), ifit (N - 1) (oddSmithXSharp p l e) j =
        ∑ j ∈ Ico (N - r) N,
          yhatP p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1) (e : ℤ) j := by
      rw [show ∑ j ∈ Ico (N - 1 - r) (N - 1), ifit (N - 1) (oddSmithXSharp p l e) j =
          ∑ j ∈ Ico (N - 1 - r) (N - 1), yhatP p (kTop p l) (Iset p l) (digitL p l)
            (p ^ kTop p l - 1) (e : ℤ) (j + 1) from
        sum_congr rfl fun j hj => oddSmith_yhatSharp_succ p l e he hne
          (by simp only [mem_Ico] at hj; omega)]
      rw [sum_Ico_add' (fun j => yhatP p (kTop p l) (Iset p l) (digitL p l) (p ^ kTop p l - 1)
          (e : ℤ) j), show N - 1 - r + 1 = N - r by omega, show N - 1 + 1 = N by omega]
    rw [hsum]
    exact oddSmith_Z_floor p hodd l e he B D hB hD
  · have e1 : N - 1 + 1 = N := by omega
    rw [e1] at hB hD ⊢
    rw [eq_univ_of_card B (by simpa using hB), eq_univ_of_card D (by simpa using hD),
      Divisors.minor_univ]
    exact (oddSmith_Z1 p l e he).2.1

/-- **(Z2)** (Part Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for an odd prime `p`, `i = 0`,
`e ≥ 1`, `I ≠ ∅` and every `r ≤ N − 1`, `ddP p MZ r = r·e·K + Σ_{j ∈ [N − 1 − r, N − 1)} ŷ^♯ j`; and
`ŷ^♯` is non-increasing on `[0, N − 1)`. -/
theorem oddSmith_Z2 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    (∀ r ≤ 2 ^ #(Iset p l) - 1, (ddP p (oddSmithMZ p l 0 e) r : ℤ) =
      r * ((e : ℤ) * (oddSmithK p l : ℤ)) +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - 1 - r) (2 ^ #(Iset p l) - 1), oddSmithYhatSharp p l e j) ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) - 1 →
      oddSmithYhatSharp p l e (j + 1) ≤ oddSmithYhatSharp p l e j) := by
  refine ⟨(oddSmith_Z_main p hodd l e he hne).1, fun j hj => ?_⟩
  rw [oddSmith_yhatSharp_succ p l e he hne hj, oddSmith_yhatSharp_succ p l e he hne (by omega)]
  exact (oddCell_lemma_7_9_I1 (oddSmith_hI p l) (oddSmith_hd p l)
    (by have := pow_pos hp.out.pos (kTop p l); omega) (e := (e : ℤ))
    (by exact_mod_cast he)).2 (j + 1) (by omega)

/-- **(Z3)** (Part Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for an odd prime `p`, `i = 0`,
`e ≥ 1` and `I ≠ ∅` there are `P, Q` over `ℤ` with `p ∤ det P`, `p ∤ det Q` and integers `u j` with
`p ∤ u j` such that `P·MZ·Q = diagonal (j ↦ if j < N − 1 then u j · p^{eK + ŷ^♯(N − 2 − j)} else 0)`
(the exponent is a natural number `E j` with `E j = eK + ŷ^♯(N − 2 − j)` in `ℤ`). For `I = ∅`,
`MZ = 0` is (Z1). -/
theorem oddSmith_Z3 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
            (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
              oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
          P * oddSmithMZ p l 0 e * Q = diagonal (fun j : Fin (2 ^ #(Iset p l)) =>
            if (j : ℕ) < 2 ^ #(Iset p l) - 1 then u j * (p : ℤ) ^ E j else 0) := by
  obtain ⟨-, P, Q, hP, hQ, E, hE, u, hu, hD⟩ := oddSmith_Z_main p hodd l e he hne
  refine ⟨P, Q, hP, hQ, u, hu, E, fun j hj => ?_, hD⟩
  rw [hE j hj, show 2 ^ #(Iset p l) - 1 - 1 - j = 2 ^ #(Iset p l) - 2 - j by omega]

end ColouredSand.OddTwist
