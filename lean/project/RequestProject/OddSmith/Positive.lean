module

public import RequestProject.OddSmith.Bounds

/-!
# Part S of `CSI18_theorem_4_4_smith_form_of_Mp.md`: the case `i ≥ 1` (Theorem 4.4)

## Encoding

* `m = i − 1`; `oddSmithC p l i e = e·K + κ_p(m, K)` is `C` (CSI13's `kappaP`);
* the clocks `oddSmithX p l i e q = R_m(dancer_I q) − R_{m+K}(I ∖ dancer_I q)` are `x q`, with CSI13's
  rulers `rulerP p e k I d μ`; `oddSmithYhat p l i e = AntitonicFit.ifit N x` is `ŷ`;
* the matrix is `MZ = oddSmithMZ p l i e : Matrix (Fin N) (Fin N) ℤ` (Part Z0);
* exponents that the file writes as integers known to be natural are natural numbers `n`, `E j`
  together with the equation in `ℤ`;
* "`ŷ` non-increasing on `[0, N)`" is `∀ j, j + 1 < N → ŷ (j + 1) ≤ ŷ j`.

The penalty cell of the proof is CSI17's `Cell(H; r_k(m), r_k(m + K))` for the house
`H = (I, k, m mod p^k, e, d)`: its costs and clocks are CSI15 (A3) (`oddSmith_cellCost_eq`,
`oddSmith_cellClock_eq`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset Matrix TheoremF AntitonicFit

variable (p : ℕ) [hp : Fact p.Prime]

/-- *Part S* of `CSI18_theorem_4_4_smith_form_of_Mp.md`: `C := e·K + κ_p(i − 1, K)`. -/
def oddSmithC (l i e : ℕ) : ℤ := (e : ℤ) * (oddSmithK p l : ℤ) + kappaP p (i - 1) (oddSmithK p l)

/-- *Part S* of `CSI18_theorem_4_4_smith_form_of_Mp.md`: the clocks
`x q := R_m(dancer_I q) − R_{m+K}(I ∖ dancer_I q)`, `m = i − 1` (CSI13's rulers). -/
def oddSmithX (l i e : ℕ) : ℕ → ℤ := fun q =>
  rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
    rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)
      (Iset p l \ dancer (Iset p l) q)

/-- *Part S* of `CSI18_theorem_4_4_smith_form_of_Mp.md`: `ŷ := ifit N x`. -/
def oddSmithYhat (l i e : ℕ) : ℕ → ℤ := ifit (2 ^ #(Iset p l)) (oddSmithX p l i e)

omit hp in
lemma oddSmith_hI (l : ℕ) : ∀ t ∈ Iset p l, t < kTop p l := fun _ ht => Iset_lt p ht

lemma oddSmith_hd (l : ℕ) : ∀ t ∈ Iset p l, 1 ≤ digitL p l t ∧ digitL p l t ≤ p - 1 :=
  fun t ht => by have := Iset_digit p ht; omega

variable {p} in
lemma oddSmith_MZ_eq_zero_of {l i e : ℕ} {q q' : Fin (2 ^ #(Iset p l))}
    (h : Mp p l i e (oddSmithSlot p l i e q) (oddSmithSlot p l i e q') = 0) :
    oddSmithMZ p l i e q q' = 0 := by
  have := oddSmith_MZ_cast p l i e q q'
  rw [h] at this
  exact_mod_cast this

/-- Off the nested pairs, `MZ` vanishes (CSI13 (P2), `P2_support`; any `i`). -/
lemma oddSmith_MZ_off (l i e : ℕ) (he : 1 ≤ e) (q q' : Fin (2 ^ #(Iset p l)))
    (h : ¬ dancer (Iset p l) q' ⊆ dancer (Iset p l) q) : oddSmithMZ p l i e q q' = 0 :=
  oddSmith_MZ_eq_zero_of (P2_support p l i e he _ _ (by
    rw [oddSmith_labL_slot, oddSmith_labL_slot]; exact h))

/-- **(S1) entries** (Part S of `CSI18_theorem_4_4_smith_form_of_Mp.md`, from CSI13 (P2)): for an odd
prime `p`, `e ≥ 1`, `i ≥ 1` and positions `q, q'` with `a = dancer_I q`, `b = dancer_I q'`:
`MZ q q' = 0` if `b ⊄ a`; otherwise `MZ q q' ≠ 0`, and `p^n ∣ MZ q q'`, `p^{n+1} ∤ MZ q q'` for the
natural number `n` with `n = C + R_m(a) − R_{m+K}(b) + γ(a ∖ b)`. -/
theorem oddSmith_S1 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i)
    (q q' : Fin (2 ^ #(Iset p l))) :
    (¬ dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' = 0) ∧
    (dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = oddSmithC p l i e +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)
            (dancer (Iset p l) q') +
          Rulers.gamma (kTop p l) (Iset p l) (dancer (Iset p l) q \ dancer (Iset p l) q') ∧
        (p : ℤ) ^ n ∣ oddSmithMZ p l i e q q' ∧ ¬ (p : ℤ) ^ (n + 1) ∣ oddSmithMZ p l i e q q') := by
  refine ⟨oddSmith_MZ_off p l i e he q q', fun h => ?_⟩
  have hba : labL p l i e (kTop p l) (oddSmithSlot p l i e q') ⊆
      labL p l i e (kTop p l) (oddSmithSlot p l i e q) := by
    rw [oddSmith_labL_slot, oddSmith_labL_slot]; exact h
  obtain ⟨h0, hv⟩ := P2_pos p hodd l i e he hi _ _ hba
  simp only [oddSmith_labL_slot] at hv
  rw [← oddSmith_MZ_cast] at h0 hv
  refine ⟨fun hz => h0 (by rw [hz, Int.cast_zero]), _, ?_, oddSmith_exact_of_valuation p h0⟩
  rw [hv, oddSmithC, oddSmithK]

/-! ### The penalty cell (CSI15 (A3)) -/

/-- The cell costs of `Cell(H; r_k(m), r_k(m + K))`, `H = (I, k, m mod p^k, e, d)`, are the costs
`ĉ(a, b) = R_m(a) − R_{m+K}(b) + γ(a ∖ b)` (CSI15 (A3), `houseP_A3_cost`; proof of (S2)). -/
lemma oddSmith_cellCost_eq (l i e : ℕ) (a b : ℕ) :
    oddCellCost p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
        (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l)) a b =
      cHatP (kTop p l) (Iset p l) (rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1))
        (rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l))
        (dancer (Iset p l) a) (dancer (Iset p l) b) := by
  have h : rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) a) -
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + digitL p l (kTop p l) * p ^ kTop p l)
        (dancer (Iset p l) b) +
      Rulers.gamma (kTop p l) (Iset p l) (dancer (Iset p l) a \ dancer (Iset p l) b) =
      cHatHP p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
          (dancer (Iset p l) a) (dancer (Iset p l) b) -
        (rP p (kTop p l) (i - 1) : ℤ) *
          JHP p (kTop p l) (digitL p l) ((i - 1) % p ^ kTop p l) (dancer (Iset p l) a) +
        (rP p (kTop p l) (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) : ℤ) *
          JHP p (kTop p l) (digitL p l) ((i - 1) % p ^ kTop p l) (dancer (Iset p l) b) :=
    houseP_A3_cost (oddSmith_hI p l) (oddSmith_hd p l) (e : ℤ) _ (i - 1) (lemma_0a _ _)
      (lemma_0a _ _)
  simp only [oddCellCost, cHatSeqP, JHseqP, cHatP, oddSmithK]
  rw [h]

/-- The cell clocks of `Cell(H; r_k(m), r_k(m + K))` are the clocks `x` (CSI15 (A3),
`houseP_A3_clock`; proof of (S2)). -/
lemma oddSmith_cellClock_eq (l i e : ℕ) {q : ℕ} (hq : q < 2 ^ #(Iset p l)) :
    oddCellClock p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
        (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l)) q =
      oddSmithX p l i e q := by
  have h : rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + digitL p l (kTop p l) * p ^ kTop p l)
        (Iset p l \ dancer (Iset p l) q) =
      xHP p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
          (dancer (Iset p l) q) -
        (rP p (kTop p l) (i - 1) : ℤ) *
          JHP p (kTop p l) (digitL p l) ((i - 1) % p ^ kTop p l) (dancer (Iset p l) q) +
        (rP p (kTop p l) (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) : ℤ) *
          JHP p (kTop p l) (digitL p l) ((i - 1) % p ^ kTop p l) (Iset p l \ dancer (Iset p l) q) :=
    houseP_A3_clock (oddSmith_hI p l) (oddSmith_hd p l) (e : ℤ) _ (i - 1) (lemma_0a _ _)
  simp only [oddCellClock, xHseqP, JHseqP, oddSmithX, oddSmithK]
  rw [lemma_0d hq, h]

lemma oddSmith_ifit_cellClock (l i e : ℕ) :
    ifit (2 ^ #(Iset p l))
      (oddCellClock p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
        (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l))) =
      oddSmithYhat p l i e :=
  DanceSmith.ifit_congr fun _ hj => oddSmith_cellClock_eq p l i e hj

/-! ### Floor and ceiling -/

/-- The floor for `i ≥ 1` (`SmithBounds.lemma_A1` with CSI15 (A3), CSI17 Part B and
`SmithBounds.theorem_U`; proof of (S2) of `CSI18_theorem_4_4_smith_form_of_Mp.md`): every `r × r`
minor of `MZ` is divisible by `p^{r C + Σ_{[N − r, N)} ŷ}`. -/
lemma oddSmith_S_floor (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) {r : ℕ}
    (B D : Finset (Fin (2 ^ #(Iset p l)))) (hB : B.card = r) (hD : D.card = r) :
    (p : ℤ) ^ ((r : ℤ) * oddSmithC p l i e + ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)),
      ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) j).toNat ∣
      Divisors.minor (oddSmithMZ p l i e) r B D := by
  set R₁ := rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1)
  set R₂ := rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)
  refine oddSmith_floor_minor (oddSmithMZ p l i e) (CellFloor.IsCellArrow (Iset p l))
    (fun a b => cHatP (kTop p l) (Iset p l) R₁ R₂ (dancer (Iset p l) a) (dancer (Iset p l) b))
    (oddSmithC p l i e) _
    (fun a b h => ?_) (fun a b h => ?_) (fun Rows β hm => ?_) B D hB hD
  · exact oddSmith_MZ_off p l i e he a b (fun hsub => h ⟨a.2, b.2, hsub⟩)
  · obtain ⟨-, n, hn, h1, -⟩ := (oddSmith_S1 p hodd l i e he hi a b).2 h.2.2
    have hc : oddSmithC p l i e +
        cHatP (kTop p l) (Iset p l) R₁ R₂ (dancer (Iset p l) a) (dancer (Iset p l) b) = n := by
      rw [hn, cHatP]; ring
    show 0 ≤ oddSmithC p l i e +
      cHatP (kTop p l) (Iset p l) R₁ R₂ (dancer (Iset p l) a) (dancer (Iset p l) b) ∧ _
    rw [hc, Int.toNat_natCast]
    exact ⟨by positivity, h1⟩
  · have hfl := oddCell_theorem_B_floor (oddSmith_hI p l) (oddSmith_hd p l)
      (Nat.mod_lt (i - 1) (pow_pos hp.out.pos (kTop p l))) (e := (e : ℤ)) (by exact_mod_cast he)
      (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l)) hm
    unfold SmithBounds.tailSum at hfl
    have h' : ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)), ifit (2 ^ #(Iset p l))
        (oddCellClock p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l) (e : ℤ)
          (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l))) j ≤
        ∑ a ∈ Rows, oddCellCost p (kTop p l) (Iset p l) (digitL p l) ((i - 1) % p ^ kTop p l)
          (e : ℤ) (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l)) a (β a) := by
      simp only at hfl
      exact_mod_cast hfl
    rw [oddSmith_ifit_cellClock] at h'
    simp only [oddSmith_cellCost_eq] at h'
    exact h'

/-- The ceiling for `i ≥ 1` (CSI14 (C1) with `R₁ = R_m`, `R₂ = R_{m+K}`; proof of (S2) of
`CSI18_theorem_4_4_smith_form_of_Mp.md`): the minor of `MZ` on the rows `[N − r, N)` and the columns
`[0, r)` is non-zero of `p`-valuation `r C + Σ_{[N − r, N)} x`. -/
lemma oddSmith_S_ceil (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) {r : ℕ}
    (hr : r ≤ 2 ^ #(Iset p l)) :
    Divisors.minor (oddSmithMZ p l i e) r (DanceSmith.lastSet _ r) (DanceSmith.firstSet _ r) ≠ 0 ∧
      (padicValInt p (Divisors.minor (oddSmithMZ p l i e) r (DanceSmith.lastSet _ r)
        (DanceSmith.firstSet _ r)) : ℤ) =
        r * oddSmithC p l i e +
          ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)), oddSmithX p l i e j := by
  set N := 2 ^ #(Iset p l) with hN
  set MZ := oddSmithMZ p l i e
  set Mo' : ℕ → ℕ → ℤ := fun a b => if h : a < N ∧ b < N then MZ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hMo' : ∀ a b : Fin N, Mo' a b = MZ a b := fun a b => by simp [Mo', a.2, b.2]
  set M' : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    Mo' (GoldenMatching.rank (Iset p l) a) (GoldenMatching.rank (Iset p l) b)
  have hrk : ∀ {a}, a ⊆ Iset p l → GoldenMatching.rank (Iset p l) a < N :=
    fun ha => GoldenMatching.rank_lt ha
  have hM' : ∀ {a b} (ha : a ⊆ Iset p l) (hb : b ⊆ Iset p l),
      M' a b = MZ ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ :=
    fun ha hb => hMo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩
  obtain ⟨n, hn, h1, h2⟩ := oddSmith_ceiling hp.out (kTop p l) (oddSmith_hI p l)
    (rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1))
    (rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)) (oddSmithC p l i e) M'
    (fun a b ha hb hab => by
      rw [hM' ha hb]
      exact oddSmith_MZ_off p l i e he _ _
        (by simp only; rw [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb]; exact hab))
    (fun a b hba ha => by
      have hb := hba.trans ha
      rw [hM' ha hb]
      obtain ⟨-, n, hn, h⟩ := (oddSmith_S1 p hodd l i e he hi ⟨_, hrk ha⟩ ⟨_, hrk hb⟩).2
        (by simp only; rw [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb]; exact hba)
      simp only [DanceSmith.dancer_rank ha, DanceSmith.dancer_rank hb] at hn
      exact ⟨n, by rw [hn, cHatP]; ring, h⟩)
    (r := r) hr
  have hmat : (Matrix.of fun i' j : Fin r =>
      M' (dancer (Iset p l) (N - r + i')) (dancer (Iset p l) j)) =
      Matrix.of fun i' j : Fin r => MZ ⟨N - r + i', by omega⟩ ⟨j, by omega⟩ := by
    ext i' j
    simp only [Matrix.of_apply, M']
    have hi' := i'.2
    have hj' := j.2
    rw [lemma_0c_rank (show N - r + i' < 2 ^ #(Iset p l) by omega),
      lemma_0c_rank (show (j : ℕ) < 2 ^ #(Iset p l) by omega)]
    exact hMo' ⟨N - r + i', by omega⟩ ⟨j, by omega⟩
  rw [hmat] at h1 h2
  rw [DanceSmith.minor_last_first _ hr]
  obtain ⟨h0, hv⟩ := oddSmith_padicValInt_eq_of_exact h1 h2
  refine ⟨h0, ?_⟩
  rw [hv, hn]
  rfl

/-! ### Conclusion -/

/-- The conclusion for `i ≥ 1` (CSI14 (Q1), (Q2) and C5's `Divisors.theorem_B_without_M`; proof of
(S2) and (S3) of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
theorem oddSmith_S_main (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ #(Iset p l), (ddP p (oddSmithMZ p l i e) r : ℤ) =
      r * oddSmithC p l i e +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)), oddSmithYhat p l i e j) ∧
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
          (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧ P * oddSmithMZ p l i e * Q =
          diagonal (fun j : Fin (2 ^ #(Iset p l)) =>
            if (j : ℕ) < 2 ^ #(Iset p l) then u j * (p : ℤ) ^ E j else 0) :=
  oddSmith_smith_of_bounds hp.out (oddSmithMZ p l i e) le_rfl (oddSmithX p l i e)
    (oddSmithC p l i e)
    (fun _ _ B D hB hD => oddSmith_S_floor p hodd l i e he hi B D hB hD)
    (fun r hr => ⟨DanceSmith.lastSet _ r, DanceSmith.firstSet _ r, DanceSmith.card_lastSet hr,
      DanceSmith.card_firstSet hr, (oddSmith_S_ceil p hodd l i e he hi hr).1,
      (oddSmith_S_ceil p hodd l i e he hi hr).2.le⟩)
    (fun h => absurd h (lt_irrefl _))

/-- **(S2) divisors** (Theorem 4.4, `i ≥ 1`; Part S of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for
an odd prime `p`, `e ≥ 1`, `i ≥ 1` and every `r ≤ N`,
`ddP p MZ r = r·C + Σ_{j ∈ [N − r, N)} ŷ j`; `det MZ ≠ 0`; and `ŷ` is non-increasing on `[0, N)`. -/
theorem oddSmith_S2 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ #(Iset p l), (ddP p (oddSmithMZ p l i e) r : ℤ) =
      r * oddSmithC p l i e +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)), oddSmithYhat p l i e j) ∧
    (oddSmithMZ p l i e).det ≠ 0 ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) → oddSmithYhat p l i e (j + 1) ≤ oddSmithYhat p l i e j) := by
  refine ⟨(oddSmith_S_main p hodd l i e he hi).1, ?_, ?_⟩
  · have h0 := (oddSmith_S_ceil p hodd l i e he hi (r := 2 ^ #(Iset p l)) le_rfl).1
    rwa [DanceSmith.lastSet_self, DanceSmith.firstSet_self, Divisors.minor_univ] at h0
  · have h := (oddCell_lemma_7_9_I2 (oddSmith_hI p l) (oddSmith_hd p l)
      (Nat.mod_lt (i - 1) (pow_pos hp.out.pos (kTop p l))) (e := (e : ℤ)) (by exact_mod_cast he)
      (rP p (kTop p l) (i - 1)) (rP p (kTop p l) (i - 1 + oddSmithK p l))).2.2
    rw [oddSmith_ifit_cellClock] at h
    exact h

/-- **(S3) Smith form** (Theorem 4.4, `i ≥ 1`; Part S of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for
an odd prime `p`, `e ≥ 1` and `i ≥ 1` there are `P, Q` over `ℤ` with `p ∤ det P`, `p ∤ det Q`, and
integers `u j` with `p ∤ u j`, such that `P·MZ·Q = diagonal (j ↦ u j · p^{C + ŷ(N − 1 − j)})` (the
exponent is a natural number `E j` with `E j = C + ŷ(N − 1 − j)` in `ℤ`). -/
theorem oddSmith_S3 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
            (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
          P * oddSmithMZ p l i e * Q =
            diagonal (fun j : Fin (2 ^ #(Iset p l)) => u j * (p : ℤ) ^ E j) := by
  obtain ⟨-, P, Q, hP, hQ, E, hE, u, hu, hD⟩ := oddSmith_S_main p hodd l i e he hi
  refine ⟨P, Q, hP, hQ, u, hu, E, hE, ?_⟩
  rw [hD]
  congr 1
  funext j
  exact if_pos j.2

end ColouredSand.OddTwist
