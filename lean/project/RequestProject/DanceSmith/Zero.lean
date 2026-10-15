module

public import RequestProject.DanceSmith.Positive

/-!
# Part Z of `C15_smith_form_of_the_dance_matrix.md`: the case `i = 0` (Theorem 7.10)

## Encoding

* `yHatS ds α = CellFloor.yhatSharp I k (2^k − 1) α` is `ŷ^♯` (the integer fit, on `N − 1`
  positions, of `x^♯ j = TheoremF.xHseq I k (2^k − 1) α (j + 1)`, i.e.
  `CellFloor.xSharp I k (2^k − 1) α`); `α` is cast to `ℤ`.
* "`I ≠ ∅`" is `Windows.Ids ds ≠ ∅`.
* `zeroPos ds : Fin N` is the position `0` (the dancer `∅`), and its slot is `sl ds (zeroPos ds)`.
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix TheoremF Windows

/-- *Setting* ("Clocks", `i = 0`) of `C15_smith_form_of_the_dance_matrix.md`:
`ŷ^♯ := CellFloor.yhatSharp I k (K − 1) α`. -/
noncomputable def yHatS (ds : List Bool) (α : ℕ) : ℕ → ℤ :=
  CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ)

/-- The position `0` of the o-order, as an element of `Fin N` (Part Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
def zeroPos (ds : List Bool) : Fin (2 ^ Dance.mCount ds) := ⟨0, Nat.two_pow_pos _⟩

/-- For `i = 0`, the row of the slot `sl(0)` (the dancer `∅`) of `M` is zero (proof of (Z1) of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma final_row_zero (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) (s' : Fin (2 ^ Dance.mCount ds)) :
    finalMatrix ℤ ds α 0 (sl ds (zeroPos ds)) s' = 0 := by
  have h0 : Dset ds (sl ds (zeroPos ds)) = ∅ := by
    rw [(P1 ds).2.2 (zeroPos ds)]; exact dancer_zero _
  by_cases h : Dset ds s' ⊆ Dset ds (sl ds (zeroPos ds))
  · have hM := (theorem_D_ii ds α 0 hα _ _).1 h
    have hD : Dset ds s' = ∅ := subset_empty.1 (h0 ▸ h)
    rw [h0, hD] at hM
    have hMc : Deficit.Mc (Ids ds) ds.length (α : ℤ) 0 ∅ ∅ = 0 := by
      unfold Deficit.Mc
      apply mul_eq_zero_of_right
      apply prod_eq_zero (i := 0)
      · simp [Rulers.oE_empty]
      · simp [Deficit.pi0]
    rw [hMc] at hM
    exact_mod_cast hM
  · exact (theorem_D_ii ds α 0 hα _ _).2 h

/-- **(Z1)** of `C15_smith_form_of_the_dance_matrix.md`: for `i = 0`, `det M = 0`; and if `I = ∅`
(so `N = 1`), then `M = 0`.  (The hypothesis `1 ≤ α` is passed on to `Windows.theorem_D_ii`; `k ≥ 1`
is not needed.) -/
theorem Z1 (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) :
    (finalMatrix ℤ ds α 0).det = 0 ∧ (Ids ds = ∅ → finalMatrix ℤ ds α 0 = 0) := by
  refine ⟨det_eq_zero_of_row_eq_zero _ (final_row_zero ds α hα), fun hI => ?_⟩
  have h1 : 2 ^ Dance.mCount ds = 1 := by rw [← card_Ids, hI, card_empty, pow_zero]
  ext s t
  have hs : s = sl ds (zeroPos ds) := by
    have h2 := s.2
    have h3 := (sl ds (zeroPos ds)).2
    exact Fin.ext (by omega)
  rw [hs]
  exact final_row_zero ds α hα t

lemma Mo_row_zero (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) (q : Fin (2 ^ Dance.mCount ds)) :
    Mo ds α 0 (zeroPos ds) q = 0 :=
  final_row_zero ds α hα (sl ds q)

lemma oE_dancer_pos {I : Finset ℕ} {p : ℕ} (hp0 : 0 < p) (hp : p < 2 ^ #I) :
    0 < Rulers.oE (dancer I p) := by
  have := lemma_0b hp0 hp (I := I)
  rwa [dancer_zero, Rulers.oE_empty] at this

/-- The entries for `i = 0` on nested pairs with `D ≠ ∅` (`Windows.theorem_D_iii` and
`Rulers.proposition_5_4_b`; proof of (Z2) of `C15_smith_form_of_the_dance_matrix.md`):
`v_2(Mo p q) = α K + ĉ_{H^♯}(p, q)`, the cost of the house `H^♯ = (I, k, K − 1, α)`. -/
lemma Z_val (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α)
    (p q : Fin (2 ^ Dance.mCount ds)) (hp : (p : ℕ) ≠ 0)
    (h : dancer (Ids ds) q ⊆ dancer (Ids ds) p) :
    Mo ds α 0 p q ≠ 0 ∧ (padicValInt 2 (Mo ds α 0 p q) : ℤ) =
      (α : ℤ) * 2 ^ ds.length + Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α p q := by
  have hpos : 0 < Rulers.oE (dancer (Ids ds) p) :=
    oE_dancer_pos (by omega) (by rw [two_pow_card_Ids]; exact p.2)
  have hne : dancer (Ids ds) p ≠ ∅ := by
    intro he; rw [he, Rulers.oE_empty] at hpos; exact lt_irrefl _ hpos
  obtain ⟨h0, hv⟩ := Mo_val ds hk α 0 hα p q h (by omega)
  simp only [zero_add] at hv
  rw [Rulers.proposition_5_4_b (hI_Ids ds) hne (lemma_0a _ _) h (α : ℤ)
    (by exact_mod_cast hα)] at hv
  refine ⟨h0, ?_⟩
  rw [hv]
  simp only [Potential.cHat, Houses.cHatH, Houses.RH, Rulers.rulerSharp, Rulers.ruler]
  ring

/-- The floor for `i = 0` (`SmithBounds.lemma_A1` with the potential of the house
`H^♯ = (I, k, K − 1, α)`, through `CellFloor.theorem_B_floor` with zero penalties; proof of (Z2) of
`C15_smith_form_of_the_dance_matrix.md`): every `r × r` minor of `Mo` is divisible by
`2^{r α K + Σ_{[N − r, N)} ŷ_{H^♯}}`.  The zero row of `∅` needs no special treatment here. -/
lemma Z_floor (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α)
    {r : ℕ} (B D : Finset (Fin (2 ^ Dance.mCount ds))) (hB : B.card = r) (hD : D.card = r) :
    (2 : ℤ) ^ ((r : ℤ) * ((α : ℤ) * 2 ^ ds.length) +
      ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds),
        AntitonicFit.ifit (2 ^ Dance.mCount ds) (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j
        ).toNat ∣ Divisors.minor (Mo ds α 0) r B D := by
  refine floor_minor (Mo ds α 0) (CellFloor.IsCellArrow (Ids ds))
    (fun p q => Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α p q)
    ((α : ℤ) * 2 ^ ds.length) _ (fun p q h => ?_) (fun p q h => ?_) (fun Rows β hm => ?_) B D hB hD
  · apply Mo_off ds α 0 hα
    intro hsub
    exact h ⟨by rw [two_pow_card_Ids]; exact p.2, by rw [two_pow_card_Ids]; exact q.2, hsub⟩
  · by_cases hp : (p : ℕ) = 0
    · have hp' : p = zeroPos ds := Fin.ext hp
      have hq : (q : ℕ) = 0 := by
        have h2 := h.2.2
        rw [hp, dancer_zero] at h2
        have h3 : dancer (Ids ds) q = dancer (Ids ds) 0 := by
          rw [dancer_zero]; exact subset_empty.1 h2
        exact CellFloor.dancer_inj (by rw [two_pow_card_Ids]; exact q.2) (by positivity) h3
      simp only [hp, hq, CellFloor.cHat_self, add_zero]
      rw [hp', Mo_row_zero ds α hα]
      exact ⟨by positivity, dvd_zero _⟩
    · obtain ⟨h0, hv⟩ := Z_val ds hk α hα p q hp h.2.2
      simp only
      rw [← hv, Int.toNat_natCast]
      exact ⟨by positivity, two_pow_padicValInt_dvd _⟩
  · rw [← two_pow_card_Ids] at hm
    have hfl := CellFloor.theorem_B_floor (hI_Ids ds) (ℓ := 2 ^ ds.length - 1)
      (by have := Nat.two_pow_pos ds.length; omega) (α := (α : ℤ)) (by exact_mod_cast hα) 0 0 hm
    have hcl : CellFloor.cellClock (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) 0 0 =
        xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α := by
      funext p; simp [CellFloor.cellClock]
    have hco : ∀ a b, CellFloor.cellCost (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) 0 0 a b =
        Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α a b := by
      intro a b; simp [CellFloor.cellCost]
    rw [hcl] at hfl
    simp only [hco] at hfl
    unfold SmithBounds.tailSum at hfl
    have h : ((∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
        AntitonicFit.ifit (2 ^ #(Ids ds)) (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j : ℤ) :
          ℝ) ≤ ((∑ a ∈ Rows, Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α a (β a) :
            ℤ) : ℝ) := by
      push_cast; exact hfl
    have h' := (Int.cast_le (R := ℝ)).1 h
    rw [two_pow_card_Ids] at h'
    exact h'

/-! ### The ceiling for `i = 0` -/

lemma r_K_sub_one (k : ℕ) : Houses.r k (2 ^ k - 1) = 0 := by
  have := Nat.two_pow_pos k
  simp [Houses.r, Nat.div_eq_of_lt (show 2 ^ k - 1 < 2 ^ k by omega), Rulers.v2]

lemma r_K_sub_one_add (k : ℕ) : Houses.r k (2 ^ k - 1 + 2 ^ k) = 1 := by
  have := Nat.two_pow_pos k
  rw [Houses.r, Nat.add_div_right _ this, Nat.div_eq_of_lt (show 2 ^ k - 1 < 2 ^ k by omega)]
  simp [Rulers.v2]

lemma oE_pos_of_ne_empty {b : Finset ℕ} (hb : b ≠ ∅) : 0 < Rulers.oE b :=
  sum_pos (fun _ _ => by positivity) (nonempty_iff_ne_empty.2 hb)

lemma JH_sharp (k : ℕ) (b : Finset ℕ) :
    (Houses.JH k (2 ^ k - 1) b : ℤ) = if b = ∅ then 0 else 1 := by
  have := Nat.two_pow_pos k
  unfold Houses.JH
  by_cases hb : b = ∅
  · subst hb; simp [Rulers.oE_empty]
  · have := oE_pos_of_ne_empty hb
    rw [if_pos (by omega), if_neg hb]; rfl

/-- With `μ = K − 1`: `ĉ_{K−1}(a, b) = ĉ_{H^♯}(a, b) + [b ≠ ∅]` (Lemma 7.5,
`Houses.lemma_A'_cost`; proof of (Z2) of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma cHat_sharp (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) {a b : Finset ℕ}
    (ha : a ⊆ I) (hb : b ⊆ I) :
    GoldenMatching.cHat k I α (2 ^ k - 1) a b =
      Houses.cHatH I k (2 ^ k - 1) α a b + if b = ∅ then 0 else 1 := by
  have := Nat.two_pow_pos k
  rw [Houses.lemma_A'_cost hI α _ ha hb, Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ k by omega),
    r_K_sub_one, r_K_sub_one_add]
  simp only [JH_sharp, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, sub_zero]

/-- With `μ = K − 1`: `x_{K−1}(D) = x_{H^♯}(D) + [I ∖ D ≠ ∅]` (Lemma 7.5,
`Houses.lemma_A'_clock`; proof of (Z2) of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma xVal_sharp (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) {D : Finset ℕ}
    (hD : D ⊆ I) :
    GoldenMatching.xVal k I α (2 ^ k - 1) D =
      Houses.xH I k (2 ^ k - 1) α D + if I \ D = ∅ then 0 else 1 := by
  have := Nat.two_pow_pos k
  rw [GoldenMatching.xVal, Houses.lemma_A'_clock hI α _ hD,
    Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ k by omega), r_K_sub_one, r_K_sub_one_add]
  simp only [JH_sharp, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, sub_zero, Houses.xH]

lemma dancer_eq_empty_iff {I : Finset ℕ} {p : ℕ} (hp : p < 2 ^ #I) : dancer I p = ∅ ↔ p = 0 := by
  constructor
  · intro h
    by_contra h0
    have := oE_dancer_pos (Nat.pos_of_ne_zero h0) hp
    rw [h, Rulers.oE_empty] at this
    exact lt_irrefl _ this
  · rintro rfl; exact dancer_zero I

lemma sum_ne_last {N r : ℕ} (hr : r ≤ N) (hN : 1 ≤ N) :
    ∑ j ∈ Ico (N - r) N, (if j = N - 1 then (0 : ℤ) else 1) = ((r - 1 : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_Ico_succ_top (by omega), if_pos (by omega), add_zero,
      sum_congr rfl fun j hj => if_neg (by simp only [mem_Ico] at hj; omega)]
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    congr 1; omega

lemma prod_scale (r : ℕ) : ∏ j : Fin r, (if (j : ℕ) = 0 then (1 : ℤ) else 2) = 2 ^ (r - 1) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [Fin.prod_univ_succ]
    simp

lemma padicValInt_two_pow (n : ℕ) : padicValInt 2 ((2 : ℤ) ^ n) = n := by
  have : ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) := by push_cast; rfl
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- The ceiling for `i = 0` (Theorem O as in `GoldenMatching.corollary_D`, here applied with
`μ = K − 1` to the matrix `Mo` with its columns `D ≠ ∅` multiplied by `2` and its row `∅` replaced;
proof of (Z2) of `C15_smith_form_of_the_dance_matrix.md`): for `I ≠ ∅` and `r ≤ N − 1`, the minor of
`Mo` with the rows `[N − r, N)` and the columns `[0, r)` is non-zero of 2-valuation
`r α K + Σ_{j ∈ [N − 1 − r, N − 1)} x^♯ j`. -/
lemma Z_ceil (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α)
    {r : ℕ} (hr : r ≤ 2 ^ Dance.mCount ds - 1) :
    Divisors.minor (Mo ds α 0) r (lastSet _ r) (firstSet _ r) ≠ 0 ∧
      (padicValInt 2 (Divisors.minor (Mo ds α 0) r (lastSet _ r) (firstSet _ r)) : ℤ) =
        r * ((α : ℤ) * 2 ^ ds.length) +
          ∑ j ∈ Ico (2 ^ Dance.mCount ds - 1 - r) (2 ^ Dance.mCount ds - 1),
            CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α j := by
  set N := 2 ^ Dance.mCount ds with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNI : 2 ^ #(Ids ds) = N := two_pow_card_Ids ds
  set Mo' : ℕ → ℕ → ℤ := fun p q => if h : p < N ∧ q < N then Mo ds α 0 ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
  have hMo' : ∀ p q : Fin N, Mo' p q = Mo ds α 0 p q := fun p q => by simp [Mo', p.2, q.2]
  set M' : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    if a = ∅ then (if b = ∅ then (2 : ℤ) ^ (α * 2 ^ ds.length) else 0)
    else Mo' (GoldenMatching.rank (Ids ds) a) (GoldenMatching.rank (Ids ds) b) *
      (if b = ∅ then 1 else 2)
  have hrk : ∀ {a}, a ⊆ Ids ds → GoldenMatching.rank (Ids ds) a < N := fun ha => by
    rw [← hNI]; exact GoldenMatching.rank_lt ha
  have hM' : ∀ {a b} (ha : a ⊆ Ids ds) (hb : b ⊆ Ids ds), a ≠ ∅ →
      M' a b = Mo ds α 0 ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ * (if b = ∅ then 1 else 2) := fun ha hb ha0 => by
    simp only [M', if_neg ha0]
    rw [hMo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩]
  have hpow : ∀ n : ℕ, ¬ (2 : ℤ) ^ (n + 1) ∣ 2 ^ n := fun n h => by
    have h1 := Int.le_of_dvd (by positivity) h
    have h2 : (2 : ℤ) ^ n < 2 ^ (n + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨n, hn, h1, h2⟩ := golden_ceiling ds.length (hI_Ids ds) (α : ℤ) (2 ^ ds.length - 1)
    ((α : ℤ) * 2 ^ ds.length) M'
    (fun a b ha hb hab => by
      by_cases ha0 : a = ∅
      · have hb0 : b ≠ ∅ := by rintro rfl; exact hab (empty_subset _)
        simp [M', ha0, hb0]
      · have hab' : ¬ dancer (Ids ds) (GoldenMatching.rank (Ids ds) b) ⊆
            dancer (Ids ds) (GoldenMatching.rank (Ids ds) a) := by
          rw [dancer_rank ha, dancer_rank hb]; exact hab
        rw [hM' ha hb ha0, Mo_off ds α 0 hα ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ hab', zero_mul])
    (fun a b hba ha => by
      have hb := hba.trans ha
      rw [cHat_sharp _ (hI_Ids ds) _ ha hb]
      by_cases ha0 : a = ∅
      · subst ha0
        obtain rfl := subset_empty.1 hba
        refine ⟨α * 2 ^ ds.length, by simp [Houses.cHatH, Rulers.gamma], ?_, ?_⟩
        · simp [M']
        · simp only [M', if_pos rfl]; exact hpow _
      · have hp : GoldenMatching.rank (Ids ds) a ≠ 0 := by
          intro h0; apply ha0; rw [← dancer_rank ha, h0, dancer_zero]
        obtain ⟨h0, hv⟩ := Z_val ds hk α hα ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ hp
          (by simp only; rw [dancer_rank ha, dancer_rank hb]; exact hba)
        simp only [Potential.cHat, dancer_rank ha, dancer_rank hb] at hv
        rw [hM' ha hb ha0]
        by_cases hb0 : b = ∅
        · refine ⟨padicValInt 2 (Mo ds α 0 ⟨_, hrk ha⟩ ⟨_, hrk hb⟩), by rw [hv, if_pos hb0]; ring,
            ?_, ?_⟩
          · rw [if_pos hb0, mul_one]; exact two_pow_padicValInt_dvd _
          · rw [if_pos hb0, mul_one]; exact not_two_pow_succ_dvd h0
        · refine ⟨padicValInt 2 (Mo ds α 0 ⟨_, hrk ha⟩ ⟨_, hrk hb⟩) + 1,
            by rw [if_neg hb0]; push_cast; rw [hv]; ring, ?_, ?_⟩
          · rw [if_neg hb0, pow_succ]; exact mul_dvd_mul_right (two_pow_padicValInt_dvd _) _
          · rw [if_neg hb0, pow_succ]
            intro hd
            exact not_two_pow_succ_dvd h0 ((mul_dvd_mul_iff_right two_ne_zero).1 hd))
    (r := r) (by rw [hNI]; omega)
  rw [hNI] at hn h1 h2
  have hmat : (Matrix.of fun i' j : Fin r => M' (dancer (Ids ds) (N - r + i')) (dancer (Ids ds) j)) =
      (Matrix.of fun i' j : Fin r => Mo ds α 0 ⟨N - r + i', by omega⟩ ⟨j, by omega⟩) *
        diagonal (fun j : Fin r => if (j : ℕ) = 0 then (1 : ℤ) else 2) := by
    ext i' j
    have hi' := i'.2
    have hj' := j.2
    have hp : N - r + i' < 2 ^ #(Ids ds) := by rw [hNI]; omega
    have hq : (j : ℕ) < 2 ^ #(Ids ds) := by rw [hNI]; omega
    rw [mul_diagonal, Matrix.of_apply, Matrix.of_apply,
      hM' (lemma_0a _ _) (lemma_0a _ _) (by rw [Ne, dancer_eq_empty_iff hp]; omega)]
    simp only [lemma_0c_rank hp, lemma_0c_rank hq, dancer_eq_empty_iff hq]
  rw [hmat, det_mul, det_diagonal, prod_scale] at h1 h2
  obtain ⟨hX0, hXv⟩ := padicValInt_eq_of_exact h1 h2
  have hX : (Matrix.of fun i' j : Fin r => Mo ds α 0 ⟨N - r + i', by omega⟩ ⟨j, by omega⟩).det ≠ 0 :=
    left_ne_zero_of_mul hX0
  rw [padicValInt.mul hX (pow_ne_zero _ two_ne_zero), padicValInt_two_pow] at hXv
  rw [minor_last_first _ (by omega)]
  refine ⟨hX, ?_⟩
  -- the clocks
  have hsum : ∑ j ∈ Ico (N - r) N, GoldenMatching.xVal ds.length (Ids ds) (α : ℤ)
      (2 ^ ds.length - 1) (dancer (Ids ds) j) =
      ∑ j ∈ Ico (N - r) N, xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j + ((r - 1 : ℕ) : ℤ) := by
    rw [← sum_ne_last (by omega) hN1, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_Ico] at hj
    have hj' : j < 2 ^ #(Ids ds) := by rw [hNI]; omega
    rw [xVal_sharp _ (hI_Ids ds) _ (lemma_0a _ _), ← lemma_0d hj']
    have hiff : dancer (Ids ds) (2 ^ #(Ids ds) - 1 - j) = ∅ ↔ j = N - 1 := by
      rw [dancer_eq_empty_iff (by omega), hNI]; omega
    simp only [xHseq, hiff]
  have hsh : ∑ j ∈ Ico (N - 1 - r) (N - 1), CellFloor.xSharp (Ids ds) ds.length
      (2 ^ ds.length - 1) α j = ∑ j ∈ Ico (N - r) N, xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j := by
    simp only [CellFloor.xSharp]
    rw [sum_Ico_add' (fun j => xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j),
      show N - 1 - r + 1 = N - r by omega, show N - 1 + 1 = N by omega]
  rw [hsh]
  have : ((padicValInt 2 (Matrix.of fun i' j : Fin r =>
      Mo ds α 0 ⟨N - r + i', by omega⟩ ⟨j, by omega⟩).det : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) = n := by
    exact_mod_cast hXv
  rw [hn, hsum] at this
  linarith

/-! ### Conclusion for `i = 0` -/

lemma yHatS_eq (ds : List Bool) (α : ℕ) :
    yHatS ds α = AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
      (CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α) := by
  unfold yHatS CellFloor.yhatSharp; rw [two_pow_card_Ids]

/-- `ŷ^♯(j) = ŷ_{H^♯}(j + 1)` for `j < N − 1` (`CellFloor.lemma_7_9_I3`; proof of (Z2) of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma yHatS_succ (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) {j : ℕ}
    (hj : j < 2 ^ Dance.mCount ds - 1) :
    yHatS ds α j = AntitonicFit.ifit (2 ^ Dance.mCount ds)
      (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) (j + 1) := by
  have h := (CellFloor.lemma_7_9_I3 (hI_Ids ds) (ℓ := 2 ^ ds.length - 1) rfl
    (α := (α : ℤ)) (by exact_mod_cast hα) (nonempty_iff_ne_empty.2 hne)).2.2.2.1 j
    (by rw [two_pow_card_Ids]; exact hj)
  unfold yHatS CellFloor.yhatSharp
  rw [h, Potential.yhat, two_pow_card_Ids]

/-- The conclusion for `i = 0` (Theorem 6.5 on `N − 1` positions with (Q1), (Q2) and
`Divisors.theorem_B_without_M`), for the matrix in o-order (proof of (Z2) and (Z3) of
`C15_smith_form_of_the_dance_matrix.md`). -/
theorem Z_main (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    (∀ r ≤ 2 ^ Dance.mCount ds - 1, (Divisors.dd (Mo ds α 0) r : ℤ) =
      r * ((α : ℤ) * 2 ^ ds.length) +
        ∑ j ∈ Ico (2 ^ Dance.mCount ds - 1 - r) (2 ^ Dance.mCount ds - 1), yHatS ds α j) ∧
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 1 - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧ P * Mo ds α 0 * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) := by
  set N := 2 ^ Dance.mCount ds with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  rw [yHatS_eq]
  refine smith_of_bounds (Mo ds α 0) (N' := N - 1) (by omega)
    (CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α) ((α : ℤ) * 2 ^ ds.length)
    (fun r hr B D hB hD => ?_)
    (fun r hr => ⟨lastSet _ r, firstSet _ r, card_lastSet (by omega), card_firstSet (by omega),
      (Z_ceil ds hk α hα hr).1, (Z_ceil ds hk α hα hr).2.le⟩)
    (fun _ B D hB hD => ?_)
  · have hsum : ∑ j ∈ Ico (N - 1 - r) (N - 1), AntitonicFit.ifit (N - 1)
        (CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α) j =
        ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N
          (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j := by
      rw [← yHatS_eq]
      rw [sum_congr rfl fun j hj => yHatS_succ ds α hα hne (by simp only [mem_Ico] at hj; omega)]
      rw [sum_Ico_add' (fun j => AntitonicFit.ifit N
          (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j),
        show N - 1 - r + 1 = N - r by omega, show N - 1 + 1 = N by omega]
    rw [hsum]
    exact Z_floor ds hk α hα B D hB hD
  · have e : N - 1 + 1 = N := by omega
    rw [e] at hB hD ⊢
    rw [eq_univ_of_card B (by simpa using hB), eq_univ_of_card D (by simpa using hD),
      Divisors.minor_univ]
    exact det_eq_zero_of_row_eq_zero (zeroPos ds) (Mo_row_zero ds α hα)

/-- **(Z2)** (Theorem 7.10, `i = 0`) of `C15_smith_form_of_the_dance_matrix.md`: for `i = 0`,
`I ≠ ∅` and every `r ≤ N − 1`, `Divisors.dd M r = r · α K + Σ_{j ∈ [N − 1 − r, N − 1)} ŷ^♯ j`
(in `ℤ`), and `ŷ^♯` is non-increasing on `[0, N − 1)`. -/
theorem Z2 (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    (∀ r ≤ 2 ^ Dance.mCount ds - 1, (Divisors.dd (finalMatrix ℤ ds α 0) r : ℤ) =
      r * ((α : ℤ) * 2 ^ ds.length) +
        ∑ j ∈ Ico (2 ^ Dance.mCount ds - 1 - r) (2 ^ Dance.mCount ds - 1), yHatS ds α j) ∧
    (∀ j, j + 1 < 2 ^ Dance.mCount ds - 1 → yHatS ds α (j + 1) ≤ yHatS ds α j) := by
  obtain ⟨h1, -⟩ := Z_main ds hk α hα hne
  refine ⟨fun r hr => ?_, fun j hj => ?_⟩
  · rw [← P2]; exact h1 r hr
  · rw [yHatS_succ ds α hα hne hj, yHatS_succ ds α hα hne (by omega)]
    have h := (CellFloor.lemma_7_9_I1 (hI_Ids ds) (ℓ := 2 ^ ds.length - 1)
      (by have := Nat.two_pow_pos ds.length; omega) (α := (α : ℤ)) (by exact_mod_cast hα)).2
      (j + 1) (by rw [two_pow_card_Ids]; omega)
    rw [Potential.yhat, two_pow_card_Ids] at h
    exact h

/-- **(Z3)** (Theorem 7.10, `i = 0`) of `C15_smith_form_of_the_dance_matrix.md`: for `i = 0` and
`I ≠ ∅` there are `P, Q` over `ℤ` with `det P`, `det Q` odd and odd integers `u j` such that `P M Q`
is diagonal with entries `u j · 2^{α K + ŷ^♯(N − 2 − j)}` for `j < N − 1` and `0` for `j = N − 1`
(the exponent is a natural number `E j` with `(E j : ℤ) = α K + ŷ^♯(N − 2 − j)`). -/
theorem Z3 (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
            (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)) ∧
          P * finalMatrix ℤ ds α 0 * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) := by
  obtain ⟨-, P, Q, hP, hQ, E, hE, u, hu, hD⟩ := Z_main ds hk α hα hne
  refine ⟨P * (slPerm ds).permMatrix ℤ, Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q, ?_, ?_, u, hu,
    E, fun j hj => ?_, smith_transfer ds α 0 hD⟩
  · rw [det_mul]; exact hP.mul (odd_det_permMatrix _)
  · rw [det_mul]; exact (odd_det_permMatrix _).mul hQ
  · rw [hE j hj, show 2 ^ Dance.mCount ds - 1 - 1 - j = 2 ^ Dance.mCount ds - 2 - j by omega]

end DanceSmith
