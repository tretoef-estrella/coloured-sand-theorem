module

public import RequestProject.DanceSmith.Golden

/-!
# Part S of `C15_smith_form_of_the_dance_matrix.md`: the case `i ≥ 1` (Theorem 7.10)

## Encoding

* `xClk ds α i j = GoldenMatching.xVal k I α (i − 1) (TheoremF.dancer I j)` are the clocks `x j`
  (`α` cast to `ℤ`), `yHat ds α i = AntitonicFit.ifit N (xClk ds α i)` is `ŷ`, and
  `Cst ds α i = α · 2^k + Rulers.kappa (i − 1) (2^k)` is `C` (with `μ = i − 1`).
* The exponents of (S1) and (S3), natural numbers equal to integers, are existentially quantified
  natural numbers together with the equation in `ℤ`.
* "`ŷ` is non-increasing on `[0, N)`" is `∀ j, j + 1 < N → ŷ (j + 1) ≤ ŷ j`.
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix TheoremF Windows

/-- *Setting* ("Clocks") of `C15_smith_form_of_the_dance_matrix.md`: the clocks
`x j := GoldenMatching.xVal k I α (i − 1) (TheoremF.dancer I j)`. -/
def xClk (ds : List Bool) (α i : ℕ) : ℕ → ℤ := fun j =>
  GoldenMatching.xVal ds.length (Ids ds) (α : ℤ) (i - 1) (dancer (Ids ds) j)

/-- *Setting* ("Clocks") of `C15_smith_form_of_the_dance_matrix.md`: `ŷ := AntitonicFit.ifit N x`. -/
noncomputable def yHat (ds : List Bool) (α i : ℕ) : ℕ → ℤ :=
  AntitonicFit.ifit (2 ^ Dance.mCount ds) (xClk ds α i)

/-- *Setting* ("Clocks") of `C15_smith_form_of_the_dance_matrix.md`:
`C := α K + κ(i − 1, K)`, `K = 2^k`. -/
def Cst (ds : List Bool) (α i : ℕ) : ℤ :=
  (α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length)

lemma hI_Ids (ds : List Bool) : ∀ t ∈ Ids ds, t < ds.length := fun _ ht => lt_of_mem_Ids ht

lemma two_pow_card_Ids (ds : List Bool) : 2 ^ #(Ids ds) = 2 ^ Dance.mCount ds := by
  rw [card_Ids]

/-- Entries of `Mo` off the nested pairs vanish (`Windows.theorem_D_ii` and (P1); Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma Mo_off (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (p q : Fin (2 ^ Dance.mCount ds))
    (h : ¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p) : Mo ds α i p q = 0 := by
  have hP := (P1 ds).2.2
  exact (theorem_D_ii ds α i hα (sl ds p) (sl ds q)).2 (by rw [hP p, hP q]; exact h)

/-- Entries of `Mo` on the nested pairs (`Windows.theorem_D_iii` and (P1); Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma Mo_val (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α)
    (p q : Fin (2 ^ Dance.mCount ds)) (h : dancer (Ids ds) q ⊆ dancer (Ids ds) p)
    (hi : 0 < i + Rulers.oE (dancer (Ids ds) p)) :
    Mo ds α i p q ≠ 0 ∧ (padicValInt 2 (Mo ds α i p q) : ℤ) =
      1 - (2 : ℤ) ^ ds.length + Rulers.oE (dancer (Ids ds) p \ dancer (Ids ds) q) +
        Rulers.delta ds.length (dancer (Ids ds) p \ dancer (Ids ds) q) +
        ∑ d ∈ Ico (Rulers.oE (dancer (Ids ds) p)) (Rulers.oE (dancer (Ids ds) q) + 2 ^ ds.length),
          ((α : ℤ) + (Rulers.v2 (i + d) : ℤ)) := by
  have hP := (P1 ds).2.2
  have := theorem_D_iii ds hk α i hα (sl ds p) (sl ds q) (by rw [hP p, hP q]; exact h)
    (by rw [hP p]; exact hi)
  rw [hP p, hP q] at this
  exact this

/-- **(S1)** of `C15_smith_form_of_the_dance_matrix.md`: for `i ≥ 1` and `p, q < N`, if
`dancer I q ⊄ dancer I p` then `Mo p q = 0`; if `dancer I q ⊆ dancer I p` then `Mo p q ≠ 0` and
`2^n ∣ Mo p q`, `2^{n+1} ∤ Mo p q` for a natural number `n` with
`(n : ℤ) = C + GoldenMatching.cHat k I α (i − 1) (dancer I p) (dancer I q)`. -/
theorem S1 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    (p q : Fin (2 ^ Dance.mCount ds)) :
    (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo ds α i p q = 0) ∧
    (dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo ds α i p q ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = Cst ds α i +
          GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ Mo ds α i p q ∧ ¬ 2 ^ (n + 1) ∣ Mo ds α i p q) := by
  refine ⟨Mo_off ds α i hα p q, fun h => ?_⟩
  obtain ⟨h0, hv⟩ := Mo_val ds hk α i hα p q h (by omega)
  rw [Rulers.proposition_5_2 (hI_Ids ds) h (lemma_0a _ _) (α : ℤ) (by exact_mod_cast hα) i hi] at hv
  refine ⟨h0, padicValInt 2 (Mo ds α i p q), ?_, two_pow_padicValInt_dvd _,
    not_two_pow_succ_dvd h0⟩
  rw [hv, Cst, GoldenMatching.cHat]
  ring

section Clocks

variable (ds : List Bool) (α i : ℕ)

/-- The cell clocks of the penalty cell are the clocks `x` (Lemma 7.5, `Houses.lemma_A'_clock`;
proof of (S2) of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma cellClock_eq_xClk {j : ℕ} (hj : j < 2 ^ Dance.mCount ds) :
    CellFloor.cellClock (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
      (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) j =
      xClk ds α i j := by
  rw [← two_pow_card_Ids] at hj
  unfold CellFloor.cellClock xClk xHseq JHseq
  rw [lemma_0d hj, GoldenMatching.xVal,
    Houses.lemma_A'_clock (hI_Ids ds) (α : ℤ) (i - 1) (lemma_0a _ _)]

/-- The cell costs of the penalty cell are the normalized costs `ĉ` (Lemma 7.5,
`Houses.lemma_A'_cost`; proof of (S2) of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma cellCost_eq_cHat (p q : ℕ) :
    CellFloor.cellCost (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
      (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) p q =
      GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (dancer (Ids ds) p) (dancer (Ids ds) q) := by
  unfold CellFloor.cellCost Potential.cHat JHseq
  rw [Houses.lemma_A'_cost (hI_Ids ds) (α : ℤ) (i - 1) (lemma_0a _ _) (lemma_0a _ _)]

lemma ifit_cellClock :
    AntitonicFit.ifit (2 ^ Dance.mCount ds)
      (CellFloor.cellClock (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
        (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length))) =
      yHat ds α i :=
  ifit_congr fun _ hj => cellClock_eq_xClk ds α i hj

end Clocks

/-- The floor for `i ≥ 1` (Lemma 6.1, Theorem 7.4, `Houses.lemma_A'_cost`,
`Houses.lemma_A'_clock`, `CellFloor.theorem_B_floor`; proof of (S2) of
`C15_smith_form_of_the_dance_matrix.md`): every `r × r` minor of `Mo` is divisible by
`2^{r C + Σ_{[N − r, N)} ŷ}`. -/
lemma S_floor (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    {r : ℕ} (B D : Finset (Fin (2 ^ Dance.mCount ds))) (hB : B.card = r) (hD : D.card = r) :
    (2 : ℤ) ^ ((r : ℤ) * Cst ds α i + ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds),
      AntitonicFit.ifit (2 ^ Dance.mCount ds) (xClk ds α i) j).toNat ∣
      Divisors.minor (Mo ds α i) r B D := by
  refine floor_minor (Mo ds α i) (CellFloor.IsCellArrow (Ids ds))
    (fun p q => GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (dancer (Ids ds) p)
      (dancer (Ids ds) q)) (Cst ds α i) _ (fun p q h => ?_) (fun p q h => ?_)
    (fun Rows β hm => ?_) B D hB hD
  · apply Mo_off ds α i hα
    intro hsub
    exact h ⟨by rw [two_pow_card_Ids]; exact p.2, by rw [two_pow_card_Ids]; exact q.2, hsub⟩
  · obtain ⟨-, n, hn, h1, -⟩ := (S1 ds hk α i hα hi p q).2 h.2.2
    simp only
    rw [← hn, Int.toNat_natCast]
    exact ⟨by positivity, h1⟩
  · rw [← two_pow_card_Ids] at hm
    have hfl := CellFloor.theorem_B_floor (hI_Ids ds) (Nat.mod_lt (i - 1) (by positivity))
      (α := (α : ℤ)) (by exact_mod_cast hα) (Houses.r ds.length (i - 1))
      (Houses.r ds.length (i - 1 + 2 ^ ds.length)) hm
    unfold SmithBounds.tailSum at hfl
    have hfl' : ∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
        AntitonicFit.ifit (2 ^ #(Ids ds)) (CellFloor.cellClock (Ids ds) ds.length
          ((i - 1) % 2 ^ ds.length) (α : ℤ) (Houses.r ds.length (i - 1))
          (Houses.r ds.length (i - 1 + 2 ^ ds.length))) j ≤
        ∑ a ∈ Rows, CellFloor.cellCost (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
          (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) a (β a) := by
      have h : ((∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
          AntitonicFit.ifit (2 ^ #(Ids ds)) (CellFloor.cellClock (Ids ds) ds.length
            ((i - 1) % 2 ^ ds.length) (α : ℤ) (Houses.r ds.length (i - 1))
            (Houses.r ds.length (i - 1 + 2 ^ ds.length))) j : ℤ) : ℝ) ≤
          ((∑ a ∈ Rows, CellFloor.cellCost (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
            (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) a (β a) : ℤ) :
              ℝ) := by
        push_cast; exact hfl
      exact_mod_cast h
    rw [two_pow_card_Ids, ifit_cellClock] at hfl'
    simp only [cellCost_eq_cHat] at hfl'
    exact hfl'

/-- The ceiling for `i ≥ 1` (Corollary 6.3, `GoldenMatching.corollary_D`; proof of (S2) of
`C15_smith_form_of_the_dance_matrix.md`): the minor of `Mo` with the rows `[N − r, N)` and the
columns `[0, r)` is non-zero of 2-valuation `r C + U(r)`, `U(r) = Σ_{[N − r, N)} x`. -/
lemma S_ceil (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    {r : ℕ} (hr : r ≤ 2 ^ Dance.mCount ds) :
    Divisors.minor (Mo ds α i) r (lastSet _ r) (firstSet _ r) ≠ 0 ∧
      (padicValInt 2 (Divisors.minor (Mo ds α i) r (lastSet _ r) (firstSet _ r)) : ℤ) =
        r * Cst ds α i + ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds), xClk ds α i j := by
  set N := 2 ^ Dance.mCount ds with hN
  set Mo' : ℕ → ℕ → ℤ := fun p q => if h : p < N ∧ q < N then Mo ds α i ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
  have hMo' : ∀ p q : Fin N, Mo' p q = Mo ds α i p q := fun p q => by simp [Mo', p.2, q.2]
  set M' : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    Mo' (GoldenMatching.rank (Ids ds) a) (GoldenMatching.rank (Ids ds) b)
  have hrk : ∀ {a}, a ⊆ Ids ds → GoldenMatching.rank (Ids ds) a < N := fun ha => by
    rw [hN, ← two_pow_card_Ids]; exact GoldenMatching.rank_lt ha
  have hM' : ∀ {a b} (ha : a ⊆ Ids ds) (hb : b ⊆ Ids ds),
      M' a b = Mo ds α i ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ := fun ha hb =>
    hMo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩
  obtain ⟨n, hn, h1, h2⟩ := golden_ceiling ds.length (hI_Ids ds) (α : ℤ) (i - 1) (Cst ds α i) M'
    (fun a b ha hb hab => by
      rw [hM' ha hb]
      exact Mo_off ds α i hα _ _ (by simp only; rw [dancer_rank ha, dancer_rank hb]; exact hab))
    (fun a b hba ha => by
      have hb := hba.trans ha
      rw [hM' ha hb]
      obtain ⟨-, n, hn, h⟩ := (S1 ds hk α i hα hi ⟨_, hrk ha⟩ ⟨_, hrk hb⟩).2
        (by simp only; rw [dancer_rank ha, dancer_rank hb]; exact hba)
      simp only [dancer_rank ha, dancer_rank hb] at hn
      exact ⟨n, hn, h⟩)
    (r := r) (by rw [two_pow_card_Ids]; exact hr)
  rw [two_pow_card_Ids] at hn h1 h2
  have hmat : (Matrix.of fun i' j : Fin r => M' (dancer (Ids ds) (N - r + i')) (dancer (Ids ds) j)) =
      Matrix.of fun i' j : Fin r => Mo ds α i ⟨N - r + i', by omega⟩ ⟨j, by omega⟩ := by
    ext i' j
    simp only [Matrix.of_apply, M']
    have hi' := i'.2
    have hj' := j.2
    have hp : N - r + i' < 2 ^ #(Ids ds) := by rw [two_pow_card_Ids, ← hN]; omega
    have hq : (j : ℕ) < 2 ^ #(Ids ds) := by rw [two_pow_card_Ids, ← hN]; omega
    rw [lemma_0c_rank hp, lemma_0c_rank hq]
    exact hMo' ⟨N - r + i', by omega⟩ ⟨j, by omega⟩
  rw [hmat] at h1 h2
  rw [minor_last_first _ hr]
  obtain ⟨h0, hv⟩ := padicValInt_eq_of_exact h1 h2
  refine ⟨h0, ?_⟩
  rw [hv, hn]
  rfl

/-- A Smith form of `Mo` is a Smith form of `M` (`Mo = P M Pᵀ` by (P2); Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma smith_transfer (ds : List Bool) (α i : ℕ) {P Q D : Matrix (Fin (2 ^ Dance.mCount ds))
    (Fin (2 ^ Dance.mCount ds)) ℤ} (h : P * Mo ds α i * Q = D) :
    (P * (slPerm ds).permMatrix ℤ) * finalMatrix ℤ ds α i *
      (Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q) = D := by
  rw [Mo_eq_mul] at h
  rw [← h]
  simp only [Matrix.mul_assoc]

lemma det_Mo (ds : List Bool) (α i : ℕ) :
    (Mo ds α i).det = ((slPerm ds).permMatrix ℤ).det * (finalMatrix ℤ ds α i).det *
      (Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹).det := by
  rw [Mo_eq_mul, det_mul, det_mul]

lemma lastSet_self (N : ℕ) : lastSet N N = univ := by ext; simp [lastSet]
lemma firstSet_self (N : ℕ) : firstSet N N = univ := by ext p; simp [firstSet]

/-- The conclusion for `i ≥ 1` (Theorem 6.5 with (Q1), (Q2) and `Divisors.theorem_B_without_M`),
for the matrix in o-order (proof of (S2) and (S3) of `C15_smith_form_of_the_dance_matrix.md`). -/
theorem S_main (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ Dance.mCount ds, (Divisors.dd (Mo ds α i) r : ℤ) =
      r * Cst ds α i + ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds), yHat ds α i j) ∧
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
          (E j : ℤ) = Cst ds α i + yHat ds α i (2 ^ Dance.mCount ds - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧ P * Mo ds α i * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds then u j * 2 ^ E j else 0) :=
  smith_of_bounds (Mo ds α i) le_rfl (xClk ds α i) (Cst ds α i)
    (fun _ _ B D hB hD => S_floor ds hk α i hα hi B D hB hD)
    (fun r hr => ⟨lastSet _ r, firstSet _ r, card_lastSet hr, card_firstSet hr,
      (S_ceil ds hk α i hα hi hr).1, (S_ceil ds hk α i hα hi hr).2.le⟩)
    (fun h => absurd h (lt_irrefl _))

/-- **(S2)** (Theorem 7.10, `i ≥ 1`) of `C15_smith_form_of_the_dance_matrix.md`: for `i ≥ 1` and every
`r ≤ N`, `Divisors.dd M r = r · C + Σ_{j ∈ [N − r, N)} ŷ j` (in `ℤ`); `det M ≠ 0`; and `ŷ` is
non-increasing on `[0, N)`. -/
theorem S2 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ Dance.mCount ds, (Divisors.dd (finalMatrix ℤ ds α i) r : ℤ) =
      r * Cst ds α i + ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds), yHat ds α i j) ∧
    (finalMatrix ℤ ds α i).det ≠ 0 ∧
    (∀ j, j + 1 < 2 ^ Dance.mCount ds → yHat ds α i (j + 1) ≤ yHat ds α i j) := by
  obtain ⟨h1, -⟩ := S_main ds hk α i hα hi
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rw [← P2]; exact h1 r hr
  · have h0 := (S_ceil ds hk α i hα hi (r := 2 ^ Dance.mCount ds) le_rfl).1
    rw [lastSet_self, firstSet_self, Divisors.minor_univ, det_Mo] at h0
    intro h; apply h0; rw [h, mul_zero, zero_mul]
  · have h := (CellFloor.lemma_7_9_I2 (hI_Ids ds) (Nat.mod_lt (i - 1) (by positivity))
      (α := (α : ℤ)) (by exact_mod_cast hα) (Houses.r ds.length (i - 1))
      (Houses.r ds.length (i - 1 + 2 ^ ds.length))).2.2
    rw [two_pow_card_Ids, ifit_cellClock] at h
    exact h

/-- **(S3)** (Theorem 7.10, `i ≥ 1`) of `C15_smith_form_of_the_dance_matrix.md`: for `i ≥ 1` there are
`P, Q` over `ℤ` with `det P`, `det Q` odd and odd integers `u j` such that `P M Q` is diagonal with
entries `u j · 2^{C + ŷ(N − 1 − j)}`, `j < N` (the exponent is a natural number `E j` with
`(E j : ℤ) = C + ŷ(N − 1 − j)`). -/
theorem S3 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
            (E j : ℤ) = Cst ds α i + yHat ds α i (2 ^ Dance.mCount ds - 1 - j)) ∧
          P * finalMatrix ℤ ds α i * Q =
            diagonal (fun j : Fin (2 ^ Dance.mCount ds) => u j * 2 ^ E j) := by
  obtain ⟨-, P, Q, hP, hQ, E, hE, u, hu, hD⟩ := S_main ds hk α i hα hi
  refine ⟨P * (slPerm ds).permMatrix ℤ, Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q, ?_, ?_, u, hu,
    E, hE, ?_⟩
  · rw [det_mul]; exact hP.mul (odd_det_permMatrix _)
  · rw [det_mul]; exact (odd_det_permMatrix _).mul hQ
  · rw [smith_transfer ds α i hD]
    congr 1
    funext j
    exact if_pos j.2

end DanceSmith
