module

public import RequestProject.AntitonicFit.Basic

/-!
# Lemma 7.1 (characterization of the antitonic fit)

This file formalizes the notion of level set (from the *Setting* of `C1_antitonic_fits.md`)
and **Lemma 7.1**.  Along the way we prove an equivalent "global" form of the
characterization (`KKT`), expressed with the prefix sums `resid x z n = Σ_{j<n} (x_j − z_j)`,
which is the main technical tool of the later files.

## Encoding of level sets

* `levelSet N z j` is the finite set `{i < N : z_i = z_j}` (the level set of position `j`).
* `IsLevelInterval N z p q` says that `[p, q]` (with `p ≤ q < N`) is a level set of `z`,
  i.e. for every `i < N`, `z_i = z_p ↔ p ≤ i ≤ q`.  For non-increasing `z` every level set is
  such an interval (`exists_levelInterval`, `levelSet_eq_Icc`).
-/

@[expose] public section

namespace AntitonicFit

open Finset

/-- *Setting* of `C1_antitonic_fits.md`: the level set `{i : z_i = z_j}` of position `j`
(positions restricted to `0, …, N-1`). -/
noncomputable def levelSet (N : ℕ) (z : ℕ → ℝ) (j : ℕ) : Finset ℕ := (range N).filter (fun i => z i = z j)

/-- *Setting* of `C1_antitonic_fits.md`: `[p, q]` is a level set of `z` (of length `N`):
`p ≤ q < N` and, for all `i < N`, `z_i = z_p` iff `p ≤ i ≤ q`. -/
def IsLevelInterval (N : ℕ) (z : ℕ → ℝ) (p q : ℕ) : Prop :=
  p ≤ q ∧ q < N ∧ ∀ i, i < N → (z i = z p ↔ p ≤ i ∧ i ≤ q)

/-- The two conditions of **Lemma 7.1** of `C1_antitonic_fits.md`, required on every level set
`[p, q]` of `z`: `Σ_{j=p}^{q} (x_j − z_j) = 0` and `Σ_{j=p}^{s} (x_j − z_j) ≤ 0` for
`p ≤ s ≤ q`. -/
def LevelCond (N : ℕ) (x z : ℕ → ℝ) : Prop :=
  ∀ p q, IsLevelInterval N z p q →
    ∑ j ∈ Icc p q, (x j - z j) = 0 ∧ ∀ s, p ≤ s → s ≤ q → ∑ j ∈ Icc p s, (x j - z j) ≤ 0

/-- Prefix sums of residuals: `resid x z n = Σ_{j<n} (x_j − z_j)` (proof tool). (Auxiliary result for Lemma 7.1 (sufficiency, Abel summation) of `C1_antitonic_fits.md`.) -/
def resid (x z : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, (x j - z j)

/-- Global form of the characterization (proof tool, equivalent to **Lemma 7.1**):
`z` non-increasing, all prefix sums of `x − z` are `≤ 0`, the total is `0`, and the prefix sum
vanishes at every strict drop of `z`. (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
def KKT (N : ℕ) (x z : ℕ → ℝ) : Prop :=
  NonIncr N z ∧ (∀ n ≤ N, resid x z n ≤ 0) ∧ resid x z N = 0 ∧
    ∀ s, s + 1 < N → z (s + 1) < z s → resid x z (s + 1) = 0

variable {N : ℕ} {x x' z z' : ℕ → ℝ}

theorem resid_zero : resid x z 0 = 0 := by simp [resid]

theorem resid_congr {n : ℕ} (hx : ∀ j < n, x j = x' j) (hz : ∀ j < n, z j = z' j) :
    resid x z n = resid x' z' n := by
  unfold resid
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [hx j hj, hz j hj]

theorem resid_add (b m : ℕ) : resid x z (b + m) = resid x z b + resid (shift b x) (shift b z) m := by
  unfold resid shift
  rw [sum_range_add]

theorem IsLevelInterval.eq {p q i : ℕ} (h : IsLevelInterval N z p q) (hpi : p ≤ i) (hiq : i ≤ q) :
    z i = z p := (h.2.2 i (by have := h.2.1; omega)).2 ⟨hpi, hiq⟩

theorem IsLevelInterval.congr {p q : ℕ} (h : IsLevelInterval N z p q) (hz : ∀ j < N, z j = z' j) :
    IsLevelInterval N z' p q := by
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  rw [← hz i hi, ← hz p (by have := h.1; have := h.2.1; omega)]
  exact h.2.2 i hi

/-- *Setting* of `C1_antitonic_fits.md`: for a non-increasing `z`, the level set of every
position is an interval `[p, q]`. -/
theorem exists_levelInterval (hz : NonIncr N z) {j : ℕ} (hj : j < N) :
    ∃ p q, p ≤ j ∧ j ≤ q ∧ IsLevelInterval N z p q := by
  classical
  let p := Nat.find (⟨j, rfl⟩ : ∃ i, z i = z j)
  let q := Nat.findGreatest (fun i => z i = z j) (N - 1)
  have hp : z p = z j := Nat.find_spec (⟨j, rfl⟩ : ∃ i, z i = z j)
  have hpj : p ≤ j := Nat.find_min' _ rfl
  have hjq : j ≤ q := Nat.le_findGreatest (by omega) rfl
  have hq : z q = z j := Nat.findGreatest_spec (P := fun i => z i = z j) (m := j) (by omega) rfl
  have hqN : q < N := (Nat.findGreatest_le _).trans_lt (by omega)
  refine ⟨p, q, hpj, hjq, by omega, hqN, fun i hi => ?_⟩
  rw [hp]
  constructor
  · intro h
    exact ⟨Nat.find_min' _ h, Nat.le_findGreatest (by omega) h⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · calc z i ≤ z p := hz.anti h1 hi
        _ = z j := hp
    · calc z j = z q := hq.symm
        _ ≤ z i := hz.anti h2 hqN

/-- The level set of a position `j ∈ [p, q]` of a level interval `[p, q]` is `[p, q]`. (Auxiliary result for *Setting* (level sets) of `C1_antitonic_fits.md`.) -/
theorem levelSet_eq_Icc {p q j : ℕ} (h : IsLevelInterval N z p q) (hpj : p ≤ j) (hjq : j ≤ q) :
    levelSet N z j = Icc p q := by
  have hzj := h.eq hpj hjq
  obtain ⟨_, hqN, hiff⟩ := h
  ext i
  simp only [levelSet, mem_filter, mem_range, mem_Icc, hzj]
  constructor
  · rintro ⟨hi, he⟩; exact (hiff i hi).1 he
  · rintro ⟨h1, h2⟩; exact ⟨by omega, (hiff i (by omega)).2 ⟨h1, h2⟩⟩

/-- *Setting* of `C1_antitonic_fits.md`: for a non-increasing `z`, every level set
`{i : z_i = z_j}` is an interval `[p, q]` of consecutive positions containing `j`. -/
theorem levelSet_isInterval (hz : NonIncr N z) {j : ℕ} (hj : j < N) :
    ∃ p q, p ≤ j ∧ j ≤ q ∧ IsLevelInterval N z p q ∧ levelSet N z j = Icc p q := by
  obtain ⟨p, q, h1, h2, h⟩ := exists_levelInterval hz hj
  exact ⟨p, q, h1, h2, h, levelSet_eq_Icc h h1 h2⟩

theorem levelSet_congr {j : ℕ} (hz : ∀ i < N, z i = z' i) (hj : j < N) :
    levelSet N z j = levelSet N z' j := by
  ext i
  simp only [levelSet, mem_filter, mem_range]
  constructor
  · rintro ⟨hi, he⟩; exact ⟨hi, by rw [← hz i hi, ← hz j hj, he]⟩
  · rintro ⟨hi, he⟩; exact ⟨hi, by rw [hz i hi, hz j hj, he]⟩

lemma sum_bump (N p s : ℕ) (hs : s < N) (f g : ℕ → ℝ) (e : ℝ) :
    ∑ j ∈ range N, f j * ((if p ≤ j ∧ j ≤ s then g j + e else g j) - g j) =
      e * ∑ j ∈ Icc p s, f j := by
  have : ∀ j, f j * ((if p ≤ j ∧ j ≤ s then g j + e else g j) - g j) =
      if j ∈ Icc p s then e * f j else 0 := by
    intro j; simp only [mem_Icc]; split_ifs <;> ring
  simp_rw [this]
  rw [sum_ite_mem, mul_sum]
  congr 1
  ext j; simp only [mem_inter, mem_range, mem_Icc]; omega

/-- Necessity in **Lemma 7.1**: a fit satisfies the level-set conditions. (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
theorem IsFit.levelCond (hz : IsFit N x z) : LevelCond N x z := by
  intro p q hpq
  obtain ⟨hpq', hqN, hiff⟩ := hpq
  have hpre : ∀ s, p ≤ s → s ≤ q → ∑ j ∈ Icc p s, (x j - z j) ≤ 0 := by
    intro s hps hsq
    set e : ℝ := if p = 0 then 1 else z (p - 1) - z p with he
    have he0 : 0 < e := by
      by_cases h0 : p = 0
      · simp [he, h0]
      · simp only [he, h0, if_false, sub_pos]
        have h1 : z p ≤ z (p - 1) := hz.1.anti (by omega) (by omega)
        have h2 : z (p - 1) ≠ z p := fun h => by have := (hiff (p - 1) (by omega)).1 h; omega
        exact lt_of_le_of_ne h1 (Ne.symm h2)
    set y : ℕ → ℝ := fun j => if p ≤ j ∧ j ≤ s then z j + e else z j with hy_def
    have hy : NonIncr N y := by
      intro i hi
      have hzi := hz.1 i hi
      simp only [hy_def]
      split_ifs with h1 h2 h2
      · linarith
      · have hp : p = i + 1 := by omega
        have : e = z i - z (i + 1) := by simp [he, hp]
        linarith
      · linarith
      · exact hzi
    have h := hz.inner_le hy
    rw [hy_def, sum_bump N p s (by omega) _ z e] at h
    by_contra hc
    push_neg at hc
    have := mul_pos he0 hc
    linarith
  refine ⟨le_antisymm (hpre q hpq' le_rfl) ?_, hpre⟩
  set e : ℝ := if q + 1 < N then z q - z (q + 1) else 1 with he
  have he0 : 0 < e := by
    by_cases h0 : q + 1 < N
    · simp only [he, h0, if_true, sub_pos]
      have h1 : z (q + 1) ≤ z q := hz.1 q h0
      have h2 : z (q + 1) ≠ z q := fun h => by
        have := (hiff (q + 1) h0).1 (by rw [h]; exact (hiff q hqN).2 ⟨hpq', le_rfl⟩)
        omega
      exact lt_of_le_of_ne h1 h2
    · simp [he, h0]
  set y : ℕ → ℝ := fun j => if p ≤ j ∧ j ≤ q then z j + -e else z j with hy_def
  have hy : NonIncr N y := by
    intro i hi
    have hzi := hz.1 i hi
    simp only [hy_def]
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · have hq : q = i := by omega
      have : e = z i - z (i + 1) := by simp [he, hq, hi]
      linarith
    · exact hzi
  have h := hz.inner_le hy
  rw [hy_def, sum_bump N p q hqN _ z (-e)] at h
  by_contra hc
  push_neg at hc
  have := mul_pos he0 (neg_pos.2 hc)
  linarith

/-- Sufficiency direction, step 1: the level-set conditions imply the global conditions. (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
theorem levelCond_kkt (hz : NonIncr N z) (h : LevelCond N x z) : KKT N x z := by
  have key : ∀ s, s < N → ∀ p q, IsLevelInterval N z p q → p ≤ s → s ≤ q →
      resid x z (s + 1) = ∑ j ∈ Icc p s, (x j - z j) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
    intro hs p q hpq hps hsq
    have hsplit : resid x z (s + 1) = resid x z p + ∑ j ∈ Icc p s, (x j - z j) := by
      rw [resid, resid, ← Finset.Ico_add_one_right_eq_Icc, sum_range_add_sum_Ico _ (by omega)]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp [hp, resid]
    · obtain ⟨p', q', hp', hq', hpq'⟩ := exists_levelInterval hz (show p - 1 < N by omega)
      have hq'eq : q' = p - 1 := by
        by_contra hne
        have hq'p : p ≤ q' := by omega
        have e1 := hpq'.eq (show p' ≤ p by omega) hq'p
        have e2 := hpq'.eq hp' hq'
        have := (hpq.2.2 (p - 1) (by omega)).1 (by rw [e2, e1])
        omega
      subst hq'eq
      have := ih (p - 1) (by omega) (by omega) p' (p - 1) hpq' hp' le_rfl
      rw [show p - 1 + 1 = p by omega] at this
      rw [this, (h p' (p - 1) hpq').1, zero_add]
  refine ⟨hz, fun n hn => ?_, ?_, fun s hs hlt => ?_⟩
  · rcases n with _ | s
    · simp [resid]
    · obtain ⟨p, q, hps, hsq, hpq⟩ := exists_levelInterval hz (show s < N by omega)
      rw [key s (by omega) p q hpq hps hsq]
      exact (h p q hpq).2 s hps hsq
  · rcases N with _ | s
    · simp [resid]
    · obtain ⟨p, q, hps, hsq, hpq⟩ := exists_levelInterval hz (show s < s + 1 by omega)
      have hq : q = s := by have := hpq.2.1; omega
      subst hq
      rw [key q (by omega) p q hpq hps hsq]
      exact (h p q hpq).1
  · obtain ⟨p, q, hps, hsq, hpq⟩ := exists_levelInterval hz (show s < N by omega)
    have hq : q = s := by
      by_contra hne
      have e1 := hpq.eq (show p ≤ s + 1 by omega) (show s + 1 ≤ q by omega)
      have e2 := hpq.eq hps hsq
      rw [e1, e2] at hlt
      exact lt_irrefl _ hlt
    subst hq
    rw [key q (by omega) p q hpq hps hsq]
    exact (h p q hpq).1

lemma abel_aux (r y : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), r j * y j = (∑ j ∈ range (n + 1), r j) * y n +
      ∑ s ∈ range n, (∑ j ∈ range (s + 1), r j) * (y s - y (s + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ (fun j => r j * y j), ih, sum_range_succ (fun s => _ * _),
      sum_range_succ r (n + 1)]
    ring

/-- Sufficiency direction, step 2: the global conditions imply minimality (Abel summation). (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
theorem KKT.isFit (h : KKT N x z) : IsFit N x z := by
  obtain ⟨hz, hle, htot, hdrop⟩ := h
  refine ⟨hz, fun y hy => ?_⟩
  rcases N with _ | n
  · simp [sqDist]
  have htot' : ∑ j ∈ range (n + 1), (x j - z j) = 0 := htot
  have hry : ∑ j ∈ range (n + 1), (x j - z j) * y j ≤ 0 := by
    rw [abel_aux, htot', zero_mul, zero_add]
    apply sum_nonpos
    intro s hs
    rw [mem_range] at hs
    exact mul_nonpos_of_nonpos_of_nonneg (hle (s + 1) (by omega)) (by linarith [hy s (by omega)])
  have hrz : ∑ j ∈ range (n + 1), (x j - z j) * z j = 0 := by
    rw [abel_aux, htot', zero_mul, zero_add]
    apply sum_eq_zero
    intro s hs
    rw [mem_range] at hs
    rcases (hz s (by omega)).lt_or_eq with hlt | heq
    · have : resid x z (s + 1) = 0 := hdrop s (by omega) hlt
      rw [resid] at this
      rw [this, zero_mul]
    · rw [heq, sub_self, mul_zero]
  have hexp : sqDist (n + 1) x y = sqDist (n + 1) x z + ∑ j ∈ range (n + 1), (z j - y j) ^ 2 +
      2 * (∑ j ∈ range (n + 1), (x j - z j) * z j - ∑ j ∈ range (n + 1), (x j - z j) * y j) := by
    simp only [sqDist, mul_sub, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hexp]
  have := sum_nonneg (fun j (_ : j ∈ range (n + 1)) => sq_nonneg (z j - y j))
  linarith

/-- The fit satisfies the global conditions. (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
theorem fit_kkt (N : ℕ) (x : ℕ → ℝ) : KKT N x (fit N x) :=
  levelCond_kkt (fit_nonIncr N x) (fit_isFit N x).levelCond

/-- The global conditions characterize the fit. (Auxiliary result for Lemma 7.1 of `C1_antitonic_fits.md`.) -/
theorem fit_eq_of_kkt (h : KKT N x z) : ∀ j < N, fit N x j = z j := fit_unique h.isFit

theorem fit_resid_total (N : ℕ) (x : ℕ → ℝ) : resid x (fit N x) N = 0 := (fit_kkt N x).2.2.1

/-- **Lemma 7.1** of `C1_antitonic_fits.md` (characterization): a non-increasing sequence `z`
equals `fit(x)` if and only if, for every level set `[p, q]` of `z`,
`Σ_{j=p}^{q} (x_j − z_j) = 0` and `Σ_{j=p}^{s} (x_j − z_j) ≤ 0` for every `p ≤ s ≤ q`. -/
theorem lemma_7_1 (hz : NonIncr N z) :
    (∀ j < N, z j = fit N x j) ↔
      ∀ p q, IsLevelInterval N z p q →
        ∑ j ∈ Icc p q, (x j - z j) = 0 ∧ ∀ s, p ≤ s → s ≤ q → ∑ j ∈ Icc p s, (x j - z j) ≤ 0 := by
  constructor
  · intro h
    exact ((fit_isFit N x).congr (fun _ _ => rfl) (fun j hj => (h j hj).symm)).levelCond
  · intro h j hj
    exact (fit_eq_of_kkt (levelCond_kkt hz h) j hj).symm

/-- Consequence of **Lemma 7.1** (first half of **(L)** of `C1_antitonic_fits.md`, real version):
on every level set `[p, q]` of `fit(x)`, `Σ_{j=p}^{q} x_j = (q − p + 1) · fit(x)_p`. -/
theorem sum_levelInterval_fit {p q : ℕ} (h : IsLevelInterval N (fit N x) p q) :
    ∑ j ∈ Icc p q, x j = ((q - p + 1 : ℕ) : ℝ) * fit N x p := by
  have h0 := ((fit_isFit N x).levelCond p q h).1
  rw [sum_sub_distrib, sum_congr rfl (fun j hj => h.eq (mem_Icc.1 hj).1 (mem_Icc.1 hj).2)] at h0
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at h0
  rw [show q - p + 1 = q + 1 - p by have := h.1; omega]
  linarith

/-- Level-set version: `Σ_{i ∈ levelSet j} x_i = |levelSet j| · fit(x)_j`. (Auxiliary result for (L) of `C1_antitonic_fits.md`.) -/
theorem sum_levelSet_fit {j : ℕ} (hj : j < N) :
    ∑ i ∈ levelSet N (fit N x) j, x i = ((levelSet N (fit N x) j).card : ℝ) * fit N x j := by
  obtain ⟨p, q, hpj, hjq, h, hL⟩ := levelSet_isInterval (fit_nonIncr N x) hj
  rw [hL, sum_levelInterval_fit h, Nat.card_Icc, h.eq hpj hjq,
    show q - p + 1 = q + 1 - p by have := h.1; omega]

end AntitonicFit
