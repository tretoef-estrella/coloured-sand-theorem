module

public import RequestProject.AntitonicFit.IntegerFit

/-!
# Cuts: consequence (D) and Lemma 7.2 (cuts and shifts)

This file formalizes the *Definition (cuts)* of `C1_antitonic_fits.md`, the consequence **(D)**
of Lemma 7.1, and **Lemma 7.2** (a), (b1), (b2), (b3), (c).

Recall the encoding (see `RequestProject/AntitonicFit/Basic.lean`): `fit b x` is
`fit(x_{<b})`, `fit (N - b) (shift b x)` is `fit(x_{≥b})`, and `concat b u v` is `[u, v]`.
-/

@[expose] public section

namespace AntitonicFit

open Finset

/-- *Definition (cuts)* of `C1_antitonic_fits.md`: for `0 < b < N`, `x` (of length `N`) is
**cut at `b`** if `fit(x) = [fit(x_{<b}), fit(x_{≥b})]`. -/
def IsCut (N : ℕ) (x : ℕ → ℝ) (b : ℕ) : Prop :=
  0 < b ∧ b < N ∧ ∀ j < N, fit N x j = concat b (fit b x) (fit (N - b) (shift b x)) j

/-- *Definition (cuts)* of `C1_antitonic_fits.md`: the cut at `b` is **strict** if moreover
`fit(x)_{b−1} > fit(x)_b`. -/
def IsStrictCut (N : ℕ) (x : ℕ → ℝ) (b : ℕ) : Prop :=
  IsCut N x b ∧ fit N x b < fit N x (b - 1)

/-- *Statement (b)* of Lemma 7.2 in `C1_antitonic_fits.md`: `δ` is constant on every level set of
`z` (of length `N`), i.e. `z_i = z_j` implies `δ_i = δ_j`. -/
def ConstOnLevelSets {α : Type*} (N : ℕ) (z : ℕ → ℝ) (δ : ℕ → α) : Prop :=
  ∀ i j, i < N → j < N → z i = z j → δ i = δ j

variable {N b : ℕ} {x : ℕ → ℝ}

/-- Cut criterion (proof tool): `x` is cut at `b` iff `Σ_{j<b} (x_j − fit(x)_j) = 0`. (Auxiliary result for (D) and Lemma 7.2 of `C1_antitonic_fits.md`.) -/
theorem isCut_iff_resid : IsCut N x b ↔ 0 < b ∧ b < N ∧ resid x (fit N x) b = 0 := by
  constructor
  · rintro ⟨hb0, hbN, h⟩
    refine ⟨hb0, hbN, ?_⟩
    have : resid x (fit N x) b = resid x (fit b x) b :=
      resid_congr (fun _ _ => rfl) (fun j hj => by rw [h j (by omega), concat, if_pos hj])
    rw [this]
    exact fit_resid_total b x
  · rintro ⟨hb0, hbN, hr⟩
    refine ⟨hb0, hbN, ?_⟩
    obtain ⟨hz, hle, htot, hdrop⟩ := fit_kkt N x
    have hpre : ∀ j < b, fit b x j = fit N x j := fit_eq_of_kkt
      ⟨hz.mono hbN.le, fun n hn => hle n (by omega), hr, fun s hs hlt => hdrop s (by omega) hlt⟩
    have hres : ∀ m, resid x (fit N x) (b + m) = resid (shift b x) (shift b (fit N x)) m := by
      intro m; rw [resid_add, hr, zero_add]
    have hsuf : ∀ j < N - b, fit (N - b) (shift b x) j = shift b (fit N x) j := by
      apply fit_eq_of_kkt
      refine ⟨fun i hi => hz (b + i) (by omega), fun n hn => ?_, ?_, fun s hs hlt => ?_⟩
      · rw [← hres]; exact hle _ (by omega)
      · rw [← hres, show b + (N - b) = N by omega]; exact htot
      · rw [← hres]; exact hdrop (b + s) (by omega) hlt
    intro j hj
    simp only [concat]
    split_ifs with h
    · exact (hpre j h).symm
    · rw [hsuf (j - b) (by omega)]
      simp [shift, show b + (j - b) = j by omega]

/-- **(D)** of `C1_antitonic_fits.md`, first part: if `0 < b < N` and
`fit(x)_{b−1} > fit(x)_b`, then `x` is cut at `b`. -/
theorem consequence_D_cut (hb0 : 0 < b) (hbN : b < N) (hlt : fit N x b < fit N x (b - 1)) :
    IsCut N x b := by
  refine isCut_iff_resid.2 ⟨hb0, hbN, ?_⟩
  have := (fit_kkt N x).2.2.2 (b - 1) (by omega)
  rw [show b - 1 + 1 = b by omega] at this
  exact this hlt

/-- **(D)** of `C1_antitonic_fits.md`, second part: `b` (with `0 < b < N`) is a strict cut iff no
level set of `fit(x)` contains both `b − 1` and `b`. -/
theorem consequence_D_strict_iff (hb0 : 0 < b) (hbN : b < N) :
    IsStrictCut N x b ↔ ¬ ∃ p q, IsLevelInterval N (fit N x) p q ∧ p ≤ b - 1 ∧ b ≤ q := by
  constructor
  · rintro ⟨-, hlt⟩ ⟨p, q, h, hp, hq⟩
    rw [h.eq (by omega) hq, h.eq hp (by omega)] at hlt
    exact lt_irrefl _ hlt
  · intro hno
    obtain ⟨p, q, hp, hq, h⟩ := exists_levelInterval (fit_nonIncr N x) (show b - 1 < N by omega)
    have hqb : q = b - 1 := by
      by_contra hne
      exact hno ⟨p, q, h, hp, by omega⟩
    have hne : fit N x b ≠ fit N x (b - 1) := by
      intro he
      rw [h.eq hp hq] at he
      have := (h.2.2 b hbN).1 he
      omega
    have hle : fit N x b ≤ fit N x (b - 1) := (fit_nonIncr N x).anti (by omega) hbN
    have hlt := lt_of_le_of_ne hle hne
    exact ⟨consequence_D_cut hb0 hbN hlt, hlt⟩

/-- **Lemma 7.2 (a)** of `C1_antitonic_fits.md`: if `0 < b < N` and
`[fit(x_{<b}), fit(x_{≥b})]` is non-increasing, then `x` is cut at `b`. -/
theorem lemma_7_2_a (hb0 : 0 < b) (hbN : b < N)
    (hmono : NonIncr N (concat b (fit b x) (fit (N - b) (shift b x)))) : IsCut N x b := by
  refine ⟨hb0, hbN, fit_eq_of_kkt ?_⟩
  set w := concat b (fit b x) (fit (N - b) (shift b x)) with hw
  obtain ⟨-, hule, hutot, hudrop⟩ := fit_kkt b x
  obtain ⟨-, hvle, hvtot, hvdrop⟩ := fit_kkt (N - b) (shift b x)
  have hwu : ∀ n ≤ b, resid x w n = resid x (fit b x) n := fun n hn =>
    resid_congr (fun _ _ => rfl) (fun j hj => by simp [w, concat, show j < b by omega])
  have hshift : shift b w = fit (N - b) (shift b x) := by
    funext j; simp [w, shift, concat]
  have hwv : ∀ m, resid x w (b + m) = resid (shift b x) (fit (N - b) (shift b x)) m := by
    intro m; rw [resid_add, hshift, hwu b le_rfl, hutot, zero_add]
  refine ⟨hmono, fun n hn => ?_, ?_, fun s hs hlt => ?_⟩
  · by_cases hnb : n ≤ b
    · rw [hwu n hnb]; exact hule n hnb
    · obtain ⟨m, rfl⟩ : ∃ m, n = b + m := ⟨n - b, by omega⟩
      rw [hwv]; exact hvle m (by omega)
  · have := hwv (N - b)
    rw [show b + (N - b) = N by omega] at this
    rw [this]; exact hvtot
  · rcases lt_trichotomy (s + 1) b with h | h | h
    · rw [hwu _ h.le]
      apply hudrop s h
      simpa [w, concat, h, show s < b by omega] using hlt
    · rw [h, hwu b le_rfl, hutot]
    · obtain ⟨t, rfl⟩ : ∃ t, s = b + t := ⟨s - b, by omega⟩
      rw [show b + t + 1 = b + (t + 1) by omega, hwv]
      apply hvdrop t (by omega)
      have e1 : w (b + t + 1) = fit (N - b) (shift b x) (t + 1) := by
        simp only [w, concat]; rw [if_neg (by omega)]; congr 1; omega
      have e2 : w (b + t) = fit (N - b) (shift b x) t := by
        simp only [w, concat]; rw [if_neg (by omega)]; congr 1; omega
      rw [e1, e2] at hlt
      exact hlt

/-- **Lemma 7.2 (b1)** of `C1_antitonic_fits.md`.  The cut positions `b_1 < ⋯ < b_s` are given as
a finite set `B` (`s = |B| ≥ 0`), each of which is a cut of `x`.  "`δ` is constant on each of the
intervals `[0, b_1), [b_1, b_2), …, [b_s, N)`" is encoded as: `δ_{j+1} = δ_j` whenever
`j + 1 < N` and `j + 1 ∉ B`.  Then `fit(x + δ) = fit(x) + δ`, and `x + δ` is cut at each `b_i`. -/
theorem lemma_7_2_b1 {B : Finset ℕ} (hB : ∀ b ∈ B, IsCut N x b) {δ : ℕ → ℝ} (hδ : NonIncr N δ)
    (hδc : ∀ j, j + 1 < N → j + 1 ∉ B → δ (j + 1) = δ j) :
    (∀ j < N, fit N (x + δ) j = fit N x j + δ j) ∧ ∀ b ∈ B, IsCut N (x + δ) b := by
  obtain ⟨hz, hle, htot, hdrop⟩ := fit_kkt N x
  have hres : ∀ n, resid (x + δ) (fit N x + δ) n = resid x (fit N x) n := fun n =>
    sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  have hfit : ∀ j < N, fit N (x + δ) j = (fit N x + δ) j := by
    apply fit_eq_of_kkt
    refine ⟨fun i hi => ?_, fun n hn => by rw [hres]; exact hle n hn, by rw [hres]; exact htot,
      fun s hs hlt => ?_⟩
    · simp only [Pi.add_apply]; linarith [hz i hi, hδ i hi]
    · rw [hres]
      simp only [Pi.add_apply] at hlt
      rcases (hz s hs).lt_or_eq with h1 | h1
      · exact hdrop s hs h1
      · have h2 : δ (s + 1) ≠ δ s := fun h => by rw [h1, h] at hlt; exact lt_irrefl _ hlt
        have hsB : s + 1 ∈ B := by
          by_contra hn; exact h2 (hδc s hs hn)
        exact (isCut_iff_resid.1 (hB _ hsB)).2.2
  refine ⟨hfit, fun b hb => ?_⟩
  obtain ⟨hb0, hbN, hr⟩ := isCut_iff_resid.1 (hB b hb)
  refine isCut_iff_resid.2 ⟨hb0, hbN, ?_⟩
  rw [resid_congr (fun _ _ => rfl) (fun j hj => hfit j (by omega)), hres, hr]

/-- **Lemma 7.2 (b2)** of `C1_antitonic_fits.md`.  Let `x, δ` be integer sequences with `δ`
non-increasing and constant on every level set of `fit(x)`.  Then the level sets of
`fit(x + δ)` are exactly those of `fit(x)`, every strict cut of `x` is a strict cut of `x + δ`,
and `ifit(x + δ) = ifit(x) + δ`.

*More general than the file:* the hypotheses that `x` is cut at positions `b_1 < ⋯ < b_s` and
that `δ` is constant between consecutive `b_i` (the setting of (b)) are not needed — they follow
from the other hypotheses (take for the `b_i` the positions where `δ` drops; these are strict
drops of `fit(x)`, hence cuts by (D)). -/
theorem lemma_7_2_b2 {x δ : ℕ → ℤ} (hδ : NonIncr N (toR δ))
    (hδc : ConstOnLevelSets N (fit N (toR x)) δ) :
    (∀ j < N, levelSet N (fit N (toR (x + δ))) j = levelSet N (fit N (toR x)) j) ∧
      (∀ b, IsStrictCut N (toR x) b → IsStrictCut N (toR (x + δ)) b) ∧
      (∀ j < N, ifit N (x + δ) j = ifit N x j + δ j) := by
  set z := fit N (toR x) with hz_def
  obtain ⟨hz, hle, htot, hdrop⟩ := fit_kkt N (toR x)
  have hres : ∀ n, resid (toR (x + δ)) (z + toR δ) n = resid (toR x) z n := fun n =>
    sum_congr rfl fun j _ => by simp only [Pi.add_apply, toR]; push_cast; ring
  have hfit : ∀ j < N, fit N (toR (x + δ)) j = (z + toR δ) j := by
    apply fit_eq_of_kkt
    refine ⟨fun i hi => ?_, fun n hn => by rw [hres]; exact hle n hn, by rw [hres]; exact htot,
      fun s hs hlt => ?_⟩
    · simp only [Pi.add_apply]; linarith [hz i hi, hδ i hi]
    · rw [hres]
      simp only [Pi.add_apply] at hlt
      rcases (hz s hs).lt_or_eq with h1 | h1
      · exact hdrop s hs h1
      · have := hδc (s + 1) s hs (by omega) h1
        simp only [toR, this] at hlt
        linarith
  have hkey : ∀ i j, i < N → j < N → ((z + toR δ) i = (z + toR δ) j ↔ z i = z j) := by
    intro i j hi hj
    simp only [Pi.add_apply]
    constructor
    · intro he
      rcases le_total i j with hij | hij
      · have := hz.anti hij hj; have := hδ.anti hij hj; linarith
      · have := hz.anti hij hi; have := hδ.anti hij hi; linarith
    · intro he
      rw [he, show toR δ i = toR δ j by simp [toR, hδc i j hi hj he]]
  have hlev : ∀ j < N, levelSet N (fit N (toR (x + δ))) j = levelSet N z j := by
    intro j hj
    rw [levelSet_congr hfit hj]
    ext i
    simp only [levelSet, mem_filter, mem_range]
    constructor
    · rintro ⟨hi, he⟩; exact ⟨hi, (hkey i j hi hj).1 he⟩
    · rintro ⟨hi, he⟩; exact ⟨hi, (hkey i j hi hj).2 he⟩
  refine ⟨hlev, fun b hb => ?_, fun j hj => ?_⟩
  · obtain ⟨hcut, hlt⟩ := hb
    obtain ⟨hb0, hbN, hr⟩ := isCut_iff_resid.1 hcut
    refine ⟨isCut_iff_resid.2 ⟨hb0, hbN, ?_⟩, ?_⟩
    · rw [resid_congr (fun _ _ => rfl) (fun j hj => hfit j (by omega)), hres, hr]
    · rw [hfit b hbN, hfit (b - 1) (by omega)]
      simp only [Pi.add_apply]
      linarith [hδ.anti (show b - 1 ≤ b by omega) hbN]
  · rw [ifit_of_lt hj, ifit_of_lt hj, hlev j hj]
    have hS : ∑ i ∈ levelSet N z j, (x + δ) i =
        ∑ i ∈ levelSet N z j, x i + ((levelSet N z j).card : ℤ) * δ j := by
      rw [Pi.add_def, sum_add_distrib]
      congr 1
      rw [sum_congr rfl (fun i hi => ?_), sum_const, nsmul_eq_mul]
      simp only [levelSet, mem_filter, mem_range] at hi
      exact hδc i j hi.1 hj hi.2
    rw [hS, blockF_add_mul]
    exact card_pos.2 ⟨j, by simp [levelSet, hj]⟩

/-- **Lemma 7.2 (b3)** of `C1_antitonic_fits.md`: if every position `b` (with `0 < b < N`) at which
`δ_{b−1} ≠ δ_b` is a strict cut of `x`, then `δ` is constant on every level set of `fit(x)`.
(*More general than the file:* `δ` may take values in any type, not only in `ℤ`.) -/
theorem lemma_7_2_b3 {α : Type*} {δ : ℕ → α}
    (h : ∀ b, 0 < b → b < N → δ (b - 1) ≠ δ b → IsStrictCut N x b) :
    ConstOnLevelSets N (fit N x) δ := by
  have main : ∀ i j, i ≤ j → j < N → fit N x i = fit N x j → δ i = δ j := by
    intro i j hij hj he
    have : ∀ k, i ≤ k → k ≤ j → δ k = δ i := by
      intro k hik
      induction k, hik using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ k hik ih =>
        intro hkj
        have h1 : fit N x (k + 1) ≤ fit N x k := fit_nonIncr N x k (by omega)
        have h2 : fit N x j ≤ fit N x (k + 1) := (fit_nonIncr N x).anti hkj hj
        have h3 : fit N x k ≤ fit N x i := (fit_nonIncr N x).anti hik (by omega)
        rw [← ih (by omega)]
        by_contra hne
        have := (h (k + 1) (by omega) (by omega) (by simpa using Ne.symm hne)).2
        simp only [Nat.add_sub_cancel] at this
        linarith
    exact (this j hij le_rfl).symm
  intro i j hi hj he
  rcases le_total i j with hij | hij
  · exact main i j hij hj he
  · exact (main j i hij hi he.symm).symm

/-- **Lemma 7.2 (b3)** of `C1_antitonic_fits.md`, "so (b2) applies": for integer `x, δ` with `δ`
non-increasing, if every position where `δ` changes is a strict cut of `x`, then the conclusions
of (b2) hold. -/
theorem lemma_7_2_b3_b2 {x δ : ℕ → ℤ} (hδ : NonIncr N (toR δ))
    (h : ∀ b, 0 < b → b < N → δ (b - 1) ≠ δ b → IsStrictCut N (toR x) b) :
    (∀ j < N, levelSet N (fit N (toR (x + δ))) j = levelSet N (fit N (toR x)) j) ∧
      (∀ b, IsStrictCut N (toR x) b → IsStrictCut N (toR (x + δ)) b) ∧
      (∀ j < N, ifit N (x + δ) j = ifit N x j + δ j) :=
  lemma_7_2_b2 hδ (lemma_7_2_b3 h)

/-- **Lemma 7.2 (c)** of `C1_antitonic_fits.md`: for `0 < b < N`, if `fit(x)_{<b} = fit(x_{<b})`
or `fit(x)_{≥b} = fit(x_{≥b})`, then `x` is cut at `b`. -/
theorem lemma_7_2_c (hb0 : 0 < b) (hbN : b < N)
    (h : (∀ j < b, fit N x j = fit b x j) ∨
      (∀ j < N - b, fit N x (b + j) = fit (N - b) (shift b x) j)) : IsCut N x b := by
  refine isCut_iff_resid.2 ⟨hb0, hbN, ?_⟩
  rcases h with h | h
  · rw [resid_congr (fun _ _ => rfl) h]
    exact fit_resid_total b x
  · have h1 := fit_resid_total N x
    have h2 := resid_add (x := x) (z := fit N x) b (N - b)
    rw [show b + (N - b) = N by omega] at h2
    have h3 : resid (shift b x) (shift b (fit N x)) (N - b) = 0 := by
      rw [resid_congr (z := shift b (fit N x)) (fun _ _ => rfl)
        (z' := fit (N - b) (shift b x)) (fun j hj => h j hj)]
      exact fit_resid_total _ _
    linarith

end AntitonicFit
