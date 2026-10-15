module

public import RequestProject.OddWindows.Steps

/-!
# `CSI12_the_odd_windows.md` — **Part W** for an abstract digit function

Namespace `ColouredSand.OddTwist`.  The windows theorem for CSI10's moves `iterD p dg h D₀`
starting from the one-slot data `D₀ = (Unit, Q_0)`, `Q_0(φ) = p^{e−1}(φ + i)` (CSI9's `Q0`), for
an arbitrary digit function `dg` and set `I` with `dg t < p` and `t ∈ I ↔ dg t ≠ 0` for `t < h`.
Entries are read in a field `K` of characteristic `0` through a ring homomorphism `φ : A →+* K`
(in the application `ℤ_[p] → ℚ_[p]`).

* `labels_gen`: the slot labels `slotLab` are a bijection onto the subsets of `I ∩ [0, h)`.
* `W1_gen`: **(W1)** for every `h`, floor `f` and slots `x, y`.
* `W2_gen`: **(W2)**, more generally for the product `P_h(0) ⋯ P_h(s − 1)` of any number `s ≥ 1`
  of payments at any level `h` (CSI10's `Mp` is `h = k`, `s = d_k`).
* `cW_supp`: `c^{(h)}` vanishes off the subsets of `[0, h)`.

Oddness of `p` is not needed: only `p ≥ 2`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

/-! ### Part C: support and the two values used by the moves -/

/-- `c^{(h)}` vanishes off the subsets of `[0, h)` (*Part C* of `CSI12_the_odd_windows.md`). -/
lemma cW_supp (p : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) :
    ∀ h Δ, ¬ Δ ⊆ range h → cW p I dg h Δ = 0 := by
  intro h
  induction h with
  | zero =>
    intro Δ hΔ
    have : Δ ≠ ∅ := by rintro rfl; exact hΔ (empty_subset _)
    simp [cW, this]
  | succ h ih =>
    intro Δ hΔ
    have h1 : ¬ Δ ⊆ range h := fun hs => hΔ (hs.trans (range_subset_range.2 (by omega)))
    simp only [cW]
    rw [starPow_supp ih p Δ h1, mul_zero, zero_add]
    by_cases hh : h ∈ Δ
    · have : ¬ Δ \ {h} ⊆ range h := by
        intro hs; apply hΔ
        intro t ht
        by_cases hth : t = h
        · subst hth; exact mem_range.2 (by omega)
        · have := hs (mem_sdiff.2 ⟨ht, by simpa using hth⟩)
          rw [mem_range] at this ⊢; omega
      rw [xMul, if_pos hh, starPow_supp ih _ _ this, mul_zero]
    · rw [xMul, if_neg hh, mul_zero]

lemma cW_succ_of_notMem (p : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (h : ℕ) {Δ : Finset ℕ} (hΔ : h ∉ Δ) :
    cW p I dg (h + 1) Δ = (-1 / (p : ℚ)) * starPow (cW p I dg h) p Δ := by
  simp [cW, xMul, hΔ]

lemma cW_succ_insert (p : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (h : ℕ) (hI : h ∈ I) {Δ : Finset ℕ}
    (hΔ : h ∉ Δ) :
    cW p I dg (h + 1) (insert h Δ) = bW p dg h * starPow (cW p I dg h) (p - dg h) Δ := by
  have h0 : starPow (cW p I dg h) p (insert h Δ) = 0 :=
    starPow_supp (cW_supp p I dg h) p _ (fun hs => by simpa using hs (mem_insert_self h Δ))
  have h1 : insert h Δ \ {h} = Δ := by
    ext t; by_cases hth : t = h
    · subst hth; simp [hΔ]
    · simp [hth]
  simp [cW, xMul, hI, h0, h1]

variable {A K : Type*} [CommRing A] [Field K] [CharZero K]

lemma cast_starPow (f : Finset ℕ → ℚ) (n : ℕ) (Δ : Finset ℕ) :
    ((starPow f n Δ : ℚ) : K) = starPow (fun Γ => (f Γ : K)) n Δ := by
  have := map_starPow (Rat.castHom K) f n Δ
  simpa [Rat.coe_castHom] using this

/-! ### Transport along `stepD` -/

lemma transport_S (Pr : (D : SData A) → (D.S → Finset ℕ) → Prop) {D₁ D₂ : SData A} (e : D₁ = D₂)
    (he : D₁.S = D₂.S) (L : D₂.S → Finset ℕ) (h : Pr D₂ L) : Pr D₁ (fun x => L (cast he x)) := by
  subst e; exact h

lemma labStep_zero_pr (Pr : (D : SData A) → (D.S → Finset ℕ) → Prop) (p d h : ℕ) (hd : d = 0)
    (D : SData A) (L : D.S → Finset ℕ) (hP : Pr ⟨D.S, QT p D.Q⟩ L) :
    Pr (stepD p d D) (labStep p d h D L) := by
  have : labStep p d h D L = fun x => L (cast (stepD_S_zero p d hd D) x) := by
    unfold labStep; rw [dif_pos hd]
  rw [this]
  exact transport_S Pr (stepD_zero_of p d hd D) _ L hP

lemma labStep_pos_pr (Pr : (D : SData A) → (D.S → Finset ℕ) → Prop) (p d h : ℕ) (hd : d ≠ 0)
    (D : SData A) (L : D.S → Finset ℕ)
    (hP : Pr ⟨D.S × Bool, QS p d D.Q⟩ (fun y => if y.2 then insert h (L y.1) else L y.1)) :
    Pr (stepD p d D) (labStep p d h D L) := by
  have : labStep p d h D L = fun x =>
      (fun y : D.S × Bool => if y.2 then insert h (L y.1) else L y.1)
        (cast (stepD_S_pos p d hd D) x) := by
    unfold labStep; rw [dif_neg hd]
  rw [this]
  exact transport_S Pr (stepD_pos p d hd D) _ _ hP

/-! ### The induction -/

/-- **Slots as subsets** (*Setting* of `CSI12_the_odd_windows.md`), abstract digits: after `h`
moves (from one slot `Unit`, any data) the labels `slotLab` are a bijection from the slots onto
the subsets of `I ∩ [0, h)`. -/
theorem labels_gen (p : ℕ) (dg : ℕ → ℕ) (I : Finset ℕ) (Q : ℕ → Matrix Unit Unit A) :
    ∀ h, (∀ t < h, (t ∈ I ↔ dg t ≠ 0)) →
      LabP (I.filter (· < h)) (slotLab p dg (⟨Unit, Q⟩ : SData A) h) := by
  intro h
  induction h with
  | zero =>
    intro _
    have : I.filter (· < 0) = ∅ := by ext t; simp
    rw [this]
    exact LabP_base
  | succ h ih =>
    intro hI
    have hL := ih (fun t ht => hI t (by omega))
    have hJ : ∀ t ∈ I.filter (· < h), t < h := fun t ht => (mem_filter.1 ht).2
    have hhI := hI h (by omega)
    by_cases hd : dg h = 0
    · have hJ' : I.filter (· < h + 1) = I.filter (· < h) := by
        ext t
        simp only [mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
          · exact h2
          · exact absurd (hhI.1 h1) (not_not.2 hd)
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      rw [hJ']
      exact labStep_zero_pr (fun _ L => LabP (I.filter (· < h)) L) p (dg h) h hd _ _ hL
    · have hhI' : h ∈ I := hhI.2 hd
      have hJ' : I.filter (· < h + 1) = insert h (I.filter (· < h)) := by
        ext t
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hhI', by omega⟩
          · exact ⟨h1, by omega⟩
      rw [hJ']
      exact labStep_pos_pr (fun _ L => LabP (insert h (I.filter (· < h))) L) p (dg h) h hd _ _
        (split_lab hL hJ)

variable (φ : A →+* K) (p : ℕ) (dg : ℕ → ℕ) (I : Finset ℕ) (e i : ℕ)

/-- **The induction of Theorem 4.1** (*Part W* of `CSI12_the_odd_windows.md`): after `h` moves
every payment is in window form with coefficient `c^{(h)}` and the labels `slotLab`. -/
theorem win_iter (hp : 2 ≤ p) (he : 1 ≤ e) : ∀ h, (∀ t < h, dg t < p) →
    (∀ t < h, (t ∈ I ↔ dg t ≠ 0)) →
      WinP φ (fun d => (piW p e i d : K)) p dg (fun Δ => (cW p I dg h Δ : K)) h
        (iterD p dg h ⟨Unit, Q0 A p e i⟩) (slotLab p dg ⟨Unit, Q0 A p e i⟩ h) := by
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  intro h
  induction h with
  | zero => intro _ _; exact base_win φ p dg I e i he
  | succ h ih =>
    intro hdg hI
    have hW := ih (fun t ht => hdg t (by omega)) (fun t ht => hI t (by omega))
    have hL := labels_gen p dg I (Q0 A p e i) h (fun t ht => hI t (by omega))
    have hJ : ∀ t ∈ I.filter (· < h), t < h := fun t ht => (mem_filter.1 ht).2
    have hdg' : ∀ t < h, dg t < p := fun t ht => hdg t (by omega)
    have hhI := hI h (by omega)
    by_cases hd : dg h = 0
    · refine labStep_zero_pr (fun D L =>
          WinP φ (fun d => (piW p e i d : K)) p dg (fun Δ => (cW p I dg (h + 1) Δ : K)) (h + 1)
            D L) p (dg h) h hd _ _ ?_
      refine twist_step φ _ dg hp hpK hL hJ hdg' (fun Δ hΔ => ?_) hW
      have hhΔ : h ∉ Δ := fun hh => lt_irrefl _ (hJ h (hΔ hh))
      rw [cW_succ_of_notMem p I dg h hhΔ]
      push_cast
      rw [cast_starPow]
    · have hhI' : h ∈ I := hhI.2 hd
      refine labStep_pos_pr (fun D L =>
          WinP φ (fun d => (piW p e i d : K)) p dg (fun Δ => (cW p I dg (h + 1) Δ : K)) (h + 1)
            D L) p (dg h) h hd _ _ ?_
      refine split_step φ _ dg hp hpK (hdg h (by omega)) rfl hL hJ hdg' (fun Δ hΔ => ?_)
        (fun Δ hΔ => ?_) hW
      · have hhΔ : h ∉ Δ := fun hh => lt_irrefl _ (hJ h (hΔ hh))
        rw [cW_succ_of_notMem p I dg h hhΔ]
        push_cast
        rw [cast_starPow]
      · have hhΔ : h ∉ Δ := fun hh => lt_irrefl _ (hJ h (hΔ hh))
        rw [cW_succ_insert p I dg h hhI' hhΔ, bW]
        push_cast
        rw [cast_starPow]

lemma Icc_pred_eq_Ico (a b : ℕ) (hb : 1 ≤ b) : Icc a (b - 1) = Ico a b := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hb]

/-- **(W1) Theorem 4.1**, abstract digits (*Part W* of `CSI12_the_odd_windows.md`): for every
`h` with `dg t < p` and `t ∈ I ↔ dg t ≠ 0` for `t < h`, every floor `f` and slots `x, y` with
labels `D = L x`, `D' = L y` (subsets of `I ∩ [0, h)`, `labels_gen`):
`P_h(f)_{D D'} = c^{(h)}(D ∖ D') · ∏_{d ∈ [p^h f + o_D, p^h f + o_{D'} + p^h − 1]} π_0(d)` if
`D' ⊆ D`, and `0` otherwise.  Here `P_h(f) = p • Q_h(f)` is read in `K` through `φ`. -/
theorem W1_gen (hp : 2 ≤ p) (he : 1 ≤ e) (h : ℕ) (hdg : ∀ t < h, dg t < p)
    (hI : ∀ t < h, (t ∈ I ↔ dg t ≠ 0)) (f : ℕ)
    (x y : (iterD p dg h (⟨Unit, Q0 A p e i⟩ : SData A)).S) :
    φ (((p : A) • (iterD p dg h (⟨Unit, Q0 A p e i⟩ : SData A)).Q f) x y) =
      ((if slotLab p dg ⟨Unit, Q0 A p e i⟩ h y ⊆ slotLab p dg ⟨Unit, Q0 A p e i⟩ h x then
          cW p I dg h (slotLab p dg ⟨Unit, Q0 A p e i⟩ h x \ slotLab p dg ⟨Unit, Q0 A p e i⟩ h y) *
            ∏ d ∈ Icc (p ^ h * f + oW p dg (slotLab p dg ⟨Unit, Q0 A p e i⟩ h x))
              (p ^ h * f + oW p dg (slotLab p dg ⟨Unit, Q0 A p e i⟩ h y) + p ^ h - 1),
              piW p e i d
        else 0 : ℚ) : K) := by
  have hW := win_iter φ p dg I e i hp he h hdg hI f x y
  rw [PmQ_apply] at hW
  rw [Matrix.smul_apply, smul_eq_mul, hW]
  have hph : 1 ≤ p ^ h := Nat.one_le_pow _ _ (by omega)
  split_ifs with hxy
  · rw [Icc_pred_eq_Ico _ _ (by omega)]
    push_cast
    congr 2
    · unfold oW; congr 1; ring
  · simp

/-- **(W2)**, abstract digits and more general (*Part W* of `CSI12_the_odd_windows.md`): for any
level `h` and any number `s ≥ 1` of factors, `p^s • (Q_h(0) ⋯ Q_h(s − 1)) = P_h(0) ⋯ P_h(s − 1)`
has the entries `[(c^{(h)})^{⋆s}](D ∖ D') · ∏_{d = o_D}^{o_{D'} + s p^h − 1} π_0(d)` for
`D' ⊆ D`, and `0` otherwise.  CSI10's `Mp` is the case `h = k`, `s = d_k`. -/
theorem W2_gen (hp : 2 ≤ p) (he : 1 ≤ e) (h : ℕ) (hdg : ∀ t < h, dg t < p)
    (hI : ∀ t < h, (t ∈ I ↔ dg t ≠ 0)) (s : ℕ) (hs : 1 ≤ s)
    (x y : (iterD p dg h (⟨Unit, Q0 A p e i⟩ : SData A)).S) :
    φ (((p : A) ^ s • prodQ (iterD p dg h (⟨Unit, Q0 A p e i⟩ : SData A)).Q 0 s) x y) =
      ((if slotLab p dg ⟨Unit, Q0 A p e i⟩ h y ⊆ slotLab p dg ⟨Unit, Q0 A p e i⟩ h x then
          starPow (cW p I dg h) s
              (slotLab p dg ⟨Unit, Q0 A p e i⟩ h x \ slotLab p dg ⟨Unit, Q0 A p e i⟩ h y) *
            ∏ d ∈ Icc (oW p dg (slotLab p dg ⟨Unit, Q0 A p e i⟩ h x))
              (oW p dg (slotLab p dg ⟨Unit, Q0 A p e i⟩ h y) + s * p ^ h - 1), piW p e i d
        else 0 : ℚ) : K) := by
  have hpK : φ (p : A) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast (show p ≠ 0 by omega)
  have hW := win_iter φ p dg I e i hp he h hdg hI
  have hL := labels_gen p dg I (Q0 A p e i) h hI
  have hJ : ∀ t ∈ I.filter (· < h), t < h := fun t ht => (mem_filter.1 ht).2
  have hprod := WinF_prodList hL (p ^ h) (o_le_of_lt dg (by omega) hdg hJ) _ hW s 0
  set Q := (iterD p dg h (⟨Unit, Q0 A p e i⟩ : SData A)).Q
  have e1 : ((p : A) ^ s • prodQ Q 0 s).map φ =
      ((List.range s).map (fun j => PmQ φ p Q (0 + j))).prod := by
    unfold prodQ PmQ
    rw [list_prod_smul_range, map_smul_matrix, map_list_prod_range, map_pow, Nat.sub_zero]
  change (((p : A) ^ s • prodQ Q 0 s).map φ) x y = _
  rw [e1, hprod x y]
  have hph : 1 ≤ p ^ h := Nat.one_le_pow _ _ (by omega)
  have hsp : 1 ≤ s * p ^ h := Nat.one_le_iff_ne_zero.2 (by positivity)
  split_ifs with hxy
  · rw [Icc_pred_eq_Ico _ _ (by omega)]
    push_cast
    rw [cast_starPow]
    congr 2
    · unfold oW; congr 1 <;> ring
  · simp

end ColouredSand.OddTwist
