module

public import RequestProject.OddWindows.Chain

/-!
# `CSI12_the_odd_windows.md` — the moves of the *Proof* of Theorem 4.1

Namespace `ColouredSand.OddTwist`.

* **The payment.** For data `Q : ℕ → Matrix S S A` (CSI10's halved data) and a ring homomorphism
  `φ : A →+* K`, `PmQ φ p Q f = φ(p) • (Q f).map φ` is the payment `P(f) = p • Q(f)` read in `K`
  (in the application `A = ℤ_[p]`, `K = ℚ_[p]`, `φ` the inclusion).
* `WinP φ π p dg c h D L`: every payment `P_h(f)` of `D` is in window form with coefficient `c`
  and window `[p^h f, p^h (f+1))`, i.e.
  `P_h(f)_{x y} = [L y ⊆ L x] c(L x ∖ L y) ∏_{d ∈ [p^h f + o(L x), p^h f + o(L y) + p^h)} π(d)`.
* `base_win`: level `0` (one slot `Unit`, label `∅`, `P_0 = π_0`).
* `twist_step`: the twist (CSI7's `QT`) at a digit `d_h = 0`: `s = p` factors from `pf`.
* `split_step`, `split_lab`: the split (CSI8's `QS`) at a digit `d_h = r ≠ 0`, slots `S × Bool`:
  `Q_A` (`s = p` from `pf`), `Q_C` (`s = p` from `pf + r`, labels `D ∪ {h}`), `K`
  (`s = p − r` from `pf + r`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

variable {A K : Type*} [CommRing A] [Field K]

/-- The payment `P(f) = p • Q(f)` read in `K` through `φ` (*Setting*, «The payment», of
`CSI12_the_odd_windows.md`). -/
def PmQ (φ : A →+* K) (p : ℕ) {S : Type*} (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S K :=
  φ (p : A) • (Q f).map φ

lemma PmQ_apply (φ : A →+* K) (p : ℕ) {S : Type*} (Q : ℕ → Matrix S S A) (f : ℕ) (x y : S) :
    PmQ φ p Q f x y = φ ((p : A) * Q f x y) := by
  simp [PmQ, Matrix.map_apply]

/-- Every payment `P_h(f)` of `D` is in window form (*Part W* (W1) of
`CSI12_the_odd_windows.md`, the induction hypothesis of the proof). -/
def WinP (φ : A →+* K) (π : ℕ → K) (p : ℕ) (dg : ℕ → ℕ) (c : Finset ℕ → K) (h : ℕ)
    (D : SData A) (L : D.S → Finset ℕ) : Prop :=
  ∀ f, WinF π (fun t => dg t * p ^ t) L c (p ^ h * f) (p ^ h * (f + 1)) (PmQ φ p D.Q f)

section Prod

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma list_prod_smul_range (c : K) (M : ℕ → Matrix S S K) (m : ℕ) :
    ((List.range m).map (fun j => c • M j)).prod = c ^ m • ((List.range m).map M).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [smul_mul_smul_comm, pow_succ]

lemma map_list_prod_range (φ : A →+* K) (M : ℕ → Matrix S S A) (m : ℕ) :
    (((List.range m).map M).prod).map φ = ((List.range m).map (fun j => (M j).map φ)).prod := by
  have := map_list_prod φ.mapMatrix ((List.range m).map M)
  rw [RingHom.mapMatrix_apply, List.map_map] at this
  rw [this]
  rfl

omit [Fintype S] [DecidableEq S] in
lemma map_smul_matrix (φ : A →+* K) (s : A) (M : Matrix S S A) :
    (s • M).map φ = φ s • M.map φ := by
  ext x y; simp [Matrix.map_apply, Matrix.smul_apply]

/-- **The scalar of a product of payments** (*Proof* of Theorem 4.1 of
`CSI12_the_odd_windows.md`): `p • (s • Q(a)⋯Q(a+m−1)) = (s p / p^m) • P(a)⋯P(a+m−1)`. -/
lemma PmQ_smul_prod (φ : A →+* K) (p : ℕ) (hpK : φ (p : A) ≠ 0) (Q : ℕ → Matrix S S A) (s : A)
    (a m : ℕ) :
    φ (p : A) • ((s • ((List.range m).map (fun j => Q (a + j))).prod).map φ) =
      (φ s * φ (p : A) / φ (p : A) ^ m) •
        ((List.range m).map (fun j => PmQ φ p Q (a + j))).prod := by
  unfold PmQ
  rw [list_prod_smul_range, map_smul_matrix, map_list_prod_range, smul_smul, smul_smul]
  congr 1
  have h' := pow_ne_zero m hpK
  field_simp

end Prod

lemma scal_T (x : K) (hx : x ≠ 0) (n m : ℕ) (hnm : m = n + 2) : -(x ^ n) * x / x ^ m = -1 / x := by
  subst hnm; rw [pow_succ, pow_succ]; field_simp

lemma scal_K (x : K) (hx : x ≠ 0) (u : K) (n m : ℕ) (hnm : m = n + 1) :
    u * x ^ n * x / x ^ m = u := by
  subst hnm; rw [pow_succ]; field_simp

variable (φ : A →+* K) (π : ℕ → K) (p : ℕ) (dg : ℕ → ℕ)

/-- **Level 0** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`): the one-slot data
`Q_0(φ) = p^{e−1}(φ + i)` (CSI9's `Q0`) has `P_0(φ) = π_0(φ)`, which is the window form with
`c^{(0)} = [Δ = ∅]`, the label `∅` and the window `[φ, φ + 1)`. -/
theorem base_win [CharZero K] (I : Finset ℕ) (e i : ℕ) (he : 1 ≤ e) :
    WinP φ (fun d => (piW p e i d : K)) p dg (fun Δ => (cW p I dg 0 Δ : K)) 0
      ⟨Unit, Q0 A p e i⟩ (fun _ => ∅) := by
  intro f x y
  rw [PmQ_apply]
  simp only [Q0, empty_subset, if_true, sdiff_self, bot_eq_empty, sum_empty, add_zero, pow_zero,
    one_mul, Nat.Ico_succ_singleton, prod_singleton, cW]
  simp only [Rat.cast_one, one_mul, piW, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_add, map_mul, map_pow, map_natCast, map_add]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

lemma LabP_base : LabP (∅ : Finset ℕ) (fun _ : Unit => (∅ : Finset ℕ)) where
  sub _ := subset_rfl
  inj a b _ := Subsingleton.elim a b
  surj _ hE := ⟨(), (subset_empty.1 hE).symm⟩

variable {p}

lemma o_le_of_lt (hp : 1 ≤ p) {h : ℕ} (hdg : ∀ t < h, dg t < p) {J : Finset ℕ}
    (hJ : ∀ t ∈ J, t < h) : ∑ t ∈ J, dg t * p ^ t ≤ p ^ h := by
  have := oW_lt hp hdg hJ
  unfold oW at this
  omega

/-- **The twist move** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`): for a digit
`d_h = 0` the new payment is `P_{h+1}(f) = a · P_h(pf) ⋯ P_h(pf + p − 1)` (CSI7's `QT`), so the
window form passes to level `h + 1` with the same slots and labels and coefficient
`a (c^{(h)})^{⋆p}`. -/
theorem twist_step (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {D : SData A} {L : D.S → Finset ℕ}
    {J : Finset ℕ} {h : ℕ} {c c' : Finset ℕ → K} (hL : LabP J L) (hJ : ∀ t ∈ J, t < h)
    (hdg : ∀ t < h, dg t < p) (hc' : ∀ Δ ⊆ J, c' Δ = (-1 / (p : K)) * starPow c p Δ)
    (hW : WinP φ π p dg c h D L) :
    WinP φ π p dg c' (h + 1) ⟨D.S, QT p D.Q⟩ L := by
  have hφp : φ (p : A) = (p : K) := map_natCast φ p
  intro f
  have e : PmQ φ p (QT p D.Q) f =
      (-1 / (p : K)) • ((List.range p).map (fun j => PmQ φ p D.Q (p * f + j))).prod := by
    change φ (p : A) • (QT p D.Q f).map φ = _
    unfold QT
    rw [PmQ_smul_prod φ p (by rw [hφp]; exact hpK)]
    congr 1
    rw [hφp]
    simp only [map_neg, map_pow, map_natCast]
    exact scal_T _ hpK _ _ (by omega)
  change WinF _ _ _ _ _ _ (PmQ φ p (QT p D.Q) f)
  rw [e]
  have h1 := WinF_prodList hL (p ^ h) (o_le_of_lt dg (by omega) hdg hJ) (PmQ φ p D.Q) hW p (p * f)
  have h2 := WinF_congr hL.sub (fun Δ hΔ => (hc' Δ hΔ).symm) (WinF_smul (-1 / (p : K)) h1)
  rw [show p ^ (h + 1) * f = p ^ h * (p * f) by ring,
    show p ^ (h + 1) * (f + 1) = p ^ h * (p * f + p) by ring]
  exact h2

/-- The labels after a split at digit `h` (*Setting*, «Slots as subsets», of
`CSI12_the_odd_windows.md`): a bijection onto the subsets of `J ∪ {h}`. -/
theorem split_lab {S : Type*} {L : S → Finset ℕ} {J : Finset ℕ} {h : ℕ} (hL : LabP J L)
    (hJ : ∀ t ∈ J, t < h) :
    LabP (insert h J) (fun y : S × Bool => if y.2 then insert h (L y.1) else L y.1) := by
  have hn : ∀ x, h ∉ L x := fun x hx => lt_irrefl _ (hJ h (hL.sub x hx))
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, _ | _⟩
    · exact (hL.sub x).trans (subset_insert _ _)
    · exact insert_subset_insert _ (hL.sub x)
  · rintro ⟨x, _ | _⟩ ⟨y, _ | _⟩ hxy <;> simp only [Bool.false_eq_true, if_false, if_true] at hxy
    · rw [hL.inj hxy]
    · exact absurd (hxy ▸ mem_insert_self h (L y)) (hn x)
    · exact absurd (hxy ▸ mem_insert_self h (L x)) (hn y)
    · have := congrArg (fun E => E.erase h) hxy
      simp only [erase_insert (hn x), erase_insert (hn y)] at this
      rw [hL.inj this]
  · intro E hE
    by_cases hh : h ∈ E
    · obtain ⟨x, hx⟩ := hL.surj (E.erase h) (by
        intro t ht
        rcases mem_insert.1 (hE (mem_of_mem_erase ht)) with rfl | h2
        · exact absurd ht (notMem_erase _ _)
        · exact h2)
      exact ⟨(x, true), by simp [hx, insert_erase hh]⟩
    · obtain ⟨x, hx⟩ := hL.surj E ((subset_insert_iff_of_notMem hh).1 hE)
      exact ⟨(x, false), by simp [hx]⟩

/-- **The split move** (*Proof* of Theorem 4.1 of `CSI12_the_odd_windows.md`): for a digit
`d_h = r` with `1 ≤ r ≤ p − 1`, CSI8's `QS` on slots `S × Bool`:
* `(A, A)`: `Q_A` gives `a (c^{(h)})^{⋆p}` with `s = p` factors from `pf`;
* `(C, C)`: `Q_C` gives `a (c^{(h)})^{⋆p}` with `s = p` factors from `pf + r` (labels `D ∪ {h}`);
* `(C, A)`: `K` gives `b_h (c^{(h)})^{⋆(p − r)}` with `s = p − r` factors from `pf + r`;
* `(A, C)`: `0`.
So the window form passes to level `h + 1` with the labels of `split_lab`. -/
theorem split_step (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {D : SData A} {L : D.S → Finset ℕ}
    {J : Finset ℕ} {h r : ℕ} (hrp : r < p) (hdh : dg h = r) {c c' : Finset ℕ → K}
    (hL : LabP J L) (hJ : ∀ t ∈ J, t < h) (hdg : ∀ t < h, dg t < p)
    (hcA : ∀ Δ ⊆ J, c' Δ = (-1 / (p : K)) * starPow c p Δ)
    (hcK : ∀ Δ ⊆ J, c' (insert h Δ) = (-1 : K) ^ (p - r + 1) * starPow c (p - r) Δ)
    (hW : WinP φ π p dg c h D L) :
    WinP φ π p dg c' (h + 1) ⟨D.S × Bool, QS p r D.Q⟩
      (fun y => if y.2 then insert h (L y.1) else L y.1) := by
  have hφp : φ (p : A) = (p : K) := map_natCast φ p
  have hpK' : φ (p : A) ≠ 0 := by rw [hφp]; exact hpK
  have hn : ∀ x, h ∉ L x := fun x hx => lt_irrefl _ (hJ h (hL.sub x hx))
  have hoJ := o_le_of_lt dg (by omega) hdg hJ
  have hins : ∀ x, ∑ t ∈ insert h (L x), dg t * p ^ t = r * p ^ h + ∑ t ∈ L x, dg t * p ^ t := by
    intro x; rw [sum_insert (hn x), hdh]
  intro f
  -- the three products
  have eA : φ (p : A) • (QA p D.Q f).map φ =
      (-1 / (p : K)) • ((List.range p).map (fun j => PmQ φ p D.Q (p * f + j))).prod := by
    unfold QA prodQ
    rw [Nat.add_sub_cancel_left, PmQ_smul_prod φ p hpK']
    congr 1
    rw [hφp]
    simp only [map_neg, map_pow, map_natCast]
    exact scal_T _ hpK _ _ (by omega)
  have eC : φ (p : A) • (QC p r D.Q f).map φ =
      (-1 / (p : K)) • ((List.range p).map (fun j => PmQ φ p D.Q (p * f + r + j))).prod := by
    unfold QC prodQ
    rw [Nat.add_sub_cancel_left, PmQ_smul_prod φ p hpK']
    congr 1
    rw [hφp]
    simp only [map_neg, map_pow, map_natCast]
    exact scal_T _ hpK _ _ (by omega)
  have eK : φ (p : A) • (KS p r D.Q f).map φ =
      (-1 : K) ^ (p - r + 1) •
        ((List.range (p - r)).map (fun j => PmQ φ p D.Q (p * f + r + j))).prod := by
    unfold KS prodQ
    rw [show p * f + p - (p * f + r) = p - r by omega, PmQ_smul_prod φ p hpK']
    congr 1
    rw [hφp]
    simp only [map_mul, map_neg, map_pow, map_natCast, map_one]
    exact scal_K _ hpK _ _ _ (by omega)
  have HA := WinF_smul (-1 / (p : K))
    (WinF_prodList hL (p ^ h) hoJ (PmQ φ p D.Q) hW p (p * f))
  have HC := WinF_smul (-1 / (p : K))
    (WinF_prodList hL (p ^ h) hoJ (PmQ φ p D.Q) hW p (p * f + r))
  have HK := WinF_smul ((-1 : K) ^ (p - r + 1))
    (WinF_prodList hL (p ^ h) hoJ (PmQ φ p D.Q) hW (p - r) (p * f + r))
  have w1 : p ^ (h + 1) * f = p ^ h * (p * f) := by ring
  have w2 : p ^ (h + 1) * (f + 1) = p ^ h * (p * f + p) := by ring
  have w3 : p * f + r + (p - r) = p * f + p := by omega
  rintro ⟨x, _ | _⟩ ⟨y, _ | _⟩
  · -- (A, A)
    have : PmQ φ p (QS p r D.Q) f (x, false) (y, false) = (φ (p : A) • (QA p D.Q f).map φ) x y := by
      simp [PmQ, QS, blockS, Matrix.map_apply]
    simp only [Bool.false_eq_true, if_false]
    rw [this, eA, HA x y, w1, w2]
    split_ifs with h1
    · rw [hcA _ (sdiff_subset.trans (hL.sub x))]
    · rfl
  · -- (A, C)
    have : PmQ φ p (QS p r D.Q) f (x, false) (y, true) = 0 := by
      simp [PmQ, QS, blockS, Matrix.map_apply]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [this, if_neg (fun hs => hn x (hs (mem_insert_self _ _)))]
  · -- (C, A)
    have : PmQ φ p (QS p r D.Q) f (x, true) (y, false) = (φ (p : A) • (KS p r D.Q f).map φ) x y := by
      simp [PmQ, QS, blockS, Matrix.map_apply]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [this, eK, HK x y]
    simp only [subset_insert_iff_of_notMem (hn y), insert_sdiff_of_notMem _ (hn y)]
    rw [hins x, w3, w1, w2]
    split_ifs with h1
    · rw [hcK _ (sdiff_subset.trans (hL.sub x)),
        show p ^ h * (p * f) + (r * p ^ h + ∑ t ∈ L x, dg t * p ^ t) =
          p ^ h * (p * f + r) + ∑ t ∈ L x, dg t * p ^ t by ring]
    · rfl
  · -- (C, C)
    have : PmQ φ p (QS p r D.Q) f (x, true) (y, true) = (φ (p : A) • (QC p r D.Q f).map φ) x y := by
      simp [PmQ, QS, blockS, Matrix.map_apply]
    simp only [if_true]
    rw [this, eC, HC x y]
    simp only [insert_subset_insert_iff (hn y), insert_sdiff_insert,
      sdiff_insert_of_notMem (hn x)]
    rw [hins x, hins y, w1, w2]
    split_ifs with h1
    · rw [hcA _ (sdiff_subset.trans (hL.sub x)),
        show p ^ h * (p * f) + (r * p ^ h + ∑ t ∈ L x, dg t * p ^ t) =
          p ^ h * (p * f + r) + ∑ t ∈ L x, dg t * p ^ t by ring,
        show p ^ h * (p * f + p) + (r * p ^ h + ∑ t ∈ L y, dg t * p ^ t) =
          p ^ h * (p * f + r + p) + ∑ t ∈ L y, dg t * p ^ t by ring]
    · rfl

end ColouredSand.OddTwist
