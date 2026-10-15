module

public import RequestProject.OddWindows.Rescaling

/-!
# `CSI12_the_odd_windows.md` — **Theorem 4.1** for CSI10's data `Q_t` and matrix `Mp`

Namespace `ColouredSand.OddTwist`.  Here `p` is a prime (`[Fact p.Prime]`; oddness is not used),
the digits are those of `λ + 1` (`d_t = digitL p λ t`, `k = kTop p λ`, `I = Iset p λ`), the data
are CSI10's `Qdata p λ i e h = (S_h, Q_h)` and the payment is `P_h(f) = p • Q_h(f)`.  Entries of
matrices over `ℤ_[p]` are compared in `ℚ_[p]` (coercion `ℤ_[p] → ℚ_[p]`), the right-hand sides
being rationals cast to `ℚ_[p]`.

* `labL p λ i e h : (Qdata p λ i e h).S → Finset ℕ` is the subset `D ⊆ I ∩ [0, h)` of a slot
  (CSI12's «slots as subsets», the labels `slotLab` of `Basic.lean`: digit `t` is in `D` iff the
  slot took the `C` side (`true`) at the split of digit `t`).
* `slots_as_subsets`: `labL` is a bijection onto the subsets of `I ∩ [0, h)` (`h ≤ k`).
* `W1_windows`: **(W1) Theorem 4.1**.
* `W2_Mp`: **(W2)** the final matrix `Mp`.
* `C1_lambda`: **(C1)** with CSI10's digits and CSI11's `aP p (dsL p λ)`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

/-! ### Part C with CSI10's digits -/

/-- `c^{(h)}` only depends on `I` and on the digits `d_t` with `t ∈ I`. -/
lemma cW_congr (p : ℕ) (I : Finset ℕ) {dg dg' : ℕ → ℕ} (hdg : ∀ t ∈ I, dg t = dg' t) (h : ℕ) :
    cW p I dg h = cW p I dg' h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    funext Δ
    simp only [cW, ih]
    by_cases hh : h ∈ I
    · rw [bW, bW, hdg h hh]
    · simp [hh]

/-- With CSI10's digits of `λ + 1`, `c^{(h)}` is the same as with CSI11's list `dsL p λ`
(*Part C* of `CSI12_the_odd_windows.md`). -/
lemma cW_lambda (p l h : ℕ) :
    cW p (Iset p l) (digitL p l) h = cW p (Iod (dsL p l)) (fun t => (dsL p l).getD t 0) h := by
  rw [Iod_lambda]
  apply cW_congr
  intro t ht
  have : t < kTop p l := by simp [Iset] at ht; exact ht.1
  rw [getD_dsL p l t this]

lemma digitL_lt {p : ℕ} (hp : p.Prime) (l t : ℕ) : digitL p l t < p := by
  unfold digitL
  by_cases ht : t < (Nat.digits p (l + 1)).length
  · rw [List.getD_eq_getElem _ _ ht]
    exact Nat.digits_lt_base hp.one_lt (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hp.pos

lemma digitL_top_ne_zero' (p l : ℕ) : digitL p l (kTop p l) ≠ 0 := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · simp [digitL, kTop]
    · simp [digitL, kTop]
  have hne : Nat.digits p (l + 1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hlen : kTop p l < (Nat.digits p (l + 1)).length := by
    unfold kTop; have := List.length_pos_of_ne_nil hne; omega
  have htop : digitL p l (kTop p l) = (Nat.digits p (l + 1)).getLast hne := by
    unfold digitL
    rw [List.getD_eq_getElem _ _ hlen, List.getLast_eq_getElem]
    rfl
  rw [htop]; exact Nat.getLast_digit_ne_zero p (by omega)

lemma mem_Iset_iff (p l t : ℕ) (ht : t < kTop p l) : t ∈ Iset p l ↔ digitL p l t ≠ 0 := by
  simp [Iset, ht]

/-- **(C1) Rescaling** with CSI10's digits of `λ + 1` (*Part C* of `CSI12_the_odd_windows.md`):
`c^{(h)}(Δ) = a^{(p^h−1)/(p−1)} · aP h Δ · ∏_{t ∈ Δ} (−b_t (−p)^{1 + d_t (p^t − 1)/(p−1)})`,
with `c^{(h)} = cW p (Iset p λ) (digitL p λ) h`, `d_t = digitL p λ t` and CSI11's
`aP p (dsL p λ) h`, `dsL p λ = (Nat.digits p (λ+1)).take k`. -/
theorem C1_lambda {p : ℕ} (hp : p.Prime) (l h : ℕ) (Δ : Finset ℕ) :
    cW p (Iset p l) (digitL p l) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p (dsL p l) h Δ : ℚ) *
        ∏ t ∈ Δ, (-(bW p (digitL p l) t) *
          (-(p : ℚ)) ^ (1 + digitL p l t * ((p ^ t - 1) / (p - 1)))) := by
  have hds : ∀ d ∈ dsL p l, d < p := fun d hd =>
    Nat.digits_lt_base hp.one_lt (List.mem_of_mem_take hd)
  rw [cW_lambda, C1_rescaling hp.two_le _ hds]
  by_cases hz : aP p (dsL p l) h Δ = 0
  · simp [hz]
  · have hsub := Q1_support p (dsL p l) h Δ hz
    congr 1
    apply prod_congr rfl
    intro t ht
    have h1 : t < kTop p l := by
      have := hsub ht
      rw [mem_filter, Iod_lambda] at this
      simp [Iset] at this
      exact this.1.1
    simp only [bW, getD_dsL p l t h1]

/-! ### Part W for `Qdata` and `Mp` -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Slots as subsets** (*Setting* of `CSI12_the_odd_windows.md`): the subset `D ⊆ I ∩ [0, h)`
attached to a slot of CSI10's `Qdata p λ i e h` (an iterated product `Unit × Bool × ⋯`): digit
`t` is in `D` iff the slot took the `C` side (`true`) at the split of digit `t`. -/
def labL (l i e h : ℕ) : (Qdata p l i e h).S → Finset ℕ :=
  slotLab p (digitL p l) ⟨Unit, Q0 ℤ_[p] p e i⟩ h

/-- **Slots as subsets** (*Setting* of `CSI12_the_odd_windows.md`): for `h ≤ k`, `labL` is a
bijection from the slots of `Qdata p λ i e h` onto the subsets of `I ∩ [0, h)`. -/
theorem slots_as_subsets (l i e h : ℕ) (hh : h ≤ kTop p l) :
    LabP ((Iset p l).filter (· < h)) (labL p l i e h) :=
  labels_gen p (digitL p l) (Iset p l) (Q0 ℤ_[p] p e i) h
    (fun t ht => mem_Iset_iff p l t (by omega))

/-- **(W1) Theorem 4.1** (*Part W* of `CSI12_the_odd_windows.md`): for `0 ≤ h ≤ k`, every floor
`f` and slots `x, y` of `Qdata p λ i e h` with subsets `D = labL x`, `D' = labL y`,
`P_h(f)_{D D'} = c^{(h)}(D ∖ D') · ∏_{d ∈ [p^h f + o_D, p^h f + o_{D'} + p^h − 1]} π_0(d)` if
`D' ⊆ D`, and `0` otherwise; here `P_h(f) = p • Q_h(f)` (row = generator slot `x`, column =
relation slot `y`), `o_D = Σ_{t∈D} d_t p^t`, `π_0(d) = p^e (i + d)`, equality in `ℚ_[p]`. -/
theorem W1_windows (l i e h : ℕ) (he : 1 ≤ e) (hh : h ≤ kTop p l) (f : ℕ)
    (x y : (Qdata p l i e h).S) :
    (((p : ℤ_[p]) • (Qdata p l i e h).Q f) x y : ℚ_[p]) =
      ((if labL p l i e h y ⊆ labL p l i e h x then
          cW p (Iset p l) (digitL p l) h (labL p l i e h x \ labL p l i e h y) *
            ∏ d ∈ Icc (p ^ h * f + oW p (digitL p l) (labL p l i e h x))
              (p ^ h * f + oW p (digitL p l) (labL p l i e h y) + p ^ h - 1), piW p e i d
        else 0 : ℚ) : ℚ_[p]) :=
  W1_gen PadicInt.Coe.ringHom p (digitL p l) (Iset p l) e i hp.out.two_le he h
    (fun t _ => digitL_lt hp.out l t) (fun t ht => mem_Iset_iff p l t (by omega)) f x y

/-- **(W2) The final matrix** (*Part W* of `CSI12_the_odd_windows.md`): for slots `x, y` of
`slots p λ i e` with subsets `D = labL x`, `D' = labL y`,
`Mp_{D D'} = [(c^{(k)})^{⋆ d_k}](D ∖ D') · ∏_{d = o_D}^{o_{D'} + K − 1} π_0(d)` for `D' ⊆ D`,
and `0` otherwise, with `K = d_k p^k`; here CSI10's `Mp = P_k(0) ⋯ P_k(d_k − 1)`
(`= p^{d_k} • Q_k(0) ⋯ Q_k(d_k − 1)`), equality in `ℚ_[p]`. -/
theorem W2_Mp (l i e : ℕ) (he : 1 ≤ e) (x y : slots p l i e) :
    (Mp p l i e x y : ℚ_[p]) =
      ((if labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x then
          starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l))
              (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y) *
            ∏ d ∈ Icc (oW p (digitL p l) (labL p l i e (kTop p l) x))
              (oW p (digitL p l) (labL p l i e (kTop p l) y) +
                digitL p l (kTop p l) * p ^ kTop p l - 1), piW p e i d
        else 0 : ℚ) : ℚ_[p]) :=
  W2_gen PadicInt.Coe.ringHom p (digitL p l) (Iset p l) e i hp.out.two_le he (kTop p l)
    (fun t _ => digitL_lt hp.out l t) (fun t ht => mem_Iset_iff p l t ht)
    (digitL p l (kTop p l)) (Nat.one_le_iff_ne_zero.2 (digitL_top_ne_zero' p l)) x y

end ColouredSand.OddTwist
