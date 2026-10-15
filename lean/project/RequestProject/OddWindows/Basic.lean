module

public import RequestProject.OddTheoremI.Basic
public import RequestProject.OddDeficit.Lambda

/-!
# `CSI12_the_odd_windows.md` — *Setting*, the slot labels and **Part C** (definitions)

Namespace `ColouredSand.OddTwist`.  This is the `p`-odd analogue of C14 (`RequestProject/Windows/`).
It reuses, unchanged, CSI10's `SData`, `stepD`, `iterD`, `digitL`, `kTop`, `Iset`, `Qdata`,
`slots`, `Mp` (`RequestProject/OddTheoremI/`), CSI7's `QT`, CSI8's `prodQ`, `QA`, `QC`, `KS`,
`blockS`, `QS`, CSI9's `Q0`, and CSI11's `starPow`, `Iod`, `aP`, `dsL` (`RequestProject/OddDeficit/`).

## Encodings

* **Digits.** The theorems are proved for an abstract digit function `dg : ℕ → ℕ` (`d_t = dg t`)
  and an abstract set `I : Finset ℕ`, under the hypotheses `dg t < p` and `t ∈ I ↔ dg t ≠ 0`
  for the digits that are used.  They are then specialised to CSI10's digits of `λ + 1`
  (`dg = digitL p λ`, `I = Iset p λ`, `k = kTop p λ`).  For the rescaling (C1) the digits are
  CSI11's list `ds` (`d_t = ds.getD t 0`, `I = Iod ds`).
* **`o_D = Σ_{t ∈ D} d_t p^t`** is `oW p dg D : ℕ`; **`π_0(d) = p^e (i + d)`** is
  `piW p e i d : ℚ`.
* **Coefficient functions** (elements of `ℚ[x_t]/(x_t²)`) are functions `Finset ℕ → ℚ` (value at
  `Δ` = coefficient of `x^Δ`), multiplied with C10's `Deficit.starMul`; powers are CSI11's
  `starPow`.  `x_h · f` is `xMul h f : Δ ↦ [h ∈ Δ] f(Δ ∖ {h})`.
* **Part C.** `cW p I dg h` is `c^{(h)}`: `cW 0 = [Δ = ∅]`,
  `cW (h+1) = (−1/p)·(cW h)^{⋆p} + [h ∈ I]·b_h·x_h·(cW h)^{⋆(p − d_h)}`, with
  `b_h = bW p dg h = (−1)^{p − d_h + 1}`.
* **Slots as subsets.** CSI10's slot types are iterated products: one move with a digit `d ≠ 0`
  replaces `S` by `S × Bool` (`false` = `A` side, `true` = `C` side), a move with `d = 0` keeps
  `S`.  The label of a slot is `slotLab p dg D₀ h : (iterD p dg h D₀).S → Finset ℕ`, defined by
  recursion on `h`: the label of the initial slot is `∅`; a move with digit `0` keeps the label
  (`slotLab_succ_zero`); a move at a digit `d_h ≠ 0` sends the slot `(s, false)` to the label of
  `s` and the slot `(s, true)` to the label of `s` with `h` added (`slotLab_succ_pos`).  So digit
  `t` is in the label iff the slot took the `C` side at the split of digit `t`.  The identification
  of `(stepD p d D).S` with `D.S` (for `d = 0`) or `D.S × Bool` (for `d ≠ 0`) is the `cast` along
  CSI10's `stepD_zero`/`stepD_pos`.  `LabP J L` says that `L` is a bijection from the slots onto
  the subsets of `J` (`∀ x, L x ⊆ J`, `L` injective, every `E ⊆ J` is a label).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

/-- `o_D := Σ_{t ∈ D} d_t p^t` (*Setting* of `CSI12_the_odd_windows.md`), for a digit function
`dg` (`d_t = dg t`). -/
def oW (p : ℕ) (dg : ℕ → ℕ) (D : Finset ℕ) : ℕ := ∑ t ∈ D, dg t * p ^ t

/-- The odd `π_0(d) := p^e (i + d)` in `ℚ` (*Setting* of `CSI12_the_odd_windows.md`). -/
def piW (p e i : ℕ) (d : ℕ) : ℚ := (p : ℚ) ^ e * ((i : ℚ) + d)

/-- `b_h := (−1)^{p − d_h + 1}` (*Part C* of `CSI12_the_odd_windows.md`). -/
def bW (p : ℕ) (dg : ℕ → ℕ) (h : ℕ) : ℚ := (-1) ^ (p - dg h + 1)

/-- `x_h · f`, the function `Δ ↦ [h ∈ Δ] f(Δ ∖ {h})` (*Part C* of `CSI12_the_odd_windows.md`). -/
def xMul (h : ℕ) (f : Finset ℕ → ℚ) (Δ : Finset ℕ) : ℚ := if h ∈ Δ then f (Δ \ {h}) else 0

/-- **The coefficients** `c^{(h)} : Finset ℕ → ℚ` (*Part C* of `CSI12_the_odd_windows.md`):
`c^{(0)} = [Δ = ∅]`, `c^{(h+1)} = a·(c^{(h)})^{⋆p} + [h ∈ I]·b_h·x_h·(c^{(h)})^{⋆(p − d_h)}` with
`a = −1/p`, `b_h = (−1)^{p − d_h + 1}`. -/
def cW (p : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) : ℕ → Finset ℕ → ℚ
  | 0, Δ => if Δ = ∅ then 1 else 0
  | h + 1, Δ => (-1 / (p : ℚ)) * starPow (cW p I dg h) p Δ +
      (if h ∈ I then 1 else 0) * bW p dg h * xMul h (starPow (cW p I dg h) (p - dg h)) Δ

/-- `L` is a bijection from the slots onto the subsets of `J` (*Setting*, «Slots as subsets», of
`CSI12_the_odd_windows.md`). -/
structure LabP {S : Type*} (J : Finset ℕ) (L : S → Finset ℕ) : Prop where
  sub : ∀ x, L x ⊆ J
  inj : Function.Injective L
  surj : ∀ E ⊆ J, ∃ x, L x = E

variable {A : Type*} [CommRing A]

lemma stepD_zero_of (p d : ℕ) (hd : d = 0) (D : SData A) : stepD p d D = ⟨D.S, QT p D.Q⟩ := by
  subst hd; exact stepD_zero p D

/-- `(stepD p d D).S = D.S` for `d = 0` (CSI10's `stepD_zero`). -/
lemma stepD_S_zero (p d : ℕ) (hd : d = 0) (D : SData A) : (stepD p d D).S = D.S := by
  rw [stepD_zero_of p d hd D]

/-- `(stepD p d D).S = D.S × Bool` for `d ≠ 0` (CSI10's `stepD_pos`). -/
lemma stepD_S_pos (p d : ℕ) (hd : d ≠ 0) (D : SData A) : (stepD p d D).S = (D.S × Bool) := by
  rw [stepD_pos p d hd D]

/-- The labels after one move (*Setting*, «Slots as subsets», of `CSI12_the_odd_windows.md`):
for `d = 0` the label is kept; for `d ≠ 0` the slot `(s, false)` (the `A` side) keeps the label of
`s` and the slot `(s, true)` (the `C` side) gets the label of `s` with `h` added. -/
def labStep (p d h : ℕ) (D : SData A) (L : D.S → Finset ℕ) : (stepD p d D).S → Finset ℕ :=
  if hd : d = 0 then fun x => L (cast (stepD_S_zero p d hd D) x)
  else fun x => (fun y : D.S × Bool => if y.2 then insert h (L y.1) else L y.1)
    (cast (stepD_S_pos p d hd D) x)

/-- **The slot labels** (*Setting*, «Slots as subsets», of `CSI12_the_odd_windows.md`): the subset
`D ⊆ I ∩ [0, h)` attached to a slot of `iterD p dg h D₀` (initial label `∅`). -/
def slotLab (p : ℕ) (dg : ℕ → ℕ) (D₀ : SData A) : (h : ℕ) → (iterD p dg h D₀).S → Finset ℕ
  | 0 => fun _ => ∅
  | h + 1 => labStep p (dg h) h (iterD p dg h D₀) (slotLab p dg D₀ h)

/-- The label of a slot after a move with digit `d_h = 0` is the label before the move
(*Setting*, «Slots as subsets», of `CSI12_the_odd_windows.md`). -/
lemma slotLab_succ_zero (p : ℕ) (dg : ℕ → ℕ) (D₀ : SData A) (h : ℕ) (hd : dg h = 0)
    (x : (iterD p dg (h + 1) D₀).S) :
    slotLab p dg D₀ (h + 1) x =
      slotLab p dg D₀ h (cast (stepD_S_zero p _ hd (iterD p dg h D₀)) x) := by
  change labStep p (dg h) h (iterD p dg h D₀) (slotLab p dg D₀ h) x = _
  rw [labStep, dif_pos hd]

/-- The label of a slot after the split at a digit `d_h ≠ 0` (*Setting*, «Slots as subsets», of
`CSI12_the_odd_windows.md`): with `(s, b)` the slot read in `S_h × Bool`, the label is that of
`s`, with `h` added iff `b = true` (the `C` side). -/
lemma slotLab_succ_pos (p : ℕ) (dg : ℕ → ℕ) (D₀ : SData A) (h : ℕ) (hd : dg h ≠ 0)
    (x : (iterD p dg (h + 1) D₀).S) :
    slotLab p dg D₀ (h + 1) x =
      (if (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).2 then
        insert h (slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1)
      else slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1) := by
  change labStep p (dg h) h (iterD p dg h D₀) (slotLab p dg D₀ h) x = _
  rw [labStep, dif_neg hd]

end ColouredSand.OddTwist
