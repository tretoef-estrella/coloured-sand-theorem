module

public import RequestProject.OddSplitMove.Basic
public import RequestProject.OddLevels.Basic

/-!
# `CSI10_theorem_Dp_and_theorem_I.md`, Setting and Part M — the halved data `Q_t` and the matrix `Mp`

Namespace `ColouredSand.OddTwist`. Reuses CSI7's twisted data `QT` (`RequestProject/OddPayment/`),
CSI8's split data `QS` and `prodQ` (`RequestProject/OddSplitMove/`) and CSI9's one-slot data `Q0`
(`RequestProject/OddLevels/`).

## Encodings

* **Digits.** As in CSI6 (`card_danceL_digits`), the base-`p` expansion of `λ + 1` is Mathlib's
  `Nat.digits p (λ + 1)` (least significant digit first). `digitL p λ t = d_t` is its `t`-th entry
  (`0` past the end), `kTop p λ = k` is its length minus one (so `d_k ≠ 0` is the leading digit), and
  `Iset p λ = I = {t < k : d_t ≠ 0}`.
* **Slot types with data.** A slot type together with halved data is a value of the structure
  `SData A`: a type `S : Type` with `Fintype` and `DecidableEq` instances and data
  `Q : ℕ → Matrix S S A`. The slot types are **iterated products**: one move with digit `d` is
  `stepD p d`, which sends `(S, Q)` to `(S, QT p Q)` if `d = 0` (CSI7) and to
  `(S × Bool, QS p d Q)` if `d ≠ 0` (CSI8; `false` is the `A` block, `true` the `C` block).
* **Part M.** `iterD p dg t D` applies the moves of the digits `dg 0, …, dg (t−1)` to `D`, by
  recursion on `t` (`iterD p dg (t+1) D = stepD p (dg t) (iterD p dg t D)`).
  `Qdata p λ i e t = (S_t, Q_t)` is `iterD p (digitL p λ) t (Unit, Q_0)` with
  `Q_0 φ = p^{e−1}(φ + i)` (CSI9's `Q0`), so `S_0 = Unit` and `S_{t+1}` is `S_t` or `S_t × Bool`.
  `Mp p λ i e = p^{d_k} • (Q_k 0 * ⋯ * Q_k (d_k − 1)) = p^{d_k} • prodQ Q_k 0 d_k`, a square matrix over
  `slots p λ i e = S_k`, whose cardinality is `2^{|I|}` (`card_slots`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

/-- A slot type with halved data (Part M of `CSI10_theorem_Dp_and_theorem_I.md`): a finite type
`S` with decidable equality and data `Q : ℕ → Matrix S S A`. -/
structure SData (A : Type*) [CommRing A] where
  /-- the slot type -/
  S : Type
  [fin : Fintype S]
  [dec : DecidableEq S]
  /-- the halved data -/
  Q : ℕ → Matrix S S A

attribute [instance] SData.fin SData.dec

variable {A : Type*} [CommRing A]

/-- The move of one digit on the data (Part M of `CSI10_theorem_Dp_and_theorem_I.md`):
`Q ↦ QT p Q` (CSI7, same slots) if `d = 0`, `Q ↦ QS p d Q` (CSI8, slots `S × Bool`) if `d ≠ 0`. -/
def stepD (p d : ℕ) (D : SData A) : SData A :=
  if d = 0 then ⟨D.S, QT p D.Q⟩ else ⟨D.S × Bool, QS p d D.Q⟩

lemma stepD_zero (p : ℕ) (D : SData A) : stepD p 0 D = ⟨D.S, QT p D.Q⟩ := by
  simp [stepD]

lemma stepD_pos (p d : ℕ) (hd : d ≠ 0) (D : SData A) :
    stepD p d D = ⟨D.S × Bool, QS p d D.Q⟩ := by
  simp [stepD, hd]

/-- The moves of the digits `dg 0, …, dg (t−1)`, by recursion on `t` (Part M of
`CSI10_theorem_Dp_and_theorem_I.md`): `iterD p dg (t+1) D = stepD p (dg t) (iterD p dg t D)`. -/
def iterD (p : ℕ) (dg : ℕ → ℕ) : ℕ → SData A → SData A
  | 0, D => D
  | t + 1, D => stepD p (dg t) (iterD p dg t D)

lemma iterD_zero (p : ℕ) (dg : ℕ → ℕ) (D : SData A) : iterD p dg 0 D = D := rfl

lemma iterD_succ (p : ℕ) (dg : ℕ → ℕ) (t : ℕ) (D : SData A) :
    iterD p dg (t + 1) D = stepD p (dg t) (iterD p dg t D) := rfl

/-- Peeling off the first digit: `iterD p dg (t+1) D = iterD p (dg ∘ succ) t (stepD p (dg 0) D)`. -/
lemma iterD_succ' (p : ℕ) (dg : ℕ → ℕ) (t : ℕ) (D : SData A) :
    iterD p dg (t + 1) D = iterD p (fun s => dg (s + 1)) t (stepD p (dg 0) D) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterD_succ, ih, iterD_succ]

/-- The number of slots after the moves: `|S_t| = |S_0| · 2^{#{s < t : dg s ≠ 0}}`. -/
lemma card_iterD (p : ℕ) (dg : ℕ → ℕ) (t : ℕ) (D : SData A) :
    Fintype.card (iterD p dg t D).S =
      Fintype.card D.S * 2 ^ ((Finset.range t).filter (fun s => dg s ≠ 0)).card := by
  induction t with
  | zero => simp [iterD_zero]
  | succ t ih =>
    rw [iterD_succ, Finset.range_add_one, Finset.filter_insert]
    by_cases h : dg t = 0
    · rw [h, stepD_zero]
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ih
    · rw [stepD_pos p _ h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      change Fintype.card ((iterD p dg t D).S × Bool) = _
      rw [Fintype.card_prod, ih, Fintype.card_bool, pow_succ, mul_assoc]

/-! ### The digits of `λ + 1` -/

/-- The digit `d_t` of `λ + 1` in base `p` (Setting of `CSI10_theorem_Dp_and_theorem_I.md`). -/
def digitL (p l t : ℕ) : ℕ := (Nat.digits p (l + 1)).getD t 0

/-- The index `k` of the leading digit of `λ + 1` in base `p` (Setting of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
def kTop (p l : ℕ) : ℕ := (Nat.digits p (l + 1)).length - 1

/-- `I = {t < k : d_t ≠ 0}` (Setting of `CSI10_theorem_Dp_and_theorem_I.md`). -/
def Iset (p l : ℕ) : Finset ℕ := (Finset.range (kTop p l)).filter (fun t => digitL p l t ≠ 0)

/-! ### Part M -/

variable (p : ℕ) [Fact p.Prime]

/-- **The halved data** `(S_t, Q_t)` (Part M of `CSI10_theorem_Dp_and_theorem_I.md`):
`S_0 = Unit`, `Q_0 φ = p^{e−1}(φ + i)`, and `Q_{t+1} = QT p Q_t` if `d_t = 0`,
`Q_{t+1} = QS p d_t Q_t` (slots `S_t × Bool`) if `d_t ≠ 0`. -/
def Qdata (l i e t : ℕ) : SData ℤ_[p] :=
  iterD p (digitL p l) t ⟨Unit, Q0 ℤ_[p] p e i⟩

/-- The slot type of `Mp`: `S_k` (Part M of `CSI10_theorem_Dp_and_theorem_I.md`). -/
abbrev slots (l i e : ℕ) : Type := (Qdata p l i e (kTop p l)).S

/-- **The matrix** `Mp p λ i e = p^{d_k} • (Q_k 0 * Q_k 1 * ⋯ * Q_k (d_k − 1))` (Part M of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
def Mp (l i e : ℕ) : Matrix (slots p l i e) (slots p l i e) ℤ_[p] :=
  (p : ℤ_[p]) ^ digitL p l (kTop p l) • prodQ (Qdata p l i e (kTop p l)).Q 0 (digitL p l (kTop p l))

/-- Part M of `CSI10_theorem_Dp_and_theorem_I.md`: `Mp` is a square matrix over a slot type of
cardinality `2^{|I|}`. -/
theorem card_slots (l i e : ℕ) : Fintype.card (slots p l i e) = 2 ^ (Iset p l).card := by
  change Fintype.card (iterD p (digitL p l) (kTop p l) ⟨Unit, Q0 ℤ_[p] p e i⟩).S = _
  rw [card_iterD]
  simp [Iset]

/-- **(M1)** (Part M of `CSI10_theorem_Dp_and_theorem_I.md`): every entry of `Mp p λ i e` lies in
`p^{d_k} ℤ_[p]`. -/
theorem M1 (l i e : ℕ) (s s' : slots p l i e) :
    Mp p l i e s s' ∈ Ideal.span {(p : ℤ_[p]) ^ digitL p l (kTop p l)} := by
  rw [Mp, Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end ColouredSand.OddTwist
