module

public import RequestProject.OddPayment.Basic

/-!
# The *Setting* and *Part S* of `CSI8_the_split_move.md`

Namespace `ColouredSand.OddTwist`. The setting is CSI7's (`RequestProject/OddPayment/`), reused
without modification: `A` a commutative ring, `p : ℕ` used as `(p : A)`, a graded family
`(ι, fl, N, F)` (`fl : ι → ℕ`, modules `N i`, `F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)`), a finite slot
type `S` (`[Fintype S] [DecidableEq S]`, no order), data `Q : ℕ → Matrix S S A`, the module of a
system C11's `Payment.Sys N S = ⨁ q : S × ι, N q.2` (`= M^S`) and CSI7's system `Gp p fl F Q`
(with `p` as explicit first argument).

## Encoding of Part S (the split of a graded family, digit `r`, `u = −1`)

* Index type `ι × Bool × Fin p` (i.e. `ι × (Bool × Fin p)`); `false` is the paper's `A`, `true`
  is the paper's `C`; the element `x : N i` at `(i, false, j)` is `A_j x`, at `(i, true, j)` it is
  `C_j x`.
* Module `NS p N (i, b, j) = N i`.
* Floor `flS p r fl (i, b, j) = p * fl i + (if b then r else 0) + j` (written with `cond`), i.e.
  `flS (i, A, j) = p·fl i + j` and `flS (i, C, j) = p·fl i + r + j`.
* `embS A N p b j : M →ₗ[A] ⨁ q, NS p N q` places `x` at `i` as `x` at `(i, b, j)` (so
  `embS false j = A_j`, `embS true j = C_j`).
* The operator `FS p r hr F` (`hr : 0 < r` is needed to make `C_{p−r}` a valid index) is defined
  on generators (`DirectSum.toModule`):
  `A_j x ↦ A_{j+1} x`, `C_j x ↦ C_{j+1} x` for `j + 1 < p`;
  `A_{p−1} x ↦ −p · A_0(F x) + p · C_{p−r} x`; `C_{p−1} x ↦ −p · C_0(F x)`.
* `prodQ Q a b = Π(a, b) = Q a * Q (a+1) * ⋯ * Q (b−1)` (empty product `= 1`), written
  `((List.range (b − a)).map (fun j => Q (a + j))).prod`.
* The new data on slots `S × Bool` (`false` = `A` slots, `true` = `C` slots; rows = generator
  slot, columns = relation slot): `QA`, `QC`, `KS` (the file's `K`, renamed to avoid a
  single-letter name) exactly as in the file, and `QS p r Q = blockS (QA ..) (QC ..) (KS ..)`,
  where `blockS a c k f (s, b) (s', b')` is `a f s s'` for `(A, A)`, `c f s s'` for `(C, C)`,
  `k f s s'` for row `(s, C)`, column `(s', A)`, and `0` for row `(s, A)`, column `(s', C)`.
* Sign convention (step 3 of the *Proof* of (M1)): the file's `QS` is used for odd `p`; the variant
  `QSsign` has the diagonal blocks `QAsign`, `QCsign` with `(−1)^p · p^(p−2)` in place of `−p^(p−2)`
  (as CSI7's `QTsign`), the coupling `KS` unchanged; it works for every `p ≥ 1`, and
  `QSsign = QS` for odd `p` (`QSsign_of_odd`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum

/-- The modules of the split: `NS p N (i, b, j) = N i` (`x` at `(i, false, j)` is `A_j x`, at
`(i, true, j)` it is `C_j x`) (*Part S* of `CSI8_the_split_move.md`). -/
abbrev NS (p : ℕ) {ι : Type*} (N : ι → Type*) (q : ι × Bool × Fin p) : Type _ := N q.1

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*}

variable (p r : ℕ)

/-- The floor of the split: `flS (i, A, j) = p·fl i + j` and `flS (i, C, j) = p·fl i + r + j`
(*Part S* of `CSI8_the_split_move.md`). -/
def flS (fl : ι → ℕ) (q : ι × Bool × Fin p) : ℕ := p * fl q.1 + cond q.2.1 r 0 + q.2.2.val

variable (A N) in
/-- `A_j` (`b = false`) and `C_j` (`b = true`) as maps `M → ⨁ q, NS p N q`, placing `x` at `i` as
`x` at `(i, b, j)` (*Part S* of `CSI8_the_split_move.md`). -/
def embS (b : Bool) (j : Fin p) : (⨁ i, N i) →ₗ[A] (⨁ q, NS p N q) :=
  DirectSum.toModule A ι _ (fun i => DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, j))

/-- **The operator of the split** (*Part S* of `CSI8_the_split_move.md`; digit `r`, `u = −1`):
`A_j x ↦ A_{j+1} x` and `C_j x ↦ C_{j+1} x` for `j ≤ p − 2`,
`A_{p−1} x ↦ −p·A_0(F x) + p·C_{p−r} x`, `C_{p−1} x ↦ −p·C_0(F x)`.
The hypothesis `hr : 0 < r` makes `p − r` an element of `Fin p`. -/
def FS (hr : 0 < r) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) :
    (⨁ q, NS p N q) →ₗ[A] (⨁ q, NS p N q) :=
  DirectSum.toModule A (ι × Bool × Fin p) _ (fun q =>
    if h : q.2.2.val + 1 < p then
      DirectSum.lof A (ι × Bool × Fin p) (NS p N) (q.1, q.2.1, ⟨q.2.2.val + 1, h⟩)
    else cond q.2.1
      (-(p : A) • (embS A N p true ⟨0, q.2.2.pos⟩ ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1))
      (-(p : A) • (embS A N p false ⟨0, q.2.2.pos⟩ ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1) +
        (p : A) • DirectSum.lof A (ι × Bool × Fin p) (NS p N)
          (q.1, true, ⟨p - r, Nat.sub_lt q.2.2.pos hr⟩)))

variable [Fintype S] [DecidableEq S]

/-- `Π(a, b) = Q(a)·Q(a+1)⋯Q(b−1)` (empty product `= 1`) (*Part S* of
`CSI8_the_split_move.md`). -/
def prodQ (Q : ℕ → Matrix S S A) (a b : ℕ) : Matrix S S A :=
  ((List.range (b - a)).map (fun j => Q (a + j))).prod

/-- `QA f = −p^{p−2} • Π(pf, pf + p)` (*Part S* of `CSI8_the_split_move.md`). -/
def QA (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  -(p : A) ^ (p - 2) • prodQ Q (p * f) (p * f + p)

/-- `QC f = −p^{p−2} • Π(pf + r, pf + r + p)` (*Part S* of `CSI8_the_split_move.md`). -/
def QC (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  -(p : A) ^ (p - 2) • prodQ Q (p * f + r) (p * f + r + p)

/-- The file's `K f = (−1)^{p−r+1} p^{p−r−1} • Π(pf + r, pf + p)` (*Part S* of
`CSI8_the_split_move.md`). -/
def KS (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  ((-1 : A) ^ (p - r + 1) * (p : A) ^ (p - r - 1)) • prodQ Q (p * f + r) (p * f + p)

/-- Assembling blocks on slots `S × Bool` (`false` = `A`, `true` = `C`; rows = generator slot,
columns = relation slot): `[[a f, 0], [k f, c f]]`, i.e. the entry at row `(s, C)`, column
`(s', A)` is `k f s s'` and the entry at row `(s, A)`, column `(s', C)` is `0` (*Part S* of
`CSI8_the_split_move.md`). -/
def blockS (a c k : ℕ → Matrix S S A) (f : ℕ) : Matrix (S × Bool) (S × Bool) A :=
  fun x y => match x.2, y.2 with
    | false, false => a f x.1 y.1
    | true, true => c f x.1 y.1
    | true, false => k f x.1 y.1
    | false, true => 0

/-- **The new data** `QS f = [[QA f, 0], [K f, QC f]]` on slots `S × Bool` (*Part S* of
`CSI8_the_split_move.md`). -/
def QS (Q : ℕ → Matrix S S A) : ℕ → Matrix (S × Bool) (S × Bool) A :=
  blockS (QA p Q) (QC p r Q) (KS p r Q)

/-- `QA` with the sign `(−1)^p` built in: `((−1)^p p^{p−2}) • Π(pf, pf + p)` (sign convention of
the *Proof* of (M1) of `CSI8_the_split_move.md`, as CSI7's `QTsign`). -/
def QAsign (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  ((-1 : A) ^ p * (p : A) ^ (p - 2)) • prodQ Q (p * f) (p * f + p)

/-- `QC` with the sign `(−1)^p` built in: `((−1)^p p^{p−2}) • Π(pf + r, pf + r + p)` (sign
convention of the *Proof* of (M1) of `CSI8_the_split_move.md`). -/
def QCsign (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  ((-1 : A) ^ p * (p : A) ^ (p - 2)) • prodQ Q (p * f + r) (p * f + r + p)

/-- The new data with the sign `(−1)^p` built into the diagonal blocks:
`QSsign f = [[QAsign f, 0], [K f, QCsign f]]` (sign convention of the *Proof* of (M1) of
`CSI8_the_split_move.md`; valid for every `p`). -/
def QSsign (Q : ℕ → Matrix S S A) : ℕ → Matrix (S × Bool) (S × Bool) A :=
  blockS (QAsign p Q) (QCsign p r Q) (KS p r Q)

/-- For odd `p`, `QSsign = QS` (sign convention of the *Proof* of (M1) of
`CSI8_the_split_move.md`). -/
lemma QSsign_of_odd {p : ℕ} (hp : Odd p) (r : ℕ) (Q : ℕ → Matrix S S A) :
    QSsign p r Q = QS p r Q := by
  have h1 : QAsign p Q = QA p Q := by funext f; simp [QAsign, QA, hp.neg_one_pow]
  have h2 : QCsign p r Q = QC p r Q := by funext f; simp [QCsign, QC, hp.neg_one_pow]
  simp [QSsign, QS, h1, h2]

/-- `QA` is CSI7's twisted data: `QA p Q = QT p Q` (*Part S* of `CSI8_the_split_move.md`). -/
lemma QA_eq_QT (Q : ℕ → Matrix S S A) : QA p Q = QT p Q := by
  funext f; simp [QA, QT, prodQ]

/-- `QAsign p Q = QTsign p Q` (*Part S* of `CSI8_the_split_move.md`). -/
lemma QAsign_eq_QTsign (Q : ℕ → Matrix S S A) : QAsign p Q = QTsign p Q := by
  funext f; simp [QAsign, QTsign, prodQ]

/-- `QCsign` is CSI7's `QTsign` of the shifted data `φ ↦ Q (φ + r)` (*Part S* of
`CSI8_the_split_move.md`). -/
lemma QCsign_eq_QTsign (Q : ℕ → Matrix S S A) :
    QCsign p r Q = QTsign p (fun φ => Q (φ + r)) := by
  funext f
  simp only [QCsign, QTsign, prodQ, Nat.add_sub_cancel_left]
  congr 2
  exact List.map_congr_left fun j _ => by rw [add_right_comm]

end ColouredSand.OddTwist
