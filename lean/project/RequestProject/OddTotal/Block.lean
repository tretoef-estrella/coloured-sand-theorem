module

public import RequestProject.OddTotal.Unit
public import RequestProject.OddTheoremI.All

/-!
# `CSI19_theorem_TOTAL.md`, Part B — one dance lattice

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

## Encodings

* CSI6's dance lattice `danceL p λ` (`λ` written `l`), CSI9's floor `flL p λ i = (λ − wt i)/2` and
  diagonal operator `Dop`, CSI10's `sigmaOp p λ e i = Fd 1 + p^e • (Dop (flL p λ) + i • 1)` and
  `Y_p(λ, i, e) = Yp p λ i e = ((danceL p λ).ι → ℤ_[p]) ⧸ range (sigmaOp p λ e i)` are reused
  (note the argument orders `sigmaOp p l e i` and `Yp p l i e`).
* "`λ ≡ m (mod 2)`" is `λ % 2 = m % 2`; `(m − λ)/2` is natural-number division (exact here).
* (B1) is proved by showing that the two operators are *equal* (`oddTotal_opT_eq_sigmaOp`): on a
  basis vector of weight `h = λ − 2f` one has `(m − h)/2 = (m − λ)/2 + f`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.BlockOp

variable {p : ℕ} [Fact p.Prime]

/-- Part B of `CSI19_theorem_TOTAL.md`: for `p ≠ 2`, `λ ≤ m` and `λ ≡ m (mod 2)`, CSG6's operator
`opT p (danceL p λ) m (p^e) c` *is* CSI10's `σ = sigmaOp p λ e (c + (m − λ)/2)`. -/
theorem oddTotal_opT_eq_sigmaOp (hp2 : p ≠ 2) {l m : ℕ} (hle : l ≤ m) (hpar : l % 2 = m % 2)
    (e c : ℕ) : opT p (danceL p l) m (p ^ e) c = sigmaOp p l e (c + (m - l) / 2) := by
  refine LinearMap.ext fun v => funext fun j => ?_
  obtain ⟨f, hf⟩ := wtForm_danceL p l j
  have hfl : flL p l j = f := wtForm_floor hf
  have hm : m = l + 2 * ((m - l) / 2) := by omega
  simp only [opT_apply, sigmaOp, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, DPLattice.Hop_apply, Dop_apply, Module.End.one_apply,
    smul_eq_mul, hfl, hf]
  have h2 := two_mul_half (p := p) hp2
  set k := (m - l) / 2
  rw [hm]
  push_cast
  linear_combination (↑p ^ e * (k + f : ℤ_[p]) * v j) * h2

/-- **(B1)** of `CSI19_theorem_TOTAL.md`: for `p ≠ 2`, `λ ≡ m (mod 2)` and `λ ≤ m`,
`cokT p (danceL p λ) m (p^e) c ≃ₗ[ℤ_[p]] Y_p(λ, c + (m − λ)/2, e)` (for every `e`, `c`). -/
theorem oddTotal_B1 (hp2 : p ≠ 2) {l m : ℕ} (hle : l ≤ m) (hpar : l % 2 = m % 2) (e c : ℕ) :
    Nonempty (cokT p (danceL p l) m (p ^ e) c ≃ₗ[ℤ_[p]] Yp p l (c + (m - l) / 2) e) :=
  ⟨Submodule.quotEquivOfEq _ _ (by rw [oddTotal_opT_eq_sigmaOp hp2 hle hpar])⟩

end ColouredSand.OddTwist
