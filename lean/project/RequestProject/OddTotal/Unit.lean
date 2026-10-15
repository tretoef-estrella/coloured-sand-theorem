module

public import RequestProject.BlockOp.All

/-!
# `CSI19_theorem_TOTAL.md`, Part U — `q` enters only through `v_p(q)`

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

## Encodings

* `ℤ_[p]` is Mathlib's `PadicInt p`, `p` a prime (`[Fact p.Prime]`); `v_p(q)` is
  `padicValNat p q`.
* CSG6's operator `BlockOp.opT p M m q c = F^{(1)} + q • (c • id + half p • (m • id − H))` on a
  DP-lattice `M` and its cokernel `BlockOp.cokT p M m q c = (M.ι → ℤ_[p]) ⧸ range (opT p M m q c)`
  are reused, not redefined.
* **The convention of (U1).** Write `q = p^e · u` (`e = v_p(q)`, `u = q / p^e` a natural number
  prime to `p`, hence a unit `U` of `ℤ_[p]`).  The diagonal map `oddTotalDiag M U` multiplies the
  coordinate of the basis vector `i` by `U ^ n(wt i)`, where the *floor index* is the integer
  `n(h) = −(h / 2)` (Lean's `Int` division, rounding towards `−∞` here since the divisor is `2`):
  it satisfies `n(h − 2) = n(h) + 1`, which is all that is used.  As `F^{(1)}` lowers weights by
  `2` (axiom (W) of a DP-lattice), `diag ∘ opT p M m q c = (U • opT p M m (p^e) c) ∘ diag`, and a
  unit factor does not change the range.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.BlockOp ColouredSand.Splitting

variable {p : ℕ} [Fact p.Prime]

/-- Coordinates of `F^{(1)} v` through the matrix of `F^{(1)}` (auxiliary for Part U of
`CSI19_theorem_TOTAL.md`). -/
lemma oddTotal_Fd_apply (M : DPLattice ℤ_[p]) (v : M.ι → ℤ_[p]) (j : M.ι) :
    M.Fd 1 v j = ∑ i, v i * M.Fd 1 (Pi.single i 1) j := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℤ_[p]) : M.ι → ℤ_[p]) := by
    ext k; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]

/-- The diagonal map `δ_i ↦ U^{n(wt i)} δ_i`, `n(h) = −(h/2)` (Part U of
`CSI19_theorem_TOTAL.md`). -/
def oddTotalDiag (M : DPLattice ℤ_[p]) (U : ℤ_[p]ˣ) : (M.ι → ℤ_[p]) ≃ₗ[ℤ_[p]] (M.ι → ℤ_[p]) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (U ^ (-(M.wt i / 2)))

lemma oddTotalDiag_apply (M : DPLattice ℤ_[p]) (U : ℤ_[p]ˣ) (v : M.ι → ℤ_[p]) (i : M.ι) :
    oddTotalDiag M U v i = ((U ^ (-(M.wt i / 2)) : ℤ_[p]ˣ) : ℤ_[p]) * v i := rfl

/-- The floor index drops by one along `F^{(1)}` (auxiliary for Part U). -/
lemma oddTotal_floor_step (U : ℤ_[p]ˣ) {h h' : ℤ} (hh : h' = h - 2) :
    ((U ^ (-(h' / 2)) : ℤ_[p]ˣ) : ℤ_[p]) = (U : ℤ_[p]) * ((U ^ (-(h / 2)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  have : -(h' / 2) = 1 + -(h / 2) := by
    subst hh
    have : (h - 2) / 2 = h / 2 - 1 := by omega
    omega
  rw [this, zpow_add, zpow_one, Units.val_mul]

/-- The conjugation of Part U of `CSI19_theorem_TOTAL.md`: for `q = p^e · u` with `U = u` a unit,
`diag (opT p M m q c v) = U • opT p M m (p^e) c (diag v)`. -/
lemma oddTotal_diag_conj (M : DPLattice ℤ_[p]) (U : ℤ_[p]ˣ) {q e u : ℕ} (hq : q = p ^ e * u)
    (hU : (U : ℤ_[p]) = u) (m c : ℕ) (v : M.ι → ℤ_[p]) :
    oddTotalDiag M U (opT p M m q c v) = (U • opT p M m (p ^ e) c) (oddTotalDiag M U v) := by
  funext j
  simp only [LinearMap.smul_apply, opT_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    oddTotalDiag_apply, DPLattice.Hop_apply, smul_eq_mul, Units.smul_def]
  rw [oddTotal_Fd_apply M v j, oddTotal_Fd_apply M (oddTotalDiag M U v) j]
  simp only [oddTotalDiag_apply]
  have hF : ∀ i, ((U ^ (-(M.wt j / 2)) : ℤ_[p]ˣ) : ℤ_[p]) * (v i * M.Fd 1 (Pi.single i 1) j) =
      (U : ℤ_[p]) * (((U ^ (-(M.wt i / 2)) : ℤ_[p]ˣ) : ℤ_[p]) * v i *
        M.Fd 1 (Pi.single i 1) j) := by
    intro i
    by_cases hw : M.wt j = M.wt i - 2 * (1 : ℕ)
    · rw [oddTotal_floor_step U (by simpa using hw)]; ring
    · rw [M.isDP.W_F i 1 j hw]; ring
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl fun i _ => hF i, ← Finset.mul_sum, hq, hU]
  push_cast
  ring

/-- A unit multiple has the same range (auxiliary for Part U). -/
lemma oddTotal_range_unit_smul {N : Type*} [AddCommGroup N] [Module ℤ_[p] N] (U : ℤ_[p]ˣ)
    (f : Module.End ℤ_[p] N) : LinearMap.range (U • f) = LinearMap.range f := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨(U : ℤ_[p]) • y, by rw [map_smul, Units.smul_def]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨((U⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y, by
      rw [map_smul, Units.smul_def, smul_smul, Units.mul_inv, one_smul]⟩

/-- `u = q / p^{v_p q}` is a unit of `ℤ_[p]` (auxiliary for Part U). -/
lemma oddTotal_isUnit_cofactor {q : ℕ} (hq : q ≠ 0) :
    IsUnit ((q / p ^ padicValNat p q : ℕ) : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  have hp : p.Prime := Fact.out
  have h := Nat.coprime_ordCompl hp hq
  rwa [Nat.factorization_def q hp] at h

/-- **(U1)** of `CSI19_theorem_TOTAL.md`: for every DP-lattice `M` over `ℤ_[p]`, every `m, c`
and every `q ≠ 0` (no hypothesis `p ∣ q` is needed: more general),
`cokT p M m q c ≃ₗ[ℤ_[p]] cokT p M m (p^e) c` with `e = v_p(q)`.  The equivalence is induced by
the diagonal map `oddTotalDiag` (see the module docstring for the convention). -/
theorem oddTotal_U1 (M : DPLattice ℤ_[p]) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (cokT p M m q c ≃ₗ[ℤ_[p]] cokT p M m (p ^ padicValNat p q) c) := by
  set e := padicValNat p q
  obtain ⟨U, hU⟩ := oddTotal_isUnit_cofactor (p := p) hq
  have hqe : q = p ^ e * (q / p ^ e) := (Nat.mul_div_cancel' (pow_padicValNat_dvd)).symm
  exact ⟨(cokerEquivOfConj (opT p M m q c) (U • opT p M m (p ^ e) c) (oddTotalDiag M U)
    (oddTotalDiag M U) (fun v => (oddTotal_diag_conj M U hqe hU m c v).symm)).trans
    (Submodule.quotEquivOfEq _ _ (oddTotal_range_unit_smul U _))⟩

end ColouredSand.OddTwist
