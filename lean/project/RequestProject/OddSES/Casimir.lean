module

public import RequestProject.OddSplit.All
public import RequestProject.Lemma35.All

/-!
# `CSI4_the_short_exact_sequences.md`: Part C, (C1) — the Casimir

Namespace `ColouredSand.OddTwist`. We reuse C18 (`DPLattice`, `H`, `Hom`, `IsDP`, `InWt`),
C20 (`Doubling.dp_lie`, `Doubling.Hop_of_inWt`, `Doubling.cancel_smul`) and CSI3 (`Q0a`).

Encodings:

* For a DP-lattice `M` over a commutative ring `A`, `casimir M : Module.End A (M.ι → A)` is
  `Ω_M := 4 • (M.Fd 1 ∘ M.Ed 1) + (H M + 1)²` (the scalar `4` is `(4 : A)`, and `1` is the identity
  endomorphism).
* "`Ω_M` commutes with `T`" is `casimir M ∘ₗ T = T ∘ₗ casimir M`.
* (C1) for `H`, `F^{(1)}`, `E^{(1)}` holds over every commutative ring (`casimir_comm_H`,
  `casimir_comm_F1`, `casimir_comm_E1`, from `E F = F E + H` and the weight rules); for every
  `F^{(r)}`, `E^{(r)}` it is proved over every domain of characteristic zero (e.g. `ℤ_[p]`) from
  (Q0a) and torsion-freeness (`casimir_comm_Fd`, `casimir_comm_Ed`) — more general than `ℤ_[p]`.
* `casimir_hom`: a morphism `f : Hom M M'` satisfies `f ∘ Ω_M = Ω_{M'} ∘ f` (any commutative ring).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

section casimir

variable {A : Type*} [CommRing A]

/-- (C1) The Casimir `Ω_M := 4 • (F ∘ E) + (H + 1)²` of a DP-lattice `M`
(`F = M.Fd 1`, `E = M.Ed 1`). -/
def casimir (M : DPLattice A) : Module.End A (M.ι → A) :=
  (4 : A) • (M.Fd 1 ∘ₗ M.Ed 1) + (H M + 1) ^ 2

variable (M : DPLattice A)

/-- `Ω x = 4 F E x + H H x + 2 H x + x`. -/
lemma casimir_apply (x : M.ι → A) :
    casimir M x = (4 : A) • M.Fd 1 (M.Ed 1 x) + H M (H M x) + (2 : A) • H M x + x := by
  simp only [casimir, pow_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Module.End.mul_apply, Module.End.one_apply, map_add]
  module

/-- Weight rule: `H F x = F H x − 2 F x`. -/
lemma H_F1 (x : M.ι → A) : H M (M.Fd 1 x) = M.Fd 1 (H M x) - (2 : A) • M.Fd 1 x := by
  have : H M ∘ₗ M.Fd 1 = M.Fd 1 ∘ₗ H M - (2 : A) • M.Fd 1 := by
    refine ext_single fun i => ?_
    have h1 : InWt M.wt (M.wt i - 2) (M.Fd 1 (Pi.single i 1)) := by
      have := M.isDP.inWt_Fd 1 (inWt_single (A := A) M.wt i); simpa using this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [Doubling.Hop_of_inWt h1, Doubling.Hop_of_inWt (inWt_single (A := A) M.wt i), map_smul]
    push_cast; module
  exact LinearMap.congr_fun this x

/-- Weight rule: `H E x = E H x + 2 E x`. -/
lemma H_E1 (x : M.ι → A) : H M (M.Ed 1 x) = M.Ed 1 (H M x) + (2 : A) • M.Ed 1 x := by
  have : H M ∘ₗ M.Ed 1 = M.Ed 1 ∘ₗ H M + (2 : A) • M.Ed 1 := by
    refine ext_single fun i => ?_
    have h1 : InWt M.wt (M.wt i + 2) (M.Ed 1 (Pi.single i 1)) := by
      have := M.isDP.inWt_Ed 1 (inWt_single (A := A) M.wt i); simpa using this
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
    rw [Doubling.Hop_of_inWt h1, Doubling.Hop_of_inWt (inWt_single (A := A) M.wt i), map_smul]
    push_cast; module
  exact LinearMap.congr_fun this x

/-- (C1) `Ω_M` commutes with `H M`. -/
theorem casimir_comm_H : casimir M ∘ₗ H M = H M ∘ₗ casimir M := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, casimir_apply, map_add, map_smul, H_F1, H_E1]
  module

/-- (C1) `Ω_M` commutes with `F = M.Fd 1` (from `E F = F E + H` and the weight rules). -/
theorem casimir_comm_F1 : casimir M ∘ₗ M.Fd 1 = M.Fd 1 ∘ₗ casimir M := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, casimir_apply, Doubling.dp_lie M, map_add, map_smul, H_F1,
    map_sub]
  module

/-- (C1) `Ω_M` commutes with `E = M.Ed 1` (from `E F = F E + H` and the weight rules). -/
theorem casimir_comm_E1 : casimir M ∘ₗ M.Ed 1 = M.Ed 1 ∘ₗ casimir M := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, casimir_apply, Doubling.dp_lie M, map_add, map_smul, H_E1]
  module

lemma comm_pow_of_comm {X : Type*} [AddCommGroup X] [Module A X] {S T : Module.End A X}
    (h : S ∘ₗ T = T ∘ₗ S) (r : ℕ) : S ∘ₗ (T ^ r) = (T ^ r) ∘ₗ S := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, h,
      ← LinearMap.comp_assoc]

/-- (C1) Over a domain of characteristic zero (e.g. `ℤ_[p]`), `Ω_M` commutes with every
`F^{(r)}`: by (Q0a) `r! F^{(r)} = F^r`, and `ℤ_[p]`-lattices are torsion-free. -/
theorem casimir_comm_Fd [IsDomain A] [CharZero A] (r : ℕ) :
    casimir M ∘ₗ M.Fd r = M.Fd r ∘ₗ casimir M := by
  refine LinearMap.ext fun x => Doubling.cancel_smul (factorial_ne_zero_cast (A := A) r) ?_
  have h := LinearMap.congr_fun (comm_pow_of_comm (casimir_comm_F1 M) r) x
  have e1 := LinearMap.congr_fun (Q0a M r).1
  simp only [LinearMap.smul_apply] at e1
  simp only [LinearMap.comp_apply] at h ⊢
  rw [← map_smul, e1, e1, h]

/-- (C1) Over a domain of characteristic zero (e.g. `ℤ_[p]`), `Ω_M` commutes with every
`E^{(r)}`. -/
theorem casimir_comm_Ed [IsDomain A] [CharZero A] (r : ℕ) :
    casimir M ∘ₗ M.Ed r = M.Ed r ∘ₗ casimir M := by
  refine LinearMap.ext fun x => Doubling.cancel_smul (factorial_ne_zero_cast (A := A) r) ?_
  have h := LinearMap.congr_fun (comm_pow_of_comm (casimir_comm_E1 M) r) x
  have e1 := LinearMap.congr_fun (Q0a M r).2
  simp only [LinearMap.smul_apply] at e1
  simp only [LinearMap.comp_apply] at h ⊢
  rw [← map_smul, e1, e1, h]

variable {M}

/-- (C1) A morphism `f : Hom M M'` satisfies `f ∘ Ω_M = Ω_{M'} ∘ f`. -/
theorem casimir_hom {M' : DPLattice A} (f : Hom M M') :
    f.toLin ∘ₗ casimir M = casimir M' ∘ₗ f.toLin := by
  have hF : ∀ x, f.toLin (M.Fd 1 x) = M'.Fd 1 (f.toLin x) :=
    fun x => LinearMap.congr_fun (f.comm_F 1) x
  have hE : ∀ x, f.toLin (M.Ed 1 x) = M'.Ed 1 (f.toLin x) :=
    fun x => LinearMap.congr_fun (f.comm_E 1) x
  have hH : ∀ x, f.toLin (H M x) = H M' (f.toLin x) := fun x => LinearMap.congr_fun f.comm_H x
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, casimir_apply, map_add, map_smul, hF, hE, hH]

variable (M)

/-- (C1) **The Casimir.** For a DP-lattice `M` over `ℤ_[p]` (more generally over any domain of
characteristic zero), `Ω_M = 4 • (F ∘ E) + (H + 1)²` commutes with `H M` and with every
`M.Fd r`, `M.Ed r`; and every morphism `f : Hom M M'` satisfies `f ∘ Ω_M = Ω_{M'} ∘ f`. -/
theorem C1 [IsDomain A] [CharZero A] :
    casimir M ∘ₗ H M = H M ∘ₗ casimir M ∧
    (∀ r, casimir M ∘ₗ M.Fd r = M.Fd r ∘ₗ casimir M) ∧
    (∀ r, casimir M ∘ₗ M.Ed r = M.Ed r ∘ₗ casimir M) ∧
    (∀ (M' : DPLattice A) (f : Hom M M'), f.toLin ∘ₗ casimir M = casimir M' ∘ₗ f.toLin) :=
  ⟨casimir_comm_H M, casimir_comm_Fd M, casimir_comm_Ed M, fun _ f => casimir_hom f⟩

end casimir

end ColouredSand.OddTwist
