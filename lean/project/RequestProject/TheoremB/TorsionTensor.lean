module

public import RequestProject.TheoremB.Completion

/-!
# `Syl_p X` as the torsion of `ℤ_[p] ⊗ X`, for finitely generated `X`

This file belongs to the proof of **(B3) Theorem B** of `CS3_theorem_B.md`: it packages (B1)
into the statement used there.  For a finitely generated abelian group `X`
(e.g. `X = coker L`), the `ℤ_[p]`-torsion of `ℤ_[p] ⊗[ℤ] X` is isomorphic to `Syl_p X`.

This replaces the "cancel the free summand" step of the proof in the file: instead of writing
`coker L ≅ ℤ ⊕ K` and cancelling `ℤ_[p]`, we take torsion submodules on both sides.

The proof uses the structure theorem `X ≅ ℤ^n × T` (`Module.equiv_free_prod_directSum`), with
`T` finite, and (B1) for `T` (`sylTensorEquiv`).
-/

@[expose] public section

open TensorProduct

namespace ColouredSand.TheoremB

variable {p : ℕ} [hp : Fact p.Prime]

lemma torsion_eq_bot_of_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : Submodule.torsion R N = ⊥) :
    Submodule.torsion R M = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hx
  have : e x ∈ Submodule.torsion R N := (Submodule.mem_torsion_iff _).mpr
    ⟨a, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, ha, map_zero]⟩
  rw [h, Submodule.mem_bot, e.map_eq_zero_iff] at this
  rw [this]
  exact zero_mem _

lemma torsion_finsupp_int (n : ℕ) : Submodule.torsion ℤ (Fin n →₀ ℤ) = ⊥ :=
  torsion_eq_bot_of_equiv (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)) (torsion_pi_eq_bot _)

lemma torsion_tensor_finsupp (n : ℕ) :
    Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] (Fin n →₀ ℤ)) = ⊥ :=
  torsion_eq_bot_of_equiv
    ((LinearEquiv.baseChange ℤ ℤ_[p] _ _ (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))).trans
      (tensorPiEquiv ℤ ℤ_[p] (Fin n)))
    (torsion_pi_eq_bot _)

lemma torsion_tensor_finite (T : Type*) [AddCommGroup T] [Finite T] :
    Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] T) = ⊤ := by
  refine torsion_eq_top_of_smul ((Nat.card T : ℕ) : ℤ_[p])
    (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')) fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul,
      card_nsmul_eq_zero', TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma finite_quot_span {a : ℤ} (ha : a ≠ 0) : Finite (ℤ ⧸ Ideal.span {a}) := by
  haveI : NeZero a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha⟩
  exact Finite.of_equiv _ (Int.quotientSpanEquivZMod a).toEquiv.symm

/-- **`torsion_{ℤ_[p]} (ℤ_[p] ⊗ X) ≅ Syl_p X`** for every finitely generated abelian group `X`. -/
theorem torsion_tensor_equiv_syl (X : Type*) [AddCommGroup X] [Module.Finite ℤ X] :
    Nonempty (Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X) ≃+ sylSub p X) := by
  obtain ⟨n, ι, hι, pr, hirr, e, ⟨E⟩⟩ := Module.equiv_free_prod_directSum ℤ X
  set T := DirectSum ι fun i => ℤ ⧸ ℤ ∙ pr i ^ e i
  haveI : ∀ i, Finite (ℤ ⧸ ℤ ∙ pr i ^ e i) := fun i =>
    finite_quot_span (pow_ne_zero _ (hirr i).ne_zero)
  haveI : Finite T := Finite.of_equiv _
    (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ℤ ⧸ ℤ ∙ pr i ^ e i)).toEquiv.symm
  let e1 : Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X) ≃ₗ[ℤ_[p]]
      Submodule.torsion ℤ_[p] ((ℤ_[p] ⊗[ℤ] (Fin n →₀ ℤ)) × (ℤ_[p] ⊗[ℤ] T)) :=
    torsionEquiv ((LinearEquiv.baseChange ℤ ℤ_[p] _ _ E).trans
      (TensorProduct.prodRight ℤ ℤ_[p] ℤ_[p] _ _))
  let e2 := torsionProdFree (torsion_tensor_finsupp (p := p) n) (torsion_tensor_finite (p := p) T)
  let e3 := (sylTensorEquiv (p := p) T).symm
  let e4 := (sylProdOfBot (p := p) (T := T) (sylSub_eq_bot_of_torsion (torsion_finsupp_int n))).symm
  let e5 := sylEquiv (p := p) E.symm
  exact ⟨(e1.trans e2).toAddEquiv.trans (e3.trans (e4.trans e5)).toAddEquiv⟩

end ColouredSand.TheoremB
