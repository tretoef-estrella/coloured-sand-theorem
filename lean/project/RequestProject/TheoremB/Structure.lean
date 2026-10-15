module

public import RequestProject.TheoremB.TorsionTensor

/-!
# §0: `coker L ≅ ℤ ⊕ K(H(d,q))`, and `K(H(d,q))` is finite

This file corresponds to **§0 (Objects)** of `CS3_theorem_B.md`: "One has `coker L ≅ ℤ ⊕ K(H(d,q))`,
and `K` is finite (the graph is connected; prove it …)".

## Encoding

As in `RequestProject/TheoremB/Basic.lean`: `coker L = cokerL d q`, `K(H(d,q)) = sandpile d q`
(the torsion subgroup of `coker L`); `≅` is a `ℤ`-linear equivalence.

## Proof

* `hammingGraph_connected`: `H(d,q)` is connected for `q ≥ 1` (change one coordinate at a time).
* Hence (Mathlib's `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`) the real Laplacian
  has a one-dimensional kernel, so its real cokernel has dimension `1`.
* By (B1) for `ℝ` (`cokerBaseChangePi`), `ℝ ⊗ coker L` is that real cokernel.
* By the structure theorem, `coker L ≅ ℤ^n × T` with `T` finite; then `ℝ ⊗ coker L ≅ ℝ^n`, so
  `n = 1`, and `K = torsion (coker L) ≅ T`.
-/

@[expose] public section

open Finset TensorProduct

namespace ColouredSand.TheoremB

open ColouredSand.Splitting

lemma hammingDist_update_lt {d q : ℕ} {x y : Fin d → Fin q} {i : Fin d} (h : x i ≠ y i) :
    hammingDist (Function.update x i (y i)) y < hammingDist x y := by
  unfold hammingDist
  have hsub : (univ.filter fun j => Function.update x i (y i) j ≠ y j) ⊆
      univ.filter fun j => x j ≠ y j := by
    intro j
    simp only [mem_filter, mem_univ, true_and]
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact id
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i, ?_, ?_⟩)
  · simp [h]
  · simp

/-- The Hamming graph `H(d,q)` is connected for `q ≥ 1`. -/
theorem hammingGraph_connected (d q : ℕ) (hq : 1 ≤ q) : (hammingGraph d q).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨fun _ => ⟨0, hq⟩⟩⟩
  intro x y
  induction h : hammingDist x y using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hxy : x = y
    · subst hxy; rfl
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hc
        push_neg at hc
        exact hxy (funext hc)
      have hadj : (hammingGraph d q).Adj x (Function.update x i (y i)) :=
        hammingDist_update_self x i (Ne.symm hi)
      exact hadj.reachable.trans (ih _ (h ▸ hammingDist_update_lt hi) _ rfl)

/-- The real Laplacian of `H(d,q)` has a one-dimensional kernel. -/
lemma finrank_ker_lap_real (d q : ℕ) (hq : 1 ≤ q) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' ((hammingGraph d q).lapMatrix ℝ))) = 1 := by
  rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  have hc := hammingGraph_connected d q hq
  rw [Fintype.card_eq_one_iff]
  refine ⟨(hammingGraph d q).connectedComponentMk (fun _ => ⟨0, hq⟩), fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v => exact SimpleGraph.ConnectedComponent.eq.mpr (hc.preconnected _ _)

/-- The real cokernel of the Laplacian of `H(d,q)` is one-dimensional. -/
lemma finrank_coker_lap_real (d q : ℕ) (hq : 1 ≤ q) :
    Module.finrank ℝ (((Fin d → Fin q) → ℝ) ⧸
      LinearMap.range (Matrix.toLin' ((hammingGraph d q).lapMatrix ℝ))) = 1 := by
  have h1 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (Matrix.toLin' ((hammingGraph d q).lapMatrix ℝ)))
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' ((hammingGraph d q).lapMatrix ℝ))
  rw [finrank_ker_lap_real d q hq] at h2
  omega

/-- (B1) over `ℝ`: `ℝ ⊗ coker L ≅ coker (L ⊗ ℝ)`. -/
noncomputable def realCokerEquiv (d q : ℕ) :
    (ℝ ⊗[ℤ] cokerL d q) ≃ₗ[ℝ] ((Fin d → Fin q) → ℝ) ⧸
      LinearMap.range (Matrix.toLin' ((hammingGraph d q).lapMatrix ℝ)) :=
  cokerBaseChangePi (laplacian d q) _ fun f => by
    funext x
    rw [Matrix.toLin'_apply, SimpleGraph.lapMatrix_mulVec_apply, laplacian_apply]
    simp

lemma tensor_finite_subsingleton (T : Type*) [AddCommGroup T] [Finite T] :
    Subsingleton (ℝ ⊗[ℤ] T) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ z : ℝ ⊗[ℤ] T, z = 0 by rw [h a, h b]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    have hN : ((Nat.card T : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have : c = (Nat.card T) • (c / (Nat.card T : ℝ)) := by
      rw [nsmul_eq_mul]; field_simp
    rw [this, TensorProduct.smul_tmul, card_nsmul_eq_zero', TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- **§0.**  For `q ≥ 1`: `coker L ≅ ℤ ⊕ K(H(d,q))`, and `K(H(d,q))` is finite, where
`K(H(d,q)) = sandpile d q` is the torsion subgroup of `coker L`. -/
theorem cokerL_equiv_int_prod_sandpile (d q : ℕ) (hq : 1 ≤ q) :
    Nonempty (cokerL d q ≃ₗ[ℤ] ℤ × sandpile d q) ∧ Finite (sandpile d q) := by
  obtain ⟨n, ι, hι, pr, hirr, e, ⟨E⟩⟩ := Module.equiv_free_prod_directSum ℤ (cokerL d q)
  set T := DirectSum ι fun i => ℤ ⧸ ℤ ∙ pr i ^ e i
  haveI : ∀ i, Finite (ℤ ⧸ ℤ ∙ pr i ^ e i) := fun i =>
    finite_quot_span (pow_ne_zero _ (hirr i).ne_zero)
  haveI : Finite T := Finite.of_equiv _
    (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ℤ ⧸ ℤ ∙ pr i ^ e i)).toEquiv.symm
  -- `n = 1`
  haveI : Subsingleton (ℝ ⊗[ℤ] T) := tensor_finite_subsingleton T
  haveI : Unique (ℝ ⊗[ℤ] T) := uniqueOfSubsingleton 0
  let ER : (ℝ ⊗[ℤ] cokerL d q) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.baseChange ℤ ℝ _ _ E).trans
      ((TensorProduct.prodRight ℤ ℝ ℝ _ _).trans
        ((LinearEquiv.prodUnique).trans
          ((LinearEquiv.baseChange ℤ ℝ _ _ (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))).trans
            (tensorPiEquiv ℤ ℝ (Fin n)))))
  have hn : n = 1 := by
    have := ((realCokerEquiv d q).symm.trans ER).finrank_eq
    rwa [finrank_coker_lap_real d q hq, Module.finrank_fin_fun, eq_comm] at this
  subst hn
  -- `K ≅ T`
  have hT : Submodule.torsion ℤ T = ⊤ :=
    torsion_eq_top_of_smul ((Nat.card T : ℕ) : ℤ)
      (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')) fun x => by
        rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  let EK : sandpile d q ≃ₗ[ℤ] T := (torsionEquiv E).trans (torsionProdFree (torsion_finsupp_int 1) hT)
  refine ⟨⟨E.trans (LinearEquiv.prodCongr (Finsupp.LinearEquiv.finsuppUnique ℤ ℤ (Fin 1))
    EK.symm)⟩, Finite.of_equiv _ EK.toEquiv.symm⟩

end ColouredSand.TheoremB
