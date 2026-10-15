module

public import RequestProject.Dance.Relabel

/-!
# Part D, (D3), of `C13_the_dance.md`: the final system is the final matrix

* `sysNilEquiv R : Sys(T([]), Fin R) ≃ (Fin R → A)`, `x ι_{s,()} ↦ Pi.single s x`.
* `D3_intertwine`: under `sysNilEquiv`, `G[0, 0, p, κ]` is `Matrix.toLin' (Mfin p κ)`.
* **(D3)** `D3_final_matrix`: `Sys(T([]), Fin R) ⧸ range(c · G[0, 0, p, κ]) ≅
  (Fin R → A) ⧸ range(c · Matrix.toLin' (Mfin p κ))`.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment
open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- On `T([])` the floor is `0` (*Setting*, "The tower", of `C13_the_dance.md`). -/
lemma fl_nil : fl [] = fun _ => 0 := rfl

variable (A) in
/-- On `T([])` the operator is `0` (*Setting*, "The tower", of `C13_the_dance.md`). -/
lemma F_nil : F A [] = 0 := rfl

variable (A) in
/-- `Sys(T([]), Fin R) = ⨁_{(s, ())} A ≅ (Fin R → A)` (*Part D*, (D3), *Proof*, of
`C13_the_dance.md`). -/
noncomputable def sysNilEquiv (R : ℕ) : SysT A [] (Fin R) ≃ₗ[A] (Fin R → A) :=
  (DirectSum.linearEquivFunOnFintype A (Fin R × Idx []) (fun _ => A)).trans
    (LinearEquiv.funCongrLeft A A (Equiv.prodPUnit (Fin R)).symm)

/-- `sysNilEquiv (x ι_{s,()}) = Pi.single s x` (*Part D*, (D3), *Proof*, of
`C13_the_dance.md`). -/
lemma sysNilEquiv_slotLof (R : ℕ) (s : Fin R) (i : Idx []) (x : A) :
    sysNilEquiv A R (slotLof A (fun _ : Idx [] => A) (Fin R) s i x) = Pi.single s x := by
  funext t
  simp only [sysNilEquiv, slotLof, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (congrArg Prod.fst h1) h2
  · exact absurd (by subst h2; rfl) h1
  · rfl

/-- On `T([])` the payment system `G[0, 0, p, κ]` is the final matrix acting on `Fin R → A`:
`sysNilEquiv ∘ G[0, 0, p, κ] = Matrix.toLin' (Mfin p κ) ∘ sysNilEquiv` (*Setting*, "The final
matrix", and *Part D*, (D3), *Proof*, of `C13_the_dance.md`). -/
theorem D3_intertwine (R : ℕ) (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) :
    (sysNilEquiv A R : SysT A [] (Fin R) →ₗ[A] (Fin R → A)) ∘ₗ G (fl []) (F A []) p κ =
      Matrix.toLin' (Mfin p κ) ∘ₗ (sysNilEquiv A R : SysT A [] (Fin R) →ₗ[A] (Fin R → A)) := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i⟩
  refine LinearMap.ext fun x => ?_
  change sysNilEquiv A R (G (fl []) (F A []) p κ (slotLof A _ (Fin R) s' i x)) =
    Matrix.toLin' (Mfin p κ) (sysNilEquiv A R (slotLof A _ (Fin R) s' i x))
  have hF : F A [] = 0 := rfl
  have hfl : fl [] i = 0 := rfl
  rw [G_eq]
  simp only [LinearMap.add_apply, FS_slotLof, DS_slotLof, map_add, map_sum, map_smul,
    sysNilEquiv_slotLof, hF, hfl, LinearMap.zero_apply, map_zero, zero_add]
  funext t
  simp only [Matrix.toLin'_apply, Matrix.mulVec_single, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Mfin]
  split_ifs <;> (subst_vars; simp_all)

/-- **(D3) The final system is the final matrix** of `C13_the_dance.md`: for data `(p, κ)` on
`Fin R` over `T([])` and every `c ∈ A`,
`Sys(T([]), Fin R) ⧸ range(c · G[0, 0, p, κ]) ≅ (Fin R → A) ⧸ range(c · Matrix.toLin' (Mfin p κ))`.
-/
theorem D3_final_matrix (R : ℕ) (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) (c : A) :
    Nonempty ((SysT A [] (Fin R) ⧸ LinearMap.range (c • G (fl []) (F A []) p κ)) ≃ₗ[A]
      ((Fin R → A) ⧸ LinearMap.range (c • Matrix.toLin' (Mfin p κ)))) :=
  ⟨cokerEquivOfIntertwine _ _ _ (D3_intertwine R p κ) c⟩

end Dance
