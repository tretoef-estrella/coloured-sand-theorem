module

public import RequestProject.Split.SplitData

/-!
# Part B of `C12_split_move.md`: the split move

* **Theorem B** (`theorem_B`): for every `c : A`, an `A`-linear equivalence
  `Sys_Ψ ⧸ range (c • G_Ψ) ≃ (M^S ⧸ c • ⊤) × (M^S ⧸ c • ⊤) × (M^{S×{A,C}} ⧸ range (c • 2 • G''))`.
* **Corollary B1** (`corollary_B1`, `corollary_B1_VΦ`; Proposition 4.2): `c = 1`.
* **Corollary B2** (`corollary_B2`): `c = 2^h`.

Here `G_Ψ = G (flΨ fl) (FΨ F) p κ`, `G_{VΦ} = G (flVΦ fl) (FVΦ F) p κ` and
`G'' = G fl F (pSp p) (κSp p κ)` on `M^{S×{A,C}} = Sys N (Lex (S × Fin 2))` (see `Basic.lean`).
-/

@[expose] public section

namespace Split

open DirectSum Finset Payment
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [Fintype S] [LinearOrder S]

/-- **Theorem B** (the split move, scaled) of `C12_split_move.md`: for every graded family
`(ι, fl, N, F)`, every slot type `S`, all halved data `(p, κ)` on `Ψ` and every `c ∈ A`, there is an
`A`-linear isomorphism
`Sys_Ψ / range(c · G_Ψ) ≅ (M^S / c M^S) × (M^S / c M^S) × (M^{S×{A,C}} / range(c · 2 · G''))`,
with `G_Ψ = G[fl^Ψ, F^Ψ, p, κ]` and `G'' = G[fl, F, p'', κ'']` (lexicographic slot order on
`S × {A, C}`). -/
theorem theorem_B (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (c : A) :
    Nonempty ((Sys (NΨ N) S ⧸ LinearMap.range (c • G (flΨ fl) (FΨ F) p κ)) ≃ₗ[A]
      (Sys N S ⧸ c • (⊤ : Submodule A (Sys N S))) × (Sys N S ⧸ c • (⊤ : Submodule A (Sys N S))) ×
        (Sys N (Lex (S × Fin 2)) ⧸
          LinearMap.range (c • (2 : A) • G fl F (pSp p) (κSp p κ)))) := by
  have hmap : (LinearMap.range (c • G (flΨ fl) (FΨ F) p κ)).map
      (splitΨ A N S : Sys (NΨ N) S →ₗ[A] _) =
      LinearMap.range (c • blk4 (DS (N := N) (fun i => 2 * fl i) p κ)
        (DS (fun i => 2 * fl i + 1) p κ) (DS (fun i => 2 * fl i + 2) p κ) (FS F)) := by
    have hsurj : LinearMap.range (projΨ A N S) = ⊤ :=
      LinearMap.range_eq_top.2 (splitΨ A N S).surjective
    change (LinearMap.range (c • G (flΨ fl) (FΨ F) p κ)).map (projΨ A N S) = _
    rw [← LinearMap.range_comp, LinearMap.comp_smul, projΨ_comp_G, ← LinearMap.smul_comp,
      LinearMap.range_comp_of_range_eq_top _ hsurj]
  have hmap2 : (LinearMap.range (c • (2 : A) • G fl F (pSp p) (κSp p κ))).map
      (split2 (A := A) (N := N) (S := S) : Sys N (Lex (S × Fin 2)) →ₗ[A] _) =
      LinearMap.range (c • (2 : A) • blkH (FS F) (DS (fun i => 2 * fl i + 1) p κ)
        (DS fl (pT p) (κT p κ)) (DS fl (pT (shiftP p)) (κT (shiftP p) (shiftK κ)))) := by
    have hsurj : LinearMap.range (proj2 A N S) = ⊤ :=
      LinearMap.range_eq_top.2 (split2 (A := A) (N := N) (S := S)).surjective
    rw [split2_toLinearMap, ← LinearMap.range_comp, LinearMap.comp_smul, LinearMap.comp_smul,
      proj2_comp_G, ← LinearMap.smul_comp, ← LinearMap.smul_comp,
      LinearMap.range_comp_of_range_eq_top _ hsurj]
  let e1 := Submodule.Quotient.equiv _ _ (splitΨ A N S) hmap
  let e2 := blk4CokerEquiv (DS (N := N) (fun i => 2 * fl i) p κ)
    (DS (fun i => 2 * fl i + 1) p κ) (DS (fun i => 2 * fl i + 2) p κ) (FS F)
    (DS fl (pT p) (κT p κ)) (DS fl (pT (shiftP p)) (κT (shiftP p) (shiftK κ)))
    (DS_comp fl p κ) (DS_comp_shift fl p κ) c
  let e3 := Submodule.Quotient.equiv _ _ (split2 (A := A) (N := N) (S := S)) hmap2
  exact ⟨e1.trans (e2.trans (LinearEquiv.prodCongr (LinearEquiv.refl A _)
    (LinearEquiv.prodCongr (LinearEquiv.refl A _) e3.symm)))⟩

/-- `M^S ⧸ ⊤` is trivial (used for Corollary B1 of `C12_split_move.md`). -/
lemma quotient_top_prod_equiv {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] : Nonempty (((X ⧸ (⊤ : Submodule A X)) × Y) ≃ₗ[A] Y) := by
  haveI : Subsingleton (X ⧸ (⊤ : Submodule A X)) := Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Unique (X ⧸ (⊤ : Submodule A X)) := uniqueOfSubsingleton 0
  exact ⟨LinearEquiv.uniqueProd⟩

/-- **Corollary B1** (Proposition 4.2) of `C12_split_move.md`, for `Ψ`: with `c = 1`,
`coker G_Ψ ≅ coker(2 G'')`, i.e. `Sys_Ψ / range G_Ψ ≅ M^{S×{A,C}} / range(2 · G'')`. -/
theorem corollary_B1 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    Nonempty ((Sys (NΨ N) S ⧸ LinearMap.range (G (flΨ fl) (FΨ F) p κ)) ≃ₗ[A]
      (Sys N (Lex (S × Fin 2)) ⧸ LinearMap.range ((2 : A) • G fl F (pSp p) (κSp p κ)))) := by
  obtain ⟨e⟩ := theorem_B fl F p κ (1 : A)
  rw [one_smul, one_smul, one_smul] at e
  obtain ⟨e'⟩ := quotient_top_prod_equiv (A := A) (X := Sys N S)
    (Y := Sys N (Lex (S × Fin 2)) ⧸ LinearMap.range ((2 : A) • G fl F (pSp p) (κSp p κ)))
  obtain ⟨e''⟩ := quotient_top_prod_equiv (A := A) (X := Sys N S)
    (Y := (Sys N S ⧸ (⊤ : Submodule A (Sys N S))) ×
      (Sys N (Lex (S × Fin 2)) ⧸ LinearMap.range ((2 : A) • G fl F (pSp p) (κSp p κ))))
  exact ⟨(e.trans e'').trans e'⟩

/-- **Corollary B1** (Proposition 4.2) of `C12_split_move.md`, for `V ⊗ Φ` (by (A3)): with
`c = 1`, `coker G_{VΦ} ≅ coker(2 G'')`, i.e.
`Sys_{VΦ} / range G_{VΦ} ≅ M^{S×{A,C}} / range(2 · G'')`. -/
theorem corollary_B1_VΦ (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    Nonempty ((Sys (NVΦ N) S ⧸ LinearMap.range (G (flVΦ fl) (FVΦ F) p κ)) ≃ₗ[A]
      (Sys N (Lex (S × Fin 2)) ⧸ LinearMap.range ((2 : A) • G fl F (pSp p) (κSp p κ)))) := by
  obtain ⟨e1⟩ := A3_coker fl F p κ (1 : A)
  rw [one_smul, one_smul] at e1
  obtain ⟨e2⟩ := corollary_B1 fl F p κ
  exact ⟨e1.trans e2⟩

/-- **Corollary B2** (one split move of Proposition 4.3) of `C12_split_move.md`: with `c = 2^h`,
`coker(2^h G_Ψ) ≅ (M^S / 2^h M^S)^2 × coker(2^{h+1} G'')`. -/
theorem corollary_B2 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (h : ℕ) :
    Nonempty ((Sys (NΨ N) S ⧸ LinearMap.range ((2 : A) ^ h • G (flΨ fl) (FΨ F) p κ)) ≃ₗ[A]
      (Sys N S ⧸ (2 : A) ^ h • (⊤ : Submodule A (Sys N S))) ×
        (Sys N S ⧸ (2 : A) ^ h • (⊤ : Submodule A (Sys N S))) ×
          (Sys N (Lex (S × Fin 2)) ⧸
            LinearMap.range ((2 : A) ^ (h + 1) • G fl F (pSp p) (κSp p κ)))) := by
  rw [pow_succ, ← smul_smul]
  exact theorem_B fl F p κ ((2 : A) ^ h)

end Split
