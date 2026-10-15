module

public import RequestProject.Payment.Twist

/-!
# Part A of `C11_payment_systems_twist.md`: the twist move

* **Theorem A** (`theorem_A`): for every `c : A`, there is an `A`-linear equivalence
  `M_Φ^S ⧸ range (c • G_Φ) ≃ (M^S ⧸ c • ⊤) × (M^S ⧸ range (c • 2 • G'))`.
* **Corollary A1** (`corollary_A1`, Proposition 4.1): `M_Φ^S ⧸ range G_Φ ≃ M^S ⧸ range (2 • G')`.
* **Corollary A2** (`corollary_A2`): `M_Φ^S ⧸ range (2^h • G_Φ) ≃
  (M^S ⧸ 2^h • ⊤) × (M^S ⧸ range (2^(h+1) • G'))`.

Here `G_Φ = G (flΦ fl) (FΦ F) p κ` and `G' = G fl F (pT p) (κT p κ)` (see `Basic.lean`).
-/

@[expose] public section

namespace Payment

open DirectSum Finset
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [Fintype S] [LinearOrder S]

/-- In the decomposition `M_Φ^S = B_0 ⊕ B_1`, `G_Φ` is the block operator
`(a, b) ↦ (T_0 a + 2 F b, a + T_1 b)` (the two displayed formulas of the *Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma projS_comp_G (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    projS (A := A) ∘ₗ G (flΦ fl) (FΦ F) p κ =
      blockOp (DS (N := N) (fun i => 2 * fl i) p κ) (DS (fun i => 2 * fl i + 1) p κ) (FS F)
        ∘ₗ projS := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i, e⟩
  refine LinearMap.ext fun x => ?_
  fin_cases e
  · exact projS_G_lof0 fl F p κ s' i x
  · exact projS_G_lof1 fl F p κ s' i x

/-- **Theorem A** (the twist move, scaled) of `C11_payment_systems_twist.md`: for every graded
family `(ι, fl, N, F)`, every slot type `S`, all halved data `(p, κ)` on `Φ` and every `c ∈ A`,
there is an `A`-linear isomorphism
`M_Φ^S / range(c · G_Φ) ≅ (M^S / c·M^S) × (M^S / range(c · 2 · G'))`,
with `G_Φ = G[fl^Φ, F^Φ, p, κ]` and `G' = G[fl, F, p', κ']`. -/
theorem theorem_A (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (c : A) :
    Nonempty ((Sys (NΦ N) S ⧸ LinearMap.range (c • G (flΦ fl) (FΦ F) p κ)) ≃ₗ[A]
      (Sys N S ⧸ c • (⊤ : Submodule A (Sys N S))) ×
        (Sys N S ⧸ LinearMap.range (c • (2 : A) • G fl F (pT p) (κT p κ)))) := by
  have hmap : (LinearMap.range (c • G (flΦ fl) (FΦ F) p κ)).map
      (splitEquiv (A := A) (N := N) (S := S) : Sys (NΦ N) S →ₗ[A] Sys N S × Sys N S) =
      LinearMap.range (c • blockOp (DS (N := N) (fun i => 2 * fl i) p κ)
        (DS (fun i => 2 * fl i + 1) p κ) (FS F)) := by
    have hsurj : LinearMap.range (projS (A := A) (N := N) (S := S)) = ⊤ :=
      LinearMap.range_eq_top.2 (splitEquiv (A := A) (N := N) (S := S)).surjective
    rw [splitEquiv_toLinearMap, ← LinearMap.range_comp, LinearMap.comp_smul, projS_comp_G,
      ← LinearMap.smul_comp,
      LinearMap.range_comp_of_range_eq_top _ hsurj]
  rw [G_eq fl F (pT p) (κT p κ)]
  let e1 := Submodule.Quotient.equiv _ _ (splitEquiv (A := A) (N := N) (S := S)) hmap
  let e2 := blockCokerEquiv (DS (N := N) (fun i => 2 * fl i) p κ)
    (DS (fun i => 2 * fl i + 1) p κ) (FS F) (DS fl (pT p) (κT p κ)) (DS_comp fl p κ) c
  exact ⟨e1.trans e2⟩

/-- **Corollary A1** (Proposition 4.1) of `C11_payment_systems_twist.md`: with `c = 1`,
`coker G_Φ ≅ coker(2 G')`, i.e. `M_Φ^S / range G_Φ ≅ M^S / range(2 · G')`. -/
theorem corollary_A1 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    Nonempty ((Sys (NΦ N) S ⧸ LinearMap.range (G (flΦ fl) (FΦ F) p κ)) ≃ₗ[A]
      (Sys N S ⧸ LinearMap.range ((2 : A) • G fl F (pT p) (κT p κ)))) := by
  obtain ⟨e⟩ := theorem_A fl F p κ (1 : A)
  rw [one_smul, one_smul, one_smul] at e
  haveI : Subsingleton (Sys N S ⧸ (⊤ : Submodule A (Sys N S))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Unique (Sys N S ⧸ (⊤ : Submodule A (Sys N S))) := uniqueOfSubsingleton 0
  exact ⟨e.trans (LinearEquiv.uniqueProd)⟩

/-- **Corollary A2** (one move of Proposition 4.3) of `C11_payment_systems_twist.md`: with
`c = 2^h`, `coker(2^h G_Φ) ≅ (M^S / 2^h M^S) × coker(2^{h+1} G')`. -/
theorem corollary_A2 (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) (h : ℕ) :
    Nonempty ((Sys (NΦ N) S ⧸ LinearMap.range ((2 : A) ^ h • G (flΦ fl) (FΦ F) p κ)) ≃ₗ[A]
      (Sys N S ⧸ (2 : A) ^ h • (⊤ : Submodule A (Sys N S))) ×
        (Sys N S ⧸ LinearMap.range ((2 : A) ^ (h + 1) • G fl F (pT p) (κT p κ)))) := by
  rw [pow_succ, ← smul_smul]
  exact theorem_A fl F p κ ((2 : A) ^ h)

end Payment
