module

public import RequestProject.DPLattice.Dictionary
public import RequestProject.CubeLaplacian.Reduction

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: Part C (Corollary 2.3)

Encodings:
* A finite family of DP-lattices is `M : J → DPLattice A` with `[Fintype J] [DecidableEq J]`;
  `Π_j M_j` is `(j : J) → (M j).ι → A`.
* "`Θ` commutes with `F^{(1)}` and `H` (componentwise on the right)" is
  `Θ (F^{(1)} x) = fun j => (M j).Fd 1 (Θ x j)` and `Θ (H x) = fun j => H (M j) (Θ x j)`.
* `F^{(1)} + n − H on M_j` is `(M j).Fd 1 + (n : A) • LinearMap.id - H (M j)`.
* (C2) uses `CubeLaplacian.D2`, `CubeLaplacian.K` and `CubeLaplacian.Syl2` of C17.
-/

@[expose] public section

noncomputable section

namespace DPLattice

open CubeLaplacian

variable {A : Type*} [CommRing A]

/-- (C1, auxiliary) The range of a componentwise operator on a finite product is the product of the ranges. -/
lemma range_pi_eq {J : Type*} {X : J → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module A (X j)]
    (T : ∀ j, Module.End A (X j)) :
    LinearMap.range (LinearMap.pi fun j => T j ∘ₗ LinearMap.proj j) =
      Submodule.pi Set.univ fun j => LinearMap.range (T j) := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, rfl⟩ j
    exact ⟨x j, rfl⟩
  · intro h
    choose x hx using h
    exact ⟨x, funext fun j => hx j⟩

/-- (C1) Corollary 2.3 (explicit equivalence): an `A`-linear equivalence
`Θ : V^{⊗n} ≃ Π_j M_j` commuting with `F^{(1)}` and `H` gives
`(G n → A) ⧸ range (lap A n) ≃ₗ[A] Π_j (M_j ⧸ range (F^{(1)} + n − H on M_j))`. -/
def C1equiv (n : ℕ) {J : Type*} [Fintype J] [DecidableEq J] (M : J → DPLattice A)
    (Θ : ((tensorPow A n).ι → A) ≃ₗ[A] ((j : J) → (M j).ι → A))
    (hF : ∀ x, Θ ((tensorPow A n).Fd 1 x) = fun j => (M j).Fd 1 (Θ x j))
    (hH : ∀ x, Θ (H (tensorPow A n) x) = fun j => H (M j) (Θ x j)) :
    ((G n → A) ⧸ LinearMap.range (lap A n)) ≃ₗ[A]
      ((j : J) → ((M j).ι → A) ⧸
        LinearMap.range ((M j).Fd 1 + (n : A) • LinearMap.id - H (M j))) :=
  let T : ∀ j, Module.End A ((M j).ι → A) := fun j =>
    (M j).Fd 1 + (n : A) • LinearMap.id - H (M j)
  let Tpi : Module.End A ((j : J) → (M j).ι → A) := LinearMap.pi fun j => T j ∘ₗ LinearMap.proj j
  let Φ := (psi A n).trans Θ
  have hΦ : Φ.toLinearMap ∘ₗ lap A n = Tpi ∘ₗ Φ.toLinearMap := by
    refine LinearMap.ext fun f => ?_
    have h1 : psi A n (lap A n f) = Tn A n (psi A n f) := LinearMap.congr_fun (psi_comm n) f
    funext j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1, Tn,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_sub, map_add, map_smul, hF, hH, Tpi, T, LinearMap.pi_apply, LinearMap.proj_apply, Φ]
    rfl
  have hmap : Submodule.map Φ.toLinearMap (LinearMap.range (lap A n)) = LinearMap.range Tpi := by
    rw [← LinearMap.range_comp, hΦ, LinearMap.range_comp_of_range_eq_top]
    exact LinearEquiv.range Φ
  (Submodule.Quotient.equiv _ _ Φ hmap).trans
    ((Submodule.quotEquivOfEq _ _ (range_pi_eq T)).trans (Submodule.quotientPi _))

/-- (C1) Corollary 2.3: if `Θ : V^{⊗n} ≃ₗ[A] Π_j M_j` is an `A`-linear equivalence commuting with
`F^{(1)}` and with `H` (componentwise on the right), then
`(G n → A) ⧸ range (lap A n) ≃ₗ[A] Π_j (M_j ⧸ range (F^{(1)} + n − H on M_j))`. -/
theorem C1 (n : ℕ) {J : Type*} [Fintype J] [DecidableEq J] (M : J → DPLattice A)
    (Θ : ((tensorPow A n).ι → A) ≃ₗ[A] ((j : J) → (M j).ι → A))
    (hF : ∀ x, Θ ((tensorPow A n).Fd 1 x) = fun j => (M j).Fd 1 (Θ x j))
    (hH : ∀ x, Θ (H (tensorPow A n) x) = fun j => H (M j) (Θ x j)) :
    Nonempty (((G n → A) ⧸ LinearMap.range (lap A n)) ≃ₗ[A]
      ((j : J) → ((M j).ι → A) ⧸
        LinearMap.range ((M j).Fd 1 + (n : A) • LinearMap.id - H (M j)))) :=
  ⟨C1equiv n M Θ hF hH⟩

/-- (C2) With `A = ℤ_[2]` and C17 (D2): under the hypothesis of (C1),
`ℤ_[2] × Syl_2 K(Q_n) ≃+ Π_j (M_j ⧸ range (F^{(1)} + n − H on M_j))`. -/
theorem C2 (n : ℕ) {J : Type*} [Fintype J] [DecidableEq J] (M : J → DPLattice ℤ_[2])
    (Θ : ((tensorPow ℤ_[2] n).ι → ℤ_[2]) ≃ₗ[ℤ_[2]] ((j : J) → (M j).ι → ℤ_[2]))
    (hF : ∀ x, Θ ((tensorPow ℤ_[2] n).Fd 1 x) = fun j => (M j).Fd 1 (Θ x j))
    (hH : ∀ x, Θ (H (tensorPow ℤ_[2] n) x) = fun j => H (M j) (Θ x j)) :
    Nonempty (ℤ_[2] × Syl2 (K n) ≃+
      ((j : J) → ((M j).ι → ℤ_[2]) ⧸
        LinearMap.range ((M j).Fd 1 + (n : ℤ_[2]) • LinearMap.id - H (M j)))) := by
  obtain ⟨d⟩ := D2 n
  exact ⟨d.symm.trans (C1equiv n M Θ hF hH).toAddEquiv⟩

end DPLattice
