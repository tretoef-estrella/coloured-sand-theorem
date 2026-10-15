module

public import RequestProject.OddSES.PartS2

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, tools for (S4) and (S5)

* `surj_of_modP` — (S4) "surjective mod `p` is enough" (Nakayama): a linear map
  `f : (ι → ℤ_[p]) → (κ → ℤ_[p])` such that every basis vector `δ_k` lies in
  `range f + p • (κ → ℤ_[p])` is surjective.
* `shortExact_of_rank` — (S5) the rank argument: if `f : X → Y` has a linear left inverse,
  `g : Y → Z` is surjective, `g ∘ f = 0` and `|X.ι| + |Z.ι| = |Y.ι|`, then
  `WeylFilt.ShortExact f g`. (`range f` is saturated by CSI3 (Q0d); `range f ⊆ ker g` have the
  same rank, so `ker g / range f` is torsion, hence `ker g ⊆ range f`.)
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime]

/-- `p • X ≤ (span {p}) • ⊤`. -/
lemma pSub_le_smul_top {X : Type*} [AddCommGroup X] [Module ℤ_[p] X] :
    pSub p X ≤ Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] X) := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_pSub.1 hx
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- (S4) **Surjective mod `p` is enough** (Nakayama's lemma over the local ring `ℤ_[p]`). -/
theorem surj_of_modP {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : (ι → ℤ_[p]) →ₗ[ℤ_[p]] (κ → ℤ_[p]))
    (h : ∀ k, (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range f ⊔ pSub p (κ → ℤ_[p])) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  have htop : (⊤ : Submodule ℤ_[p] (κ → ℤ_[p])) ≤ LinearMap.range f ⊔ pSub p (κ → ℤ_[p]) := by
    rw [← (Pi.basisFun ℤ_[p] κ).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    exact h k
  refine top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : ℤ_[p])})
    Module.Finite.fg_top ?_ (htop.trans (sup_le_sup_left pSub_le_smul_top _)))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]

/-- (S5) **The rank argument.** If `f : X → Y` has a linear left inverse `ρ`, `g : Y → Z` is
surjective, `g ∘ f = 0`, and `|X.ι| + |Z.ι| = |Y.ι|`, then `0 → X → Y → Z → 0` is short exact. -/
theorem shortExact_of_rank {X Y Z : DPLattice ℤ_[p]} (f : Hom X Y) (g : Hom Y Z)
    (ρ : (Y.ι → ℤ_[p]) →ₗ[ℤ_[p]] (X.ι → ℤ_[p])) (hρ : ρ ∘ₗ f.toLin = LinearMap.id)
    (hg : Function.Surjective g.toLin) (hgf : g.toLin ∘ₗ f.toLin = 0)
    (hcard : Fintype.card X.ι + Fintype.card Z.ι = Fintype.card Y.ι) :
    WeylFilt.ShortExact f g := by
  have hinj : Function.Injective f.toLin := by
    intro x y hxy
    have := congrArg ρ hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hρ] at this
  refine ⟨hinj, hg, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hgf, LinearMap.zero_apply]
  · -- ranks
    set K := LinearMap.ker g.toLin
    set R := LinearMap.range f.toLin
    have hRK : R ≤ K := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hgf, LinearMap.zero_apply]
    have hR : Module.finrank ℤ_[p] R = Fintype.card X.ι := by
      rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
    have hK : Module.finrank ℤ_[p] K + Fintype.card Z.ι = Fintype.card Y.ι := by
      have h1 := Submodule.finrank_quotient_add_finrank K
      rw [(g.toLin.quotKerEquivOfSurjective hg).finrank_eq, Module.finrank_fintype_fun_eq_card,
        Module.finrank_fintype_fun_eq_card] at h1
      omega
    set R' : Submodule ℤ_[p] K := R.comap K.subtype
    have hR' : Module.finrank ℤ_[p] R' = Fintype.card X.ι := by
      rw [← hR]
      exact (Submodule.comapSubtypeEquivOfLe hRK).finrank_eq
    have hQ : Module.finrank ℤ_[p] (K ⧸ R') = 0 := by
      have h2 := Submodule.finrank_quotient_add_finrank R'
      omega
    intro y hy
    obtain ⟨a, ha, hay⟩ := (Module.finrank_eq_zero_iff.1 hQ) (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hay
    exact Q0d f.toLin ρ hρ ha hay

end ColouredSand.OddTwist
