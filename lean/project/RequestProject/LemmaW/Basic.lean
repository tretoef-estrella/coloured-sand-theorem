module

public import RequestProject.WeylFilt.Basic

/-!
# `C25_lemma_W_and_ext.md`: Setting and Part P — weights of morphisms and of extensions

Encodings (namespace `LemmaW`), reusing C18 (namespace `DPLattice`: `DPLattice`, `IsDP`, `Hop`,
`H`, `Hom`, `delta`, `nabla`, `weylWt`, `deltaF`, `deltaE`, `nablaF`, `nablaE`) and C19
(namespace `WeylFilt`: `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`):

* A DP-lattice `M` over `A` is C18's `DPLattice A`: a finite basis `M.ι`, the module `M.ι → A`
  with basis vectors `δ_i = Pi.single i 1`, weights `M.wt`, and operators `M.Fd r = F^{(r)}`,
  `M.Ed s = E^{(s)}`. A morphism is C18's `Hom M N`, with underlying linear map `f.toLin`.
* An extension of `Z` by `N` is a short exact sequence `N —f→ X —g→ Z` of DP-lattices
  (C19's `ShortExact f g`: `f.toLin` injective, `g.toLin` surjective, `range f = ker g`).
* `IsWtPres φ` (Setting, "weight-preserving"): `φ (δ_i) j = 0` whenever `M.wt i ≠ N.wt j`.
* `pr M w` (Setting, "weight projection"): `(pr M w z) i = if M.wt i = w then z i else 0`.
  `HasWt M w z` ("`z` has weight `w`") is `pr M w z = z`.
* `trM φ` (Setting, "transpose"): `Matrix.toLin' (LinearMap.toMatrix' φ)ᵀ`, so that
  `trM φ (δ_k) i = φ (δ_i) k` (`trM_single_apply`).
-/

@[expose] public section

noncomputable section

namespace LemmaW

open DPLattice WeylFilt Finset

variable {A : Type*} [CommRing A]

/-! ### Setting: weight-preserving maps, weight projections, transposes -/

/-- Setting: a linear map `φ : (M.ι → A) → (N.ι → A)` is *weight-preserving* if
`φ (δ_i) j = 0` whenever `M.wt i ≠ N.wt j`. -/
def IsWtPres {M N : DPLattice A} (φ : (M.ι → A) →ₗ[A] (N.ι → A)) : Prop :=
  ∀ i j, M.wt i ≠ N.wt j → φ (Pi.single i 1) j = 0

/-- Setting (auxiliary, raw data): the weight projection attached to a weight function. -/
def prW {ι : Type*} (wt : ι → ℤ) (w : ℤ) : Module.End A (ι → A) where
  toFun z i := if wt i = w then z i else 0
  map_add' z z' := by funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c z := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

@[simp] lemma prW_apply {ι : Type*} (wt : ι → ℤ) (w : ℤ) (z : ι → A) (i : ι) :
    prW (A := A) wt w z i = if wt i = w then z i else 0 := rfl

/-- Setting: the weight projection `pr w` on a DP-lattice `M`:
`(pr M w z) i = if M.wt i = w then z i else 0`. -/
abbrev pr (M : DPLattice A) (w : ℤ) : Module.End A (M.ι → A) := prW M.wt w

lemma pr_apply (M : DPLattice A) (w : ℤ) (z : M.ι → A) (i : M.ι) :
    pr M w z i = if M.wt i = w then z i else 0 := rfl

/-- Setting: the vector `z` *has weight `w`*: `pr w z = z`. -/
def HasWt (M : DPLattice A) (w : ℤ) (z : M.ι → A) : Prop := pr M w z = z

lemma hasWt_iff_inWt (M : DPLattice A) (w : ℤ) (z : M.ι → A) :
    HasWt M w z ↔ InWt M.wt w z := by
  constructor
  · intro h j hj
    have := congrFun h j
    simp only [pr_apply, if_neg hj] at this
    exact this.symm
  · intro h
    funext j
    by_cases hj : M.wt j = w
    · simp [hj]
    · simp [hj, h j hj]

lemma pr_pr (M : DPLattice A) (w : ℤ) (z : M.ι → A) : pr M w (pr M w z) = pr M w z := by
  funext i; simp only [pr_apply]; split_ifs <;> rfl

lemma hasWt_pr (M : DPLattice A) (w : ℤ) (z : M.ι → A) : HasWt M w (pr M w z) :=
  pr_pr M w z

section trM

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- Setting: the transpose `trM φ := Matrix.toLin' (LinearMap.toMatrix' φ)ᵀ` of a linear map
`φ : (ι → A) → (κ → A)`. -/
def trM (φ : (ι → A) →ₗ[A] (κ → A)) : (κ → A) →ₗ[A] (ι → A) :=
  Matrix.toLin' (LinearMap.toMatrix' φ).transpose

/-- Setting: `trM φ (δ_k) i = φ (δ_i) k`. -/
@[simp] lemma trM_single_apply (φ : (ι → A) →ₗ[A] (κ → A)) (k : κ) (i : ι) :
    trM φ (Pi.single k 1) i = φ (Pi.single i 1) k := by
  simp [trM, LinearMap.toMatrix'_apply]

lemma trM_comp (g : (κ → A) →ₗ[A] (μ → A)) (f : (ι → A) →ₗ[A] (κ → A)) :
    trM (g ∘ₗ f) = trM f ∘ₗ trM g := by
  simp [trM, LinearMap.toMatrix'_comp, Matrix.transpose_mul, Matrix.toLin'_mul]

lemma trM_id : trM (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) = LinearMap.id := by
  simp [trM, LinearMap.toMatrix'_id]

lemma trM_trM (φ : (ι → A) →ₗ[A] (κ → A)) : trM (trM φ) = φ := by
  simp [trM]

lemma trM_add (f g : (ι → A) →ₗ[A] (κ → A)) : trM (f + g) = trM f + trM g := by
  simp [trM, Matrix.transpose_add, map_add]

lemma trM_sub (f g : (ι → A) →ₗ[A] (κ → A)) : trM (f - g) = trM f - trM g := by
  simp [trM, Matrix.transpose_sub, map_sub]

lemma trM_zero : trM (0 : (ι → A) →ₗ[A] (κ → A)) = 0 := by
  simp [trM]

/-- C18's `tr` (on endomorphisms) is `trM`. -/
lemma tr_eq_trM (f : Module.End A (ι → A)) : tr f = trM f := rfl

lemma trM_Hop (wt : ι → ℤ) : trM (Hop (A := A) wt) = Hop wt := by
  refine ext_single fun k => ?_
  funext i
  rw [trM_single_apply, Hop_apply, Hop_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

end trM

/-! ### Linear-algebra helpers -/

lemma apply_eq_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → A) →ₗ[A] (κ → A)) (z : ι → A) (j : κ) :
    φ z j = ∑ i, z i * φ (Pi.single i 1) j := by
  conv_lhs => rw [show z = ∑ i, z i • (Pi.single i (1 : A) : ι → A) by
    funext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, Finset.sum_apply]

/-- (P2, auxiliary, raw data) A map shifting weights by `d` intertwines the weight projections
`pr w` and `pr (w + d)`. -/
lemma comm_prW_of_shift {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (wt : ι → ℤ) (wt' : κ → ℤ) (d : ℤ) (φ : (ι → A) →ₗ[A] (κ → A))
    (h : ∀ i j, wt' j ≠ wt i + d → φ (Pi.single i 1) j = 0) (w : ℤ) :
    φ ∘ₗ prW wt w = prW wt' (w + d) ∘ₗ φ := by
  refine ext_single fun i => ?_
  funext j
  simp only [LinearMap.comp_apply, prW_apply]
  have hpr : prW (A := A) wt w (Pi.single i 1) = if wt i = w then Pi.single i 1 else 0 := by
    funext k
    by_cases hk : k = i
    · subst hk; split_ifs <;> simp_all
    · by_cases hi : wt i = w <;> simp [hk, hi]
  rw [hpr]
  by_cases hi : wt i = w
  · rw [if_pos hi]
    by_cases hj : wt' j = w + d
    · rw [if_pos hj]
    · rw [if_neg hj, h i j (by rw [hi]; exact hj)]
  · rw [if_neg hi, map_zero, Pi.zero_apply]
    by_cases hj : wt' j = w + d
    · rw [if_pos hj, h i j (by omega)]
    · rw [if_neg hj]

/-! ### Part P -/

/-- (P1), first step, over any commutative ring: a morphism commutes with `H`, so
`(N.wt j − M.wt i) · f(δ_i) j = 0`. -/
theorem P1_H {M N : DPLattice A} (f : Hom M N) (i : M.ι) (j : N.ι) :
    ((N.wt j - M.wt i : ℤ) : A) * f.toLin (Pi.single i 1) j = 0 := by
  have h := congrFun (LinearMap.congr_fun f.comm_H (Pi.single i 1)) j
  simp only [LinearMap.comp_apply, H, Hop_apply] at h
  have hs : Hop (A := A) M.wt (Pi.single i 1) = (M.wt i : A) • (Pi.single i 1 : M.ι → A) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul] at h
  push_cast; rw [sub_mul, ← h, sub_self]

/-- (P1) Over a domain of characteristic zero, the underlying map of every morphism
`f : Hom M N` is weight-preserving (from `comm_H`: `(N.wt j − M.wt i) · f(δ_i) j = 0`, and
`N.wt j − M.wt i` is a nonzero integer, hence a nonzero element of `A`). -/
theorem P1 [IsDomain A] [CharZero A] {M N : DPLattice A} (f : Hom M N) : IsWtPres f.toLin := by
  intro i j hij
  rcases mul_eq_zero.mp (P1_H f i j) with h3 | h3
  · exfalso
    have : N.wt j - M.wt i = 0 := by exact_mod_cast h3
    omega
  · exact h3

/-- (P2) A weight-preserving `φ` commutes with the weight projections: `φ ∘ pr w = pr w ∘ φ`. -/
theorem P2_wtPres {M N : DPLattice A} {φ : (M.ι → A) →ₗ[A] (N.ι → A)} (hφ : IsWtPres φ)
    (w : ℤ) : φ ∘ₗ pr M w = pr N w ∘ₗ φ := by
  have := comm_prW_of_shift M.wt N.wt 0 φ (fun i j hj => hφ i j (by omega)) w
  simpa using this

/-- (P2) On every DP-lattice, `F^{(r)} ∘ pr w = pr (w − 2r) ∘ F^{(r)}`. -/
theorem P2_F (M : DPLattice A) (r : ℕ) (w : ℤ) :
    M.Fd r ∘ₗ pr M w = pr M (w - 2 * r) ∘ₗ M.Fd r := by
  have := comm_prW_of_shift M.wt M.wt (-(2 * r)) (M.Fd r)
    (fun i j hj => M.isDP.W_F i r j (by omega)) w
  simpa [sub_eq_add_neg] using this

/-- (P2) On every DP-lattice, `E^{(r)} ∘ pr w = pr (w + 2r) ∘ E^{(r)}`. -/
theorem P2_E (M : DPLattice A) (r : ℕ) (w : ℤ) :
    M.Ed r ∘ₗ pr M w = pr M (w + 2 * r) ∘ₗ M.Ed r :=
  comm_prW_of_shift M.wt M.wt (2 * r) (M.Ed r) (fun i j hj => M.isDP.W_E i r j hj) w

/-- (P2) The three statements of (P2) together. -/
theorem P2 :
    (∀ {M N : DPLattice A} {φ : (M.ι → A) →ₗ[A] (N.ι → A)}, IsWtPres φ →
      ∀ w : ℤ, φ ∘ₗ pr M w = pr N w ∘ₗ φ) ∧
    (∀ (M : DPLattice A) (r : ℕ) (w : ℤ), M.Fd r ∘ₗ pr M w = pr M (w - 2 * r) ∘ₗ M.Fd r) ∧
    (∀ (M : DPLattice A) (r : ℕ) (w : ℤ), M.Ed r ∘ₗ pr M w = pr M (w + 2 * r) ∘ₗ M.Ed r) :=
  ⟨fun h w => P2_wtPres h w, P2_F, P2_E⟩

lemma pr_eq_zero_of_noWt (M : DPLattice A) (w : ℤ) (h : ∀ i, M.wt i ≠ w) : pr M w = 0 := by
  ext z i; simp [h i]

/-- (P3) Weights of an extension: if `f : Hom N X`, `g : Hom X Z` is short exact with
`f.toLin`, `g.toLin` weight-preserving, and no basis index of `N` and no basis index of `Z` has
weight `w`, then `pr w = 0` on `X`. -/
theorem P3 {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (hfg : ShortExact f g)
    (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) (w : ℤ) (hN : ∀ i, N.wt i ≠ w)
    (hZ : ∀ k, Z.wt k ≠ w) : pr X w = 0 := by
  refine LinearMap.ext fun y => ?_
  have hgy : g.toLin (pr X w y) = 0 := by
    rw [← LinearMap.comp_apply, P2_wtPres hg, LinearMap.comp_apply,
      pr_eq_zero_of_noWt Z w hZ, LinearMap.zero_apply]
  have hmem : pr X w y ∈ LinearMap.range f.toLin := by
    rw [hfg.exact]; exact hgy
  obtain ⟨n, hn⟩ := hmem
  rw [LinearMap.zero_apply, ← pr_pr, ← hn, ← LinearMap.comp_apply, ← P2_wtPres hf,
    LinearMap.comp_apply, pr_eq_zero_of_noWt N w hN, LinearMap.zero_apply, map_zero]

end LemmaW
