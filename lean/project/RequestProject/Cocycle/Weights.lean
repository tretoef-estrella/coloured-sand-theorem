module

public import RequestProject.Cocycle.Basic

/-!
# `C27_cocycles_and_filtrations.md`: weight lemmas (auxiliary, for Parts G and V)

Auxiliary lemmas for the proof sketch of `C27_cocycles_and_filtrations.md` (namespace
`Cocycle`):

* `wd φ` is the *weight-diagonal part* of a linear map `φ : Lin(M, N)` ((G5) of the file):
  `(wd φ z) j := φ (pr M (N.wt j) z) j`; `wd_eq_sum` shows `wd φ = Σ_w pr N w ∘ φ ∘ pr M w`
  (sum over the weights of `M`).
* weight-preserving linear sections and lifts exist (`exists_wtPres_lift`,
  `exists_wtPres_section`) — "on each weight space separately" (proof sketch);
* `isDP_transport`: the transport of `IsDP` along a weight-preserving intertwiner which hits
  every basis vector by a vector of the same weight ((G4), (G6)(b), (G7));
* `cF_inWt`, `cE_inWt`, `K_cocycle_vec`: the cocycle equations (W) and (K) for vectors of one
  weight.
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-! ### Weight-preserving maps -/

/-- (auxiliary, raw data) a map `φ` with `φ (δ_i) j = 0` for `wt i ≠ wt' j` sends vectors of
weight `w` to vectors of weight `w`. -/
lemma inWt_map_raw {ι κ : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ} {wt' : κ → ℤ}
    (φ : (ι → A) →ₗ[A] (κ → A)) (hφ : ∀ i j, wt i ≠ wt' j → φ (Pi.single i 1) j = 0)
    {w : ℤ} {v : ι → A} (hv : InWt wt w v) : InWt wt' w (φ v) := by
  intro j hj
  rw [apply_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : wt i = w
  · rw [hφ i j (by rw [hi]; exact Ne.symm hj), mul_zero]
  · rw [hv i hi, zero_mul]

variable {M N P : DPLattice A}

lemma inWt_map {φ : Lin M N} (hφ : IsWtPres φ) {w : ℤ} {v : M.ι → A} (hv : InWt M.wt w v) :
    InWt N.wt w (φ v) := inWt_map_raw φ hφ hv

/-- (auxiliary) a linear map commuting with all weight projections is weight-preserving. -/
lemma isWtPres_of_comm_pr {φ : Lin M N} (h : ∀ w, φ ∘ₗ pr M w = pr N w ∘ₗ φ) : IsWtPres φ := by
  intro i j hij
  have := congrFun (LinearMap.congr_fun (h (N.wt j)) (Pi.single i 1)) j
  simp only [LinearMap.comp_apply, pr_apply, ↓reduceIte] at this
  rw [← this]
  have : pr M (N.wt j) (Pi.single i (1 : A)) = 0 := by
    funext k
    simp only [pr_apply, Pi.zero_apply]
    split_ifs with hk
    · by_cases hki : k = i
      · subst hki; exact absurd hk hij
      · simp [hki]
    · rfl
  rw [this, map_zero, Pi.zero_apply]

lemma isWtPres_iff {φ : Lin M N} : IsWtPres φ ↔ ∀ w, φ ∘ₗ pr M w = pr N w ∘ₗ φ :=
  ⟨fun h w => P2_wtPres h w, isWtPres_of_comm_pr⟩

lemma isWtPres_comp {g : Lin N P} {f : Lin M N} (hg : IsWtPres g) (hf : IsWtPres f) :
    IsWtPres (g ∘ₗ f) := isWtPres_of_comm_pr fun w => by
  rw [LinearMap.comp_assoc, P2_wtPres hf, ← LinearMap.comp_assoc, P2_wtPres hg,
    LinearMap.comp_assoc]

lemma isWtPres_id : IsWtPres (LinearMap.id : Lin M M) := fun i j hij => by
  have : j ≠ i := fun h => hij (h ▸ rfl)
  simp [this]

lemma isWtPres_zero : IsWtPres (0 : Lin M N) := fun _ _ _ => rfl

lemma isWtPres_add {f g : Lin M N} (hf : IsWtPres f) (hg : IsWtPres g) : IsWtPres (f + g) :=
  fun i j hij => by simp [hf i j hij, hg i j hij]

lemma isWtPres_sub {f g : Lin M N} (hf : IsWtPres f) (hg : IsWtPres g) : IsWtPres (f - g) :=
  fun i j hij => by simp [hf i j hij, hg i j hij]

lemma isWtPres_neg {f : Lin M N} (hf : IsWtPres f) : IsWtPres (-f) :=
  fun i j hij => by simp [hf i j hij]

/-- (G5, auxiliary) a weight-preserving map commutes with `H`. -/
lemma comm_H_of_isWtPres {ψ : Lin M N} (hψ : IsWtPres ψ) : ψ ∘ₗ H M = H N ∘ₗ ψ := by
  refine ext_single fun i => ?_
  funext j
  have hs : Hop (A := A) M.wt (Pi.single i 1) = (M.wt i : A) • (Pi.single i 1 : M.ι → A) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp only [LinearMap.comp_apply, H, hs, map_smul, Pi.smul_apply, smul_eq_mul, Hop_apply]
  by_cases h : M.wt i = N.wt j
  · rw [h]
  · rw [hψ i j h, mul_zero, mul_zero]

/-- (G7, V2, auxiliary) if `f` is injective and weight-preserving and `f ∘ ρ = id − σ ∘ g` with
`σ`, `g` weight-preserving, then `ρ` is weight-preserving. -/
lemma isWtPres_retraction {X : DPLattice A} {f : Lin N X} {g : Lin X M} {σ : Lin M X}
    {ρ : Lin X N} (hinj : Function.Injective f) (hf : IsWtPres f) (hg : IsWtPres g)
    (hσ : IsWtPres σ) (hfρ : f ∘ₗ ρ = LinearMap.id - σ ∘ₗ g) : IsWtPres ρ := by
  refine isWtPres_of_comm_pr fun w => LinearMap.ext fun x => hinj ?_
  have h1 : ∀ v, f (ρ v) = v - σ (g v) := fun v => by
    simpa using LinearMap.congr_fun hfρ v
  have hsg := P2_wtPres (isWtPres_comp hσ hg) w
  have hf' := P2_wtPres hf w
  simp only [LinearMap.comp_apply]
  rw [h1, ← LinearMap.comp_apply f (pr N w), hf', LinearMap.comp_apply, h1, map_sub]
  congr 1
  exact LinearMap.congr_fun hsg x

/-! ### The weight-diagonal part -/

/-- (G5) The weight-diagonal part `wd φ` of `φ : Lin(M, N)`: `(wd φ z) j := φ (pr M (N.wt j) z) j`
(equal to `Σ_w pr N w ∘ φ ∘ pr M w`, see `wd_eq_sum`). -/
def wd (φ : Lin M N) : Lin M N where
  toFun z j := φ (pr M (N.wt j) z) j
  map_add' z z' := by funext j; simp
  map_smul' t z := by funext j; simp

lemma wd_apply (φ : Lin M N) (z : M.ι → A) (j : N.ι) : wd φ z j = φ (pr M (N.wt j) z) j := rfl

/-- (G5) `wd φ = Σ_w pr N w ∘ φ ∘ pr M w`, the sum over the weights `w` of `M`. -/
lemma wd_eq_sum (φ : Lin M N) :
    wd φ = ∑ w ∈ univ.image M.wt, pr N w ∘ₗ φ ∘ₗ pr M w := by
  refine LinearMap.ext fun z => funext fun j => ?_
  rw [wd_apply, LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.comp_apply, pr_apply]
  by_cases hj : N.wt j ∈ univ.image M.wt
  · rw [Finset.sum_eq_single (N.wt j)]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · have : pr M (N.wt j) z = 0 := by
        funext k
        simp only [pr_apply, Pi.zero_apply]
        rw [if_neg]
        intro hk; exact hj (Finset.mem_image.mpr ⟨k, mem_univ _, hk⟩)
      rw [this, map_zero, Pi.zero_apply]
    · intro b hb
      rw [if_neg]
      intro h; exact hj (h ▸ hb)

lemma pr_wd (φ : Lin M N) (u : ℤ) : pr N u ∘ₗ wd φ = pr N u ∘ₗ φ ∘ₗ pr M u := by
  refine LinearMap.ext fun z => funext fun j => ?_
  simp only [LinearMap.comp_apply, pr_apply, wd_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- (G5) the weight-diagonal part is weight-preserving. -/
lemma wd_isWtPres (φ : Lin M N) : IsWtPres (wd φ) := by
  intro i j hij
  rw [wd_apply]
  have : pr M (N.wt j) (Pi.single i (1 : A)) = 0 := by
    funext k
    simp only [pr_apply, Pi.zero_apply]
    split_ifs with hk
    · by_cases hki : k = i
      · subst hki; exact absurd hk hij
      · simp [hki]
    · rfl
  rw [this, map_zero, Pi.zero_apply]

lemma wd_of_isWtPres {φ : Lin M N} (hφ : IsWtPres φ) : wd φ = φ := by
  refine LinearMap.ext fun z => funext fun j => ?_
  rw [wd_apply, ← LinearMap.comp_apply φ, P2_wtPres hφ, LinearMap.comp_apply, pr_apply,
    if_pos rfl]

lemma apply_eq_pr (N : DPLattice A) (y : N.ι → A) (j : N.ι) : y j = pr N (N.wt j) y j := by
  rw [pr_apply, if_pos rfl]

lemma comp_wd {g : Lin N P} (hg : IsWtPres g) (φ : Lin M N) : g ∘ₗ wd φ = wd (g ∘ₗ φ) := by
  refine LinearMap.ext fun z => funext fun k => ?_
  have e1 := LinearMap.congr_fun (P2_wtPres hg (P.wt k)) (wd φ z)
  have e2 := LinearMap.congr_fun (pr_wd φ (P.wt k)) z
  have e3 := LinearMap.congr_fun (P2_wtPres hg (P.wt k)) (φ (pr M (P.wt k) z))
  simp only [LinearMap.comp_apply] at e1 e2 e3
  rw [LinearMap.comp_apply, apply_eq_pr P (g (wd φ z)) k, ← e1, e2, e3, wd_apply,
    LinearMap.comp_apply, pr_apply, if_pos rfl]

lemma wd_comp {g : Lin P M} (hg : IsWtPres g) (φ : Lin M N) : wd φ ∘ₗ g = wd (φ ∘ₗ g) := by
  refine LinearMap.ext fun z => funext fun k => ?_
  show φ (pr M _ (g z)) k = φ (g (pr P _ z)) k
  rw [← LinearMap.comp_apply (pr M _) g, ← P2_wtPres hg]
  rfl

/-! ### Weight-preserving lifts and sections -/

/-- Proof sketch ("weight-preserving linear sections and lifts exist"): if `g : Lin(N, N')` is
surjective and weight-preserving and `ψ' : Lin(M, N')` is weight-preserving, there is a
weight-preserving `ψ : Lin(M, N)` with `g ∘ ψ = ψ'`. -/
theorem exists_wtPres_lift {N' : DPLattice A} {g : Lin N N'} (hg : Function.Surjective g)
    (hgw : IsWtPres g) {ψ' : Lin M N'} (hψ' : IsWtPres ψ') :
    ∃ ψ : Lin M N, IsWtPres ψ ∧ g ∘ₗ ψ = ψ' := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g ψ' hg
  exact ⟨wd h, wd_isWtPres h, by rw [comp_wd hgw, hh, wd_of_isWtPres hψ']⟩

/-- Proof sketch: a surjective weight-preserving `g : Lin(X, M)` has a weight-preserving linear
section. -/
theorem exists_wtPres_section {X : DPLattice A} {g : Lin X M} (hg : Function.Surjective g)
    (hgw : IsWtPres g) : ∃ σ : Lin M X, IsWtPres σ ∧ g ∘ₗ σ = LinearMap.id :=
  exists_wtPres_lift hg hgw isWtPres_id

/-! ### Transport of `IsDP` -/

/-- (G4, G6, G7, auxiliary) Transport of `IsDP`: if `φ : (X.ι → A) → (κ → A)` is
weight-preserving (`φ (δ_i) k = 0` for `X.wt i ≠ wt' k`), intertwines the operators of the
DP-lattice `X` with raw data `(wt', Fd', Ed')`, and every basis vector `δ_k` of `κ` is the image
of a vector of `X` of weight `wt' k`, then the raw data satisfy `IsDP`. -/
theorem isDP_transport (X : DPLattice A) {κ : Type*} [Fintype κ] [DecidableEq κ]
    {wt' : κ → ℤ} {Fd' Ed' : ℕ → Module.End A (κ → A)} (φ : (X.ι → A) →ₗ[A] (κ → A))
    (hφw : ∀ i k, X.wt i ≠ wt' k → φ (Pi.single i 1) k = 0)
    (hF : ∀ r, φ ∘ₗ X.Fd r = Fd' r ∘ₗ φ) (hE : ∀ r, φ ∘ₗ X.Ed r = Ed' r ∘ₗ φ)
    (hsurj : ∀ k, ∃ v, InWt X.wt (wt' k) v ∧ φ v = Pi.single k 1) :
    IsDP wt' Fd' Ed' := by
  have hF' : ∀ r v, φ (X.Fd r v) = Fd' r (φ v) := fun r v => LinearMap.congr_fun (hF r) v
  have hE' : ∀ r v, φ (X.Ed r v) = Ed' r (φ v) := fun r v => LinearMap.congr_fun (hE r) v
  refine ⟨fun k r j hj => ?_, fun k r j hj => ?_, ?_, ?_, fun a b => ?_, fun a b => ?_,
    fun k r s => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := hsurj k
    rw [← hv', ← hF']
    exact inWt_map_raw φ hφw (X.isDP.inWt_Fd r hv) j hj
  · obtain ⟨v, hv, hv'⟩ := hsurj k
    rw [← hv', ← hE']
    exact inWt_map_raw φ hφw (X.isDP.inWt_Ed r hv) j hj
  · refine ext_single fun k => ?_
    obtain ⟨v, -, hv⟩ := hsurj k
    rw [← hv, ← hF', X.isDP.P0_F]; rfl
  · refine ext_single fun k => ?_
    obtain ⟨v, -, hv⟩ := hsurj k
    rw [← hv, ← hE', X.isDP.P0_E]; rfl
  · refine ext_single fun k => ?_
    obtain ⟨v, -, hv⟩ := hsurj k
    rw [← hv, LinearMap.comp_apply, ← hF', ← hF', LinearMap.smul_apply, ← hF', ← map_smul,
      ← LinearMap.smul_apply, ← X.isDP.P1_F]
    rfl
  · refine ext_single fun k => ?_
    obtain ⟨v, -, hv⟩ := hsurj k
    rw [← hv, LinearMap.comp_apply, ← hE', ← hE', LinearMap.smul_apply, ← hE', ← map_smul,
      ← LinearMap.smul_apply, ← X.isDP.P1_E]
    rfl
  · obtain ⟨v, hv, hv'⟩ := hsurj k
    rw [← hv', ← hF', ← hE', K_vec X hv, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hF', hE']

/-! ### Cocycle equations at vectors of one weight -/

lemma elim_inWt {u : N.ι → A} {v : M.ι → A} {w : ℤ} (hu : InWt N.wt w u) (hv : InWt M.wt w v) :
    InWt (gwt M N) w (Sum.elim u v) := by
  intro x hx
  cases x with
  | inl x => exact hu x hx
  | inr x => exact hv x hx

/-- (G2, W) at vectors: for a cocycle, `cF r` sends vectors of weight `w` to vectors of weight
`w − 2r`. -/
lemma cF_inWt {c : Pair M N} (hc : IsCocycle c) (r : ℕ) {w : ℤ} {v : M.ι → A}
    (hv : InWt M.wt w v) : InWt N.wt (w - 2 * r) (c.1 r v) := by
  intro j hj
  have := (glue M N c hc).isDP.inWt_Fd r (elim_inWt (inWt_zero (wt := N.wt)) hv) (Sum.inl j) hj
  simpa [glue] using this

/-- (G2, W) at vectors: for a cocycle, `cE r` sends vectors of weight `w` to vectors of weight
`w + 2r`. -/
lemma cE_inWt {c : Pair M N} (hc : IsCocycle c) (r : ℕ) {w : ℤ} {v : M.ι → A}
    (hv : InWt M.wt w v) : InWt N.wt (w + 2 * r) (c.2 r v) := by
  intro j hj
  have := (glue M N c hc).isDP.inWt_Ed r (elim_inWt (inWt_zero (wt := N.wt)) hv) (Sum.inl j) hj
  simpa [glue] using this

/-- (G2, K) at vectors: the cocycle equation (K) for a vector `v` of weight `w`. -/
lemma K_cocycle_vec {c : Pair M N} (hc : IsCocycle c) {w : ℤ} {v : M.ι → A}
    (hv : InWt M.wt w v) (r s : ℕ) :
    N.Ed s (c.1 r v) + c.2 s (M.Fd r v) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (w + s - r) j : ℤ) : A) •
        (N.Fd (r - j) (c.2 (s - j) v) + c.1 (r - j) (M.Ed (s - j) v)) := by
  have := K_vec (glue M N c hc) (elim_inWt (inWt_zero (wt := N.wt)) hv) r s
  simp only [glue, gF_elim, gE_elim, map_zero, zero_add, elim_smul, elim_sum,
    elim_eq_iff] at this
  exact this.1

end Cocycle
