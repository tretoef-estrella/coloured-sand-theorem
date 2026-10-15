module

public import RequestProject.Filt.PartI

/-!
# `C29_filtrations_and_dance_lattices.md`: Part E — extensions

Encodings (namespace `Filt`):

* A short exact sequence is C19's `ShortExact f g`; "weight-preserving" is C25's `IsWtPres` on
  the underlying linear maps; the filtrations are C27's `HasDeltaFilt`, `HasNablaFilt`.
* In the proof of (E1), the sub-lattice `K` of (S1) has basis `M'.ι ⊕ Q'.ι` (a vector is
  `Sum.elim u v`), `j (u, v) = f u + σ (f' v)` (C27's `thetaInvL`) and
  `p x = (ρ (x − σ (f' (ρ' (g x)))), ρ' (g x))` (C27's `thetaL`), with `σ, ρ` and `σ', ρ'` given
  by C27 (G7). In the proof of (E2), the quotient lattice of (S2) has basis `N₁.ι ⊕ N''.ι`,
  `q x = (g₁ (ρ x), g x)` and `s (u, v) = f (σ₁ u) + σ v`.
* `inlL x = Sum.elim x 0` and `sndL z = z ∘ Sum.inr` are C22's maps.
-/

@[expose] public section

noncomputable section

namespace Filt

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

variable {A : Type*} [CommRing A]

/-! ### Auxiliary facts -/

section aux

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- (auxiliary) `0 → (ι → A) → (ι ⊕ κ → A) → (κ → A) → 0` (`inlL`, `sndL`) is exact. -/
lemma inlL_sndL_exact :
    Function.Injective (Lemma35.inlL : (ι → A) →ₗ[A] (ι ⊕ κ → A)) ∧
    Function.Surjective (Lemma35.sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A)) ∧
    LinearMap.range (Lemma35.inlL : (ι → A) →ₗ[A] (ι ⊕ κ → A)) =
      LinearMap.ker (Lemma35.sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A)) := by
  refine ⟨fun x y h => congrArg (· ∘ Sum.inl) h, fun v => ⟨Sum.elim 0 v, rfl⟩, ?_⟩
  ext z
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩; rfl
  · intro hz
    refine ⟨z ∘ Sum.inl, ?_⟩
    change Sum.elim (z ∘ Sum.inl) 0 = z
    rw [← elim_comp z]
    change Sum.elim (z ∘ Sum.inl) (0 : κ → A) = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)
    rw [show z ∘ Sum.inr = 0 from hz]

omit [DecidableEq κ] in
/-- (auxiliary) `inlL` is weight-preserving for the weights `wt₁` and `Sum.elim wt₁ wt₂`. -/
lemma inlL_wt (wt₁ : ι → ℤ) (wt₂ : κ → ℤ) :
    ∀ i k, wt₁ i ≠ Sum.elim wt₁ wt₂ k →
      (Lemma35.inlL : (ι → A) →ₗ[A] (ι ⊕ κ → A)) (Pi.single i 1) k = 0 := by
  intro i k h
  cases k with
  | inl k =>
    have : k ≠ i := fun e => h (e ▸ rfl)
    change (Pi.single i (1 : A) : ι → A) k = 0
    simp [this]
  | inr k => rfl

/-- (auxiliary) `sndL` is weight-preserving for the weights `Sum.elim wt₁ wt₂` and `wt₂`. -/
lemma sndL_wt (wt₁ : ι → ℤ) (wt₂ : κ → ℤ) :
    ∀ k i, Sum.elim wt₁ wt₂ k ≠ wt₂ i →
      (Lemma35.sndL : (ι ⊕ κ → A) →ₗ[A] (κ → A)) (Pi.single k 1) i = 0 := by
  intro k i h
  cases k with
  | inl k => change (Pi.single (Sum.inl k) (1 : A) : ι ⊕ κ → A) (Sum.inr i) = 0; simp
  | inr k =>
    have : i ≠ k := fun e => h (e ▸ rfl)
    change (Pi.single (Sum.inr k) (1 : A) : ι ⊕ κ → A) (Sum.inr i) = 0
    simp [this]

variable {X Y Z : DPLattice A}

/-- (auxiliary) a bijective weight-preserving morphism is an isomorphism with weight-preserving
underlying maps (the inverse is weight-preserving by C28 `isWtPres_inverse`). -/
lemma exists_iso_of_bij (f : Hom X Y) (hi : Function.Injective f.toLin)
    (hs : Function.Surjective f.toLin) (hf : IsWtPres f.toLin) :
    ∃ e : Iso X Y, IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin := by
  let L := LinearEquiv.ofBijective f.toLin ⟨hi, hs⟩
  have h1 : (L.symm : (Y.ι → A) →ₗ[A] (X.ι → A)) ∘ₗ f.toLin = LinearMap.id :=
    LinearMap.ext fun x => L.symm_apply_apply x
  have h2 : f.toLin ∘ₗ (L.symm : (Y.ι → A) →ₗ[A] (X.ι → A)) = LinearMap.id :=
    LinearMap.ext fun y => L.apply_symm_apply y
  exact ⟨Iso.ofInverse f _ h1 h2, hf, Lift2.isWtPres_inverse hf h1 h2⟩

lemma ShortExact.comp_zero {f : Hom X Y} {g : Hom Y Z} (h : ShortExact f g) (x : X.ι → A) :
    g.toLin (f.toLin x) = 0 := by
  rw [← LinearMap.mem_ker, ← h.exact]; exact ⟨x, rfl⟩

lemma ShortExact.mem_range {f : Hom X Y} {g : Hom Y Z} (h : ShortExact f g) {y : Y.ι → A}
    (hy : g.toLin y = 0) : ∃ x, f.toLin x = y := by
  rw [← LinearMap.mem_ker, ← h.exact] at hy; exact hy

end aux

/-! ### (E1) -/

section E1

variable {M' M Q Q' : DPLattice A}

/-- (E1, base case) if `Q.ι` is empty, `f` is bijective, so `M ≅ M'`. -/
lemma E1_base {f : Hom M' M} {g : Hom M Q} (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hQ : IsEmpty Q.ι) (hM' : HasDeltaFilt M') : HasDeltaFilt M := by
  have hs : Function.Surjective f.toLin := fun y =>
    ShortExact.mem_range h (Subsingleton.elim _ _)
  obtain ⟨e, he, he'⟩ := exists_iso_of_bij f h.inj hs hf
  exact I1_delta e he he' hM'

/-- (E1, induction step) the construction of the sketch: the sub-lattice `K = g⁻¹(range f')` of
(S1), the sequences `M' → K → Q'` and `K → M → delta A l`. -/
lemma E1_step {l : ℕ} {f : Hom M' M} {g : Hom M Q} (hfg : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (f' : Hom Q' Q) (g' : Hom Q (delta A l)) (hfg' : ShortExact f' g')
    (hf' : IsWtPres f'.toLin) (hg' : IsWtPres g'.toLin)
    (IH : ∀ {M'' K : DPLattice A} (a : Hom M'' K) (b : Hom K Q'), ShortExact a b →
      IsWtPres a.toLin → IsWtPres b.toLin → HasDeltaFilt M'' → HasDeltaFilt K)
    (hM' : HasDeltaFilt M') : HasDeltaFilt M := by
  obtain ⟨σ, ρ, hσw, hρw, hgσ, hρf, -, -⟩ := G7 hfg hf hg
  obtain ⟨σ', ρ', -, hρ'w, -, hρ'f', -, -⟩ := G7 hfg' hf' hg'
  have hgσ' : ∀ v, g.toLin (σ v) = v := fun v => LinearMap.congr_fun hgσ v
  have hρf'' : ∀ u, ρ (f.toLin u) = u := fun u => LinearMap.congr_fun hρf u
  have hρ'f'' : ∀ u, ρ' (f'.toLin u) = u := fun u => LinearMap.congr_fun hρ'f' u
  let wK : M'.ι ⊕ Q'.ι → ℤ := Sum.elim M'.wt Q'.wt
  let jL : (M'.ι ⊕ Q'.ι → A) →ₗ[A] (M.ι → A) := thetaInvL f.toLin (σ ∘ₗ f'.toLin)
  let pL : (M.ι → A) →ₗ[A] (M'.ι ⊕ Q'.ι → A) :=
    thetaL (ρ ∘ₗ (LinearMap.id - σ ∘ₗ f'.toLin ∘ₗ ρ' ∘ₗ g.toLin)) (ρ' ∘ₗ g.toLin)
  have hj_elim : ∀ u v, jL (Sum.elim u v) = f.toLin u + σ (f'.toLin v) := fun _ _ => rfl
  have hg_j : ∀ u v, g.toLin (jL (Sum.elim u v)) = f'.toLin v := fun u v => by
    rw [hj_elim, map_add, ShortExact.comp_zero hfg, hgσ', zero_add]
  have hpj : pL ∘ₗ jL = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    rw [← elim_comp z]
    change Sum.elim (ρ (jL _ - σ (f'.toLin (ρ' (g.toLin (jL _))))))
      (ρ' (g.toLin (jL _))) = _
    rw [hg_j, hρ'f'', hj_elim, add_sub_cancel_right, hρf'']
    rfl
  have hj : ∀ k i, wK k ≠ M.wt i → jL (Pi.single k 1) i = 0 := by
    intro k i h
    cases k with
    | inl k => rw [single_inl, hj_elim, map_zero, map_zero, add_zero]; exact hf k i h
    | inr k =>
      rw [single_inr, hj_elim, map_zero, zero_add]
      exact isWtPres_comp hσw hf' k i h
  have hp : ∀ i k, M.wt i ≠ wK k → pL (Pi.single i 1) k = 0 := by
    intro i k h
    cases k with
    | inl k =>
      exact isWtPres_comp hρw (isWtPres_sub isWtPres_id (isWtPres_comp hσw
        (isWtPres_comp hf' (isWtPres_comp hρ'w hg)))) i k h
    | inr k => exact isWtPres_comp hρ'w hg i k h
  have hrange : ∀ y, y ∈ LinearMap.range jL ↔ g.toLin y ∈ LinearMap.range f'.toLin := by
    intro y
    constructor
    · rintro ⟨z, rfl⟩
      rw [← elim_comp z, hg_j]; exact ⟨_, rfl⟩
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ := ShortExact.mem_range hfg (y := y - σ (f'.toLin v))
        (by rw [map_sub, hgσ', hv, sub_self])
      exact ⟨Sum.elim u v, by rw [hj_elim, hu, sub_add_cancel]⟩
  have hF : ∀ r x, M.Fd r (jL x) ∈ LinearMap.range jL := by
    intro r x
    rw [hrange]
    obtain ⟨v, hv⟩ := (hrange (jL x)).1 ⟨x, rfl⟩
    refine ⟨Q'.Fd r v, ?_⟩
    rw [← LinearMap.comp_apply g.toLin, g.comm_F, LinearMap.comp_apply, ← hv,
      ← LinearMap.comp_apply _ f'.toLin, ← f'.comm_F, LinearMap.comp_apply]
  have hE : ∀ r x, M.Ed r (jL x) ∈ LinearMap.range jL := by
    intro r x
    rw [hrange]
    obtain ⟨v, hv⟩ := (hrange (jL x)).1 ⟨x, rfl⟩
    refine ⟨Q'.Ed r v, ?_⟩
    rw [← LinearMap.comp_apply g.toLin, g.comm_E, LinearMap.comp_apply, ← hv,
      ← LinearMap.comp_apply _ f'.toLin, ← f'.comm_E, LinearMap.comp_apply]
  let K := sub M wK jL pL hpj hj hp hF hE
  let J : Hom K M := subHom M wK jL pL hpj hj hp hF hE
  have hJinj : Function.Injective J.toLin := fun x y hxy => by
    have := congrArg pL hxy
    change pL (jL x) = pL (jL y) at this
    rwa [← LinearMap.comp_apply pL, hpj, ← LinearMap.comp_apply pL, hpj] at this
  obtain ⟨e1, e2, e3⟩ := inlL_sndL_exact (A := A) (ι := M'.ι) (κ := Q'.ι)
  let a : Hom M' K := Hom.liftInj Lemma35.inlL J hJinj f (LinearMap.ext fun u => by
    change jL (Sum.elim u 0) = f.toLin u
    rw [hj_elim, map_zero, map_zero, add_zero])
  let b : Hom K Q' := Hom.liftInj Lemma35.sndL f' hfg'.inj (Hom.comp g J)
    (LinearMap.ext fun z => by
      change f'.toLin (z ∘ Sum.inr) = g.toLin (jL z)
      rw [← elim_comp z, hg_j]; rfl)
  have hK : HasDeltaFilt K := IH a b ⟨e1, e2, e3⟩ (inlL_wt M'.wt Q'.wt) (sndL_wt M'.wt Q'.wt) hM'
  refine HasDeltaFilt.step J (Hom.comp g' g) ⟨hJinj, ?_, ?_⟩ hj (isWtPres_comp hg' hg) hK
  · exact hfg'.surj.comp hfg.surj
  · ext y
    change y ∈ LinearMap.range jL ↔ g'.toLin (g.toLin y) = 0
    rw [hrange, ← LinearMap.mem_ker, ← hfg'.exact]

/-- (E1) **Extensions of `Δ`-filtered lattices.** If `f : Hom M' M`, `g : Hom M Q` are short
exact and weight-preserving, `HasDeltaFilt M'` and `HasDeltaFilt Q`, then `HasDeltaFilt M`
(induction on `HasDeltaFilt Q`, as in the sketch). -/
theorem E1 (f : Hom M' M) (g : Hom M Q) (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (hM' : HasDeltaFilt M') (hQ : HasDeltaFilt Q) : HasDeltaFilt M := by
  induction hQ generalizing M' M with
  | base hQ => exact E1_base h hf hQ hM'
  | step f' g' hfg' hf' hg' _ IH =>
    exact E1_step h hf hg f' g' hfg' hf' hg' (fun a b hab ha hb hM'' => IH a b hab ha hb hM'') hM'

end E1

/-! ### (E2) -/

section E2

variable {N' N N'' N₁ : DPLattice A}

/-- (E2, base case) if `N'.ι` is empty, `g` is bijective, so `N ≅ N''`. -/
lemma E2_base {f : Hom N' N} {g : Hom N N''} (h : ShortExact f g) (hg : IsWtPres g.toLin)
    (hN' : IsEmpty N'.ι) (hN'' : HasNablaFilt N'') : HasNablaFilt N := by
  have hi : Function.Injective g.toLin := by
    rw [← LinearMap.ker_eq_bot, ← h.exact, LinearMap.range_eq_bot]
    exact Subsingleton.elim _ _
  obtain ⟨e, he, he'⟩ := exists_iso_of_bij g hi h.surj hg
  exact I1_nabla e.symm he' he hN''

/-- (E2, induction step) the construction dual to (E1): the quotient lattice `N / f(f₁(∇(m)))`
of (S2), the sequences `N₁ → N / f(f₁(∇(m))) → N''` and `∇(m) → N → N / f(f₁(∇(m)))`. -/
lemma E2_step {m : ℕ} {f : Hom N' N} {g : Hom N N''} (hfg : ShortExact f g)
    (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) (f₁ : Hom (nabla A m) N') (g₁ : Hom N' N₁)
    (hfg₁ : ShortExact f₁ g₁) (hf₁ : IsWtPres f₁.toLin) (hg₁ : IsWtPres g₁.toLin)
    (IH : ∀ {X N₂ : DPLattice A} (c : Hom N₁ X) (d : Hom X N₂), ShortExact c d →
      IsWtPres c.toLin → IsWtPres d.toLin → HasNablaFilt N₂ → HasNablaFilt X)
    (hN'' : HasNablaFilt N'') : HasNablaFilt N := by
  obtain ⟨σ, ρ, hσw, hρw, hgσ, hρf, hfρ, -⟩ := G7 hfg hf hg
  obtain ⟨σ₁, ρ₁, hσ₁w, -, hg₁σ₁, -, -, -⟩ := G7 hfg₁ hf₁ hg₁
  have hgσ' : ∀ v, g.toLin (σ v) = v := fun v => LinearMap.congr_fun hgσ v
  have hρf' : ∀ u, ρ (f.toLin u) = u := fun u => LinearMap.congr_fun hρf u
  have hg₁σ₁' : ∀ u, g₁.toLin (σ₁ u) = u := fun u => LinearMap.congr_fun hg₁σ₁ u
  have hρσ : ∀ v, ρ (σ v) = 0 := fun v => by
    apply hfg.inj
    have := LinearMap.congr_fun hfρ (σ v)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hgσ',
      sub_self] at this
    rw [this, map_zero]
  let wK : N₁.ι ⊕ N''.ι → ℤ := Sum.elim N₁.wt N''.wt
  let qL : (N.ι → A) →ₗ[A] (N₁.ι ⊕ N''.ι → A) := thetaL (g₁.toLin ∘ₗ ρ) g.toLin
  let sL : (N₁.ι ⊕ N''.ι → A) →ₗ[A] (N.ι → A) := thetaInvL (f.toLin ∘ₗ σ₁) σ
  have hq_apply : ∀ x, qL x = Sum.elim (g₁.toLin (ρ x)) (g.toLin x) := fun _ => rfl
  have hs_elim : ∀ u v, sL (Sum.elim u v) = f.toLin (σ₁ u) + σ v := fun _ _ => rfl
  have hqs : qL ∘ₗ sL = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    rw [← elim_comp z]
    change qL (sL _) = _
    simp only [hs_elim, hq_apply, map_add, hρf', hρσ, add_zero, hg₁σ₁',
      ShortExact.comp_zero hfg, hgσ', zero_add]
    rfl
  have hq : ∀ i k, N.wt i ≠ wK k → qL (Pi.single i 1) k = 0 := by
    intro i k h
    cases k with
    | inl k => exact isWtPres_comp hg₁ hρw i k h
    | inr k => exact hg i k h
  have hs : ∀ k i, wK k ≠ N.wt i → sL (Pi.single k 1) i = 0 := by
    intro k i h
    cases k with
    | inl k =>
      rw [single_inl, hs_elim, map_zero, add_zero]
      exact isWtPres_comp hf hσ₁w k i h
    | inr k => rw [single_inr, hs_elim, map_zero, map_zero, zero_add]; exact hσw k i h
  have hker : ∀ x, x ∈ LinearMap.ker qL ↔ ∃ z, f.toLin (f₁.toLin z) = x := by
    intro x
    rw [LinearMap.mem_ker, hq_apply]
    constructor
    · intro hx
      rw [← Sum.elim_zero_zero, elim_eq_iff] at hx
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨y, rfl⟩ := ShortExact.mem_range hfg h2
      rw [hρf'] at h1
      obtain ⟨z, rfl⟩ := ShortExact.mem_range hfg₁ h1
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      rw [hρf', ShortExact.comp_zero hfg₁, ShortExact.comp_zero hfg, Sum.elim_zero_zero]
  have hF : ∀ r x, x ∈ LinearMap.ker qL → N.Fd r x ∈ LinearMap.ker qL := by
    intro r x hx
    obtain ⟨z, rfl⟩ := (hker x).1 hx
    rw [hker]
    refine ⟨(nabla A m).Fd r z, ?_⟩
    rw [← LinearMap.comp_apply f₁.toLin, f₁.comm_F, LinearMap.comp_apply,
      ← LinearMap.comp_apply f.toLin, f.comm_F, LinearMap.comp_apply]
  have hE : ∀ r x, x ∈ LinearMap.ker qL → N.Ed r x ∈ LinearMap.ker qL := by
    intro r x hx
    obtain ⟨z, rfl⟩ := (hker x).1 hx
    rw [hker]
    refine ⟨(nabla A m).Ed r z, ?_⟩
    rw [← LinearMap.comp_apply f₁.toLin, f₁.comm_E, LinearMap.comp_apply,
      ← LinearMap.comp_apply f.toLin, f.comm_E, LinearMap.comp_apply]
  let X := quot N wK qL sL hqs hq hs hF hE
  let P : Hom N X := quotHom N wK qL sL hqs hq hs hF hE
  have hPs : Function.Surjective P.toLin := fun z =>
    ⟨sL z, by change qL (sL z) = z; rw [← LinearMap.comp_apply qL, hqs, LinearMap.id_apply]⟩
  obtain ⟨e1, e2, e3⟩ := inlL_sndL_exact (A := A) (ι := N₁.ι) (κ := N''.ι)
  let c : Hom N₁ X := Hom.descSurj Lemma35.inlL g₁ hfg₁.surj (Hom.comp P f)
    (LinearMap.ext fun y => by
      change Sum.elim (g₁.toLin y) 0 = qL (f.toLin y)
      rw [hq_apply, hρf', ShortExact.comp_zero hfg])
  let d : Hom X N'' := Hom.descSurj Lemma35.sndL P hPs g (LinearMap.ext fun y => rfl)
  have hX : HasNablaFilt X :=
    IH c d ⟨e1, e2, e3⟩ (inlL_wt N₁.wt N''.wt) (sndL_wt N₁.wt N''.wt) hN''
  refine HasNablaFilt.step (Hom.comp f f₁) P ⟨hfg.inj.comp hfg₁.inj, hPs, ?_⟩
    (isWtPres_comp hf hf₁) hq hX
  ext x
  change x ∈ LinearMap.range (f.toLin ∘ₗ f₁.toLin) ↔ x ∈ LinearMap.ker qL
  rw [hker]
  rfl

/-- (E2) **Extensions of `∇`-filtered lattices.** If `f : Hom N' N`, `g : Hom N N''` are short
exact and weight-preserving, `HasNablaFilt N'` and `HasNablaFilt N''`, then `HasNablaFilt N`
(induction on `HasNablaFilt N'`, with the quotient lattice of (S2)). -/
theorem E2 (f : Hom N' N) (g : Hom N N'') (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (hN' : HasNablaFilt N') (hN'' : HasNablaFilt N'') :
    HasNablaFilt N := by
  induction hN' generalizing N N'' with
  | base hN' => exact E2_base h hg hN' hN''
  | step f₁ g₁ hfg₁ hf₁ hg₁ _ IH =>
    exact E2_step h hf hg f₁ g₁ hfg₁ hf₁ hg₁ (fun c d hcd hc hd hN₂ => IH c d hcd hc hd hN₂) hN''

end E2

/-! ### (E3) -/

section E3

variable {M N : DPLattice A}

/-- (E3, auxiliary) `M → M ⊕ N → N` (`inlHom`, `sndHom`) is short exact. -/
lemma shortExact_inl_snd (M N : DPLattice A) :
    ShortExact (Lemma35.inlHom M N) (Lemma35.sndHom M N) :=
  ⟨inlL_sndL_exact.1, inlL_sndL_exact.2.1, inlL_sndL_exact.2.2⟩

/-- (E3) `HasDeltaFilt M → HasDeltaFilt N → HasDeltaFilt (dsum M N)` (by (E1) for `inlHom`,
`sndHom`). -/
theorem E3_delta (hM : HasDeltaFilt M) (hN : HasDeltaFilt N) :
    HasDeltaFilt (Lemma35.dsum M N) :=
  E1 _ _ (shortExact_inl_snd M N) (inlL_wt M.wt N.wt) (sndL_wt M.wt N.wt) hM hN

/-- (E3) `HasNablaFilt M → HasNablaFilt N → HasNablaFilt (dsum M N)` (by (E2) for `inlHom`,
`sndHom`). -/
theorem E3_nabla (hM : HasNablaFilt M) (hN : HasNablaFilt N) :
    HasNablaFilt (Lemma35.dsum M N) :=
  E2 _ _ (shortExact_inl_snd M N) (inlL_wt M.wt N.wt) (sndL_wt M.wt N.wt) hM hN

/-- (E3) **Direct sums.** `HasDeltaFilt M → HasDeltaFilt N → HasDeltaFilt (dsum M N)`, and the
same for `HasNablaFilt`. -/
theorem E3 :
    (HasDeltaFilt M → HasDeltaFilt N → HasDeltaFilt (Lemma35.dsum M N)) ∧
    (HasNablaFilt M → HasNablaFilt N → HasNablaFilt (Lemma35.dsum M N)) :=
  ⟨E3_delta, E3_nabla⟩

end E3

end Filt
