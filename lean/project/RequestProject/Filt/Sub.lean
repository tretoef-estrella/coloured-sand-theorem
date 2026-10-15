module

public import RequestProject.Lift2.All
public import RequestProject.Lemma35.All
public import RequestProject.Tensor2.All

/-!
# `C29_filtrations_and_dance_lattices.md`: Part S — sub-lattices and quotient lattices

Encodings (namespace `Filt`), reusing C18's `DPLattice`, `IsDP`, `Hom`, `H`:

* A vector of the new lattice is a function `κ → A`, `κ : Type` a finite type with decidable
  equality, with weights `wK : κ → ℤ`; `δ_k = Pi.single k 1`.
* "`j` is weight-preserving" is `∀ k i, wK k ≠ X.wt i → j (δ_k) i = 0`, and "`p` is
  weight-preserving" is `∀ i k, X.wt i ≠ wK k → p (δ_i) k = 0` (the same condition as C25's
  `IsWtPres`, for raw weights).
* "`range j` is stable under every `X.Fd r`, `X.Ed r`" is
  `∀ r x, X.Fd r (j x) ∈ LinearMap.range j` (and the same for `Ed`); "`ker q` is stable" is
  `∀ r x, x ∈ LinearMap.ker q → X.Fd r x ∈ LinearMap.ker q` (and the same for `Ed`).
* `sub X wK j p …` and `quot X wK q s …` are the DP-lattices of (S1), (S2): basis `κ`, weights
  `wK`, operators `p ∘ X.Fd r ∘ j`, `p ∘ X.Ed r ∘ j` (resp. `q ∘ X.Fd r ∘ s`, `q ∘ X.Ed r ∘ s`);
  `subHom` and `quotHom` are the morphisms `j : sub … → X` and `q : X → quot …`.
-/

@[expose] public section

noncomputable section

namespace Filt

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

variable {A : Type*} [CommRing A]

/-! ### (S1) sub-lattice -/

section sub

variable (X : DPLattice A) {κ : Type} [Fintype κ] [DecidableEq κ] (wK : κ → ℤ)
  (j : (κ → A) →ₗ[A] (X.ι → A)) (p : (X.ι → A) →ₗ[A] (κ → A))

omit [Fintype κ] [DecidableEq κ] in
/-- (S1, auxiliary) `j ∘ p ∘ T ∘ j = T ∘ j` for an operator `T` with `T (range j) ⊆ range j`. -/
lemma jp_comp (hpj : p ∘ₗ j = LinearMap.id) (T : Module.End A (X.ι → A))
    (hT : ∀ x, T (j x) ∈ LinearMap.range j) : j ∘ₗ p ∘ₗ T ∘ₗ j = T ∘ₗ j := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, hy⟩ := hT x
  simp only [LinearMap.comp_apply, ← hy]
  rw [← LinearMap.comp_apply p j, hpj, LinearMap.id_apply]

omit [Fintype κ] [DecidableEq κ] in
lemma jp_comp_apply (hpj : p ∘ₗ j = LinearMap.id) (T : Module.End A (X.ι → A))
    (hT : ∀ x, T (j x) ∈ LinearMap.range j) (x : κ → A) : j (p (T (j x))) = T (j x) :=
  LinearMap.congr_fun (jp_comp X j p hpj T hT) x

/-- (S1) the raw data `(κ, wK, p ∘ X.Fd r ∘ j, p ∘ X.Ed r ∘ j)` satisfy `IsDP`. -/
theorem sub_isDP (hpj : p ∘ₗ j = LinearMap.id)
    (hj : ∀ k i, wK k ≠ X.wt i → j (Pi.single k 1) i = 0)
    (hp : ∀ i k, X.wt i ≠ wK k → p (Pi.single i 1) k = 0)
    (hF : ∀ r x, X.Fd r (j x) ∈ LinearMap.range j)
    (hE : ∀ r x, X.Ed r (j x) ∈ LinearMap.range j) :
    IsDP wK (fun r => p ∘ₗ X.Fd r ∘ₗ j) (fun r => p ∘ₗ X.Ed r ∘ₗ j) := by
  have hjw : ∀ k, InWt X.wt (wK k) (j (Pi.single k 1)) := fun k =>
    inWt_map_raw j hj (inWt_single wK k)
  refine ⟨fun k r i hi => ?_, fun k r i hi => ?_, ?_, ?_, fun a b => ?_, fun a b => ?_,
    fun k r s => ?_⟩
  · exact inWt_map_raw p hp (X.isDP.inWt_Fd r (hjw k)) i hi
  · exact inWt_map_raw p hp (X.isDP.inWt_Ed r (hjw k)) i hi
  · simp only [X.isDP.P0_F, Module.End.one_eq_id, LinearMap.id_comp]; exact hpj
  · simp only [X.isDP.P0_E, Module.End.one_eq_id, LinearMap.id_comp]; exact hpj
  · calc (p ∘ₗ X.Fd a ∘ₗ j) ∘ₗ (p ∘ₗ X.Fd b ∘ₗ j)
          = p ∘ₗ X.Fd a ∘ₗ (j ∘ₗ p ∘ₗ X.Fd b ∘ₗ j) := rfl
      _ = p ∘ₗ (X.Fd a ∘ₗ X.Fd b) ∘ₗ j := by rw [jp_comp X j p hpj _ (hF b)]; rfl
      _ = _ := by rw [X.isDP.P1_F, LinearMap.smul_comp, LinearMap.comp_smul]
  · calc (p ∘ₗ X.Ed a ∘ₗ j) ∘ₗ (p ∘ₗ X.Ed b ∘ₗ j)
          = p ∘ₗ X.Ed a ∘ₗ (j ∘ₗ p ∘ₗ X.Ed b ∘ₗ j) := rfl
      _ = p ∘ₗ (X.Ed a ∘ₗ X.Ed b) ∘ₗ j := by rw [jp_comp X j p hpj _ (hE b)]; rfl
      _ = _ := by rw [X.isDP.P1_E, LinearMap.smul_comp, LinearMap.comp_smul]
  · simp only [LinearMap.comp_apply]
    rw [jp_comp_apply X j p hpj _ (hF r), K_vec X (hjw k), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, jp_comp_apply X j p hpj _ (hE (s - i))]

variable (hpj : p ∘ₗ j = LinearMap.id)
    (hj : ∀ k i, wK k ≠ X.wt i → j (Pi.single k 1) i = 0)
    (hp : ∀ i k, X.wt i ≠ wK k → p (Pi.single i 1) k = 0)
    (hF : ∀ r x, X.Fd r (j x) ∈ LinearMap.range j)
    (hE : ∀ r x, X.Ed r (j x) ∈ LinearMap.range j)

/-- (S1) the sub-lattice `sub X wK j p …`: basis `κ`, weights `wK`,
`Fd r = p ∘ X.Fd r ∘ j`, `Ed r = p ∘ X.Ed r ∘ j`. -/
def sub : DPLattice A where
  ι := κ
  wt := wK
  Fd r := p ∘ₗ X.Fd r ∘ₗ j
  Ed r := p ∘ₗ X.Ed r ∘ₗ j
  isDP := sub_isDP X wK j p hpj hj hp hF hE

/-- (S1) `j` as a morphism `sub X wK j p … → X`. -/
def subHom : Hom (sub X wK j p hpj hj hp hF hE) X where
  toLin := j
  comm_F r := jp_comp X j p hpj _ (hF r)
  comm_E r := jp_comp X j p hpj _ (hE r)
  comm_H := comm_H_of_isWtPres (M := sub X wK j p hpj hj hp hF hE) (N := X) hj

/-- (S1) **Sub-lattice.** Let `X` be a DP-lattice, `κ` a finite type with decidable equality,
`wK : κ → ℤ`, and `j : (κ → A) → (X.ι → A)`, `p : (X.ι → A) → (κ → A)` linear with `p ∘ j = id`,
`j`, `p` weight-preserving and `range j` stable under every `X.Fd r`, `X.Ed r`. Then
`sub X wK j p …` is a DP-lattice with basis `κ`, weights `wK`, operators
`Fd r = p ∘ X.Fd r ∘ j`, `Ed r = p ∘ X.Ed r ∘ j`, and `j` is a morphism `subHom` from it to
`X`. -/
theorem S1 :
    (sub X wK j p hpj hj hp hF hE).ι = κ ∧
    (∀ k, (sub X wK j p hpj hj hp hF hE).wt k = wK k) ∧
    (∀ r, (sub X wK j p hpj hj hp hF hE).Fd r = p ∘ₗ X.Fd r ∘ₗ j) ∧
    (∀ r, (sub X wK j p hpj hj hp hF hE).Ed r = p ∘ₗ X.Ed r ∘ₗ j) ∧
    (subHom X wK j p hpj hj hp hF hE).toLin = j :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

end sub

/-! ### (S2) quotient lattice -/

section quot

variable (X : DPLattice A) {κ : Type} [Fintype κ] [DecidableEq κ] (wK : κ → ℤ)
  (q : (X.ι → A) →ₗ[A] (κ → A)) (s : (κ → A) →ₗ[A] (X.ι → A))

omit [Fintype κ] [DecidableEq κ] in
/-- (S2, auxiliary) `q ∘ T ∘ s ∘ q = q ∘ T` for an operator `T` with `T (ker q) ⊆ ker q`. -/
lemma qs_comp (hqs : q ∘ₗ s = LinearMap.id) (T : Module.End A (X.ι → A))
    (hT : ∀ x, x ∈ LinearMap.ker q → T x ∈ LinearMap.ker q) :
    (q ∘ₗ T ∘ₗ s) ∘ₗ q = q ∘ₗ T := by
  refine LinearMap.ext fun x => ?_
  have hx : s (q x) - x ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply q s, hqs, LinearMap.id_apply,
      sub_self]
  have := hT _ hx
  rw [LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero] at this
  exact this

/-- (S2) the raw data `(κ, wK, q ∘ X.Fd r ∘ s, q ∘ X.Ed r ∘ s)` satisfy `IsDP`. -/
theorem quot_isDP (hqs : q ∘ₗ s = LinearMap.id)
    (hq : ∀ i k, X.wt i ≠ wK k → q (Pi.single i 1) k = 0)
    (hs : ∀ k i, wK k ≠ X.wt i → s (Pi.single k 1) i = 0)
    (hF : ∀ r x, x ∈ LinearMap.ker q → X.Fd r x ∈ LinearMap.ker q)
    (hE : ∀ r x, x ∈ LinearMap.ker q → X.Ed r x ∈ LinearMap.ker q) :
    IsDP wK (fun r => q ∘ₗ X.Fd r ∘ₗ s) (fun r => q ∘ₗ X.Ed r ∘ₗ s) :=
  isDP_transport X q hq (fun r => (qs_comp X q s hqs _ (hF r)).symm)
    (fun r => (qs_comp X q s hqs _ (hE r)).symm)
    (fun k => ⟨s (Pi.single k 1), inWt_map_raw s hs (inWt_single wK k), by
      rw [← LinearMap.comp_apply q s, hqs, LinearMap.id_apply]⟩)

variable (hqs : q ∘ₗ s = LinearMap.id)
    (hq : ∀ i k, X.wt i ≠ wK k → q (Pi.single i 1) k = 0)
    (hs : ∀ k i, wK k ≠ X.wt i → s (Pi.single k 1) i = 0)
    (hF : ∀ r x, x ∈ LinearMap.ker q → X.Fd r x ∈ LinearMap.ker q)
    (hE : ∀ r x, x ∈ LinearMap.ker q → X.Ed r x ∈ LinearMap.ker q)

/-- (S2) the quotient lattice `quot X wK q s …`: basis `κ`, weights `wK`,
`Fd r = q ∘ X.Fd r ∘ s`, `Ed r = q ∘ X.Ed r ∘ s`. -/
def quot : DPLattice A where
  ι := κ
  wt := wK
  Fd r := q ∘ₗ X.Fd r ∘ₗ s
  Ed r := q ∘ₗ X.Ed r ∘ₗ s
  isDP := quot_isDP X wK q s hqs hq hs hF hE

/-- (S2) `q` as a morphism `X → quot X wK q s …`. -/
def quotHom : Hom X (quot X wK q s hqs hq hs hF hE) where
  toLin := q
  comm_F r := (qs_comp X q s hqs _ (hF r)).symm
  comm_E r := (qs_comp X q s hqs _ (hE r)).symm
  comm_H := comm_H_of_isWtPres (M := X) (N := quot X wK q s hqs hq hs hF hE) hq

/-- (S2) **Quotient lattice.** Let `X` be a DP-lattice, `κ`, `wK` as in (S1),
`q : (X.ι → A) → (κ → A)`, `s : (κ → A) → (X.ι → A)` linear with `q ∘ s = id`, both
weight-preserving, and `ker q` stable under every `X.Fd r`, `X.Ed r`. Then `quot X wK q s …` is
a DP-lattice with basis `κ`, weights `wK`, operators `Fd r = q ∘ X.Fd r ∘ s`,
`Ed r = q ∘ X.Ed r ∘ s`, and `q` is a morphism `quotHom` from `X` to it. -/
theorem S2 :
    (quot X wK q s hqs hq hs hF hE).ι = κ ∧
    (∀ k, (quot X wK q s hqs hq hs hF hE).wt k = wK k) ∧
    (∀ r, (quot X wK q s hqs hq hs hF hE).Fd r = q ∘ₗ X.Fd r ∘ₗ s) ∧
    (∀ r, (quot X wK q s hqs hq hs hF hE).Ed r = q ∘ₗ X.Ed r ∘ₗ s) ∧
    (quotHom X wK q s hqs hq hs hF hE).toLin = q :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

end quot

end Filt
