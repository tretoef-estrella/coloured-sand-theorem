module

public import RequestProject.Cocycle.PartG7

/-!
# `C27_cocycles_and_filtrations.md`: Part F — filtrations, Part V — vanishing

Encodings (namespace `Cocycle`):

* (F1) `HasDeltaFilt M` and `HasNablaFilt N` are inductive predicates (in `Prop`) with the
  constructors `base` (empty basis) and `step` (one short exact sequence with weight-preserving
  maps, `Δ` on top, resp. `∇` at the bottom), exactly as in the file.
* "every cocycle from `M` to `N` is a coboundary" is
  `∀ c : Pair M N, IsCocycle c → IsCoboundary c`.
* a short exact sequence `f : Hom N X`, `g : Hom X M` *splits* when
  `∃ s : Hom M X, Hom.comp g s = Hom.id M` and `∃ r : Hom X N, Hom.comp r f = Hom.id N`.
* `ℤ_[2]` is Mathlib's `PadicInt 2`.
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-! ### Part F -/

/-- (F1) `HasDeltaFilt M`: (base) if `M.ι` is empty; (step) if `f : Hom M' M`,
`g : Hom M (delta A l)` are short exact with `f.toLin`, `g.toLin` weight-preserving and
`HasDeltaFilt M'`. -/
inductive HasDeltaFilt : DPLattice A → Prop
  | base {M : DPLattice A} (h : IsEmpty M.ι) : HasDeltaFilt M
  | step {M' M : DPLattice A} {l : ℕ} (f : Hom M' M) (g : Hom M (delta A l))
      (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
      (hM' : HasDeltaFilt M') : HasDeltaFilt M

/-- (F1) `HasNablaFilt N`: (base) if `N.ι` is empty; (step) if `f : Hom (nabla A m) N`,
`g : Hom N N'` are short exact with `f.toLin`, `g.toLin` weight-preserving and
`HasNablaFilt N'`. -/
inductive HasNablaFilt : DPLattice A → Prop
  | base {N : DPLattice A} (h : IsEmpty N.ι) : HasNablaFilt N
  | step {N N' : DPLattice A} {m : ℕ} (f : Hom (nabla A m) N) (g : Hom N N')
      (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
      (hN' : HasNablaFilt N') : HasNablaFilt N

instance : IsEmpty (zeroL A).ι := inferInstanceAs (IsEmpty Empty)

/-- (F2, auxiliary) the zero morphism `zeroL A → M`. -/
def fromZero (M : DPLattice A) : Hom (zeroL A) M where
  toLin := 0
  comm_F _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_E _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_H := by rw [LinearMap.zero_comp, LinearMap.comp_zero]

/-- (F2, auxiliary) the zero morphism `M → zeroL A`. -/
def toZero (M : DPLattice A) : Hom M (zeroL A) where
  toLin := 0
  comm_F _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_E _ := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  comm_H := by rw [LinearMap.zero_comp, LinearMap.comp_zero]

/-- (F2) `HasDeltaFilt (delta A l)`: one step `zeroL A → delta A l → delta A l`. -/
theorem F2_delta (l : ℕ) : HasDeltaFilt (delta A l) := by
  refine HasDeltaFilt.step (fromZero (delta A l)) (Hom.id (delta A l)) ⟨?_, ?_, ?_⟩
    isWtPres_zero isWtPres_id (HasDeltaFilt.base inferInstance)
  · intro a b _; exact Subsingleton.elim a b
  · intro y; exact ⟨y, rfl⟩
  · change LinearMap.range (0 : Lin (zeroL A) (delta A l)) = LinearMap.ker LinearMap.id
    rw [LinearMap.range_zero, LinearMap.ker_id]

/-- (F2) `HasNablaFilt (nabla A m)`: one step `nabla A m → nabla A m → zeroL A`. -/
theorem F2_nabla (m : ℕ) : HasNablaFilt (nabla A m) := by
  refine HasNablaFilt.step (Hom.id (nabla A m)) (toZero (nabla A m)) ⟨?_, ?_, ?_⟩
    isWtPres_id isWtPres_zero (HasNablaFilt.base inferInstance)
  · intro a b h; exact h
  · intro y; exact ⟨0, Subsingleton.elim _ _⟩
  · change LinearMap.range LinearMap.id = LinearMap.ker (0 : Lin (nabla A m) (zeroL A))
    rw [LinearMap.range_id, LinearMap.ker_zero]

/-- (F2) `HasDeltaFilt (delta A l)` and `HasNablaFilt (nabla A m)`. -/
theorem F2 (l m : ℕ) : HasDeltaFilt (delta A l) ∧ HasNablaFilt (nabla A m) :=
  ⟨F2_delta l, F2_nabla m⟩

/-! ### Part V -/

variable {M N : DPLattice A}

/-- (V4, base case) if `M.ι` is empty, every cocycle from `M` to `N` is `0 = d0`. -/
lemma coboundary_of_isEmpty_left (hM : IsEmpty M.ι) (c : Pair M N) : IsCoboundary c := by
  refine ⟨0, isWtPres_zero, Prod.ext (funext fun r => ?_) (funext fun r => ?_)⟩ <;>
  · refine LinearMap.ext fun v => ?_
    rw [Subsingleton.elim v 0, map_zero, map_zero]

/-- (V4, base case) if `N.ι` is empty, every cocycle from `M` to `N` is `0 = d0`. -/
lemma coboundary_of_isEmpty_right (hN : IsEmpty N.ι) (c : Pair M N) : IsCoboundary c :=
  ⟨0, isWtPres_zero, Prod.ext (funext fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _)
    (funext fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _)⟩

/-- (V1) **One pair.** Every cocycle from `delta A l` to `nabla A m` is a coboundary, for all
`l m` (by (G3), (G5) and C25 (E2)). -/
theorem V1 (l m : ℕ) (c : Pair (delta A l) (nabla A m)) (hc : IsCocycle c) : IsCoboundary c := by
  obtain ⟨hi, hp, hse⟩ := G3 c hc
  exact ((G5 c hc).1).mpr (E2 l m hse hi hp).1

/-- (V2, auxiliary) if `c ∘ f = 0` and `f ∘ r = id − σ ∘ g`, then `c = (c ∘ σ) ∘ g`. -/
lemma pcomp_split {M' M'' : DPLattice A} {c : Pair M N} {f : Lin M' M} {g : Lin M M''}
    {σ : Lin M'' M} {r : Lin M M'} (hcf : pcomp c f = 0)
    (hfr : f ∘ₗ r = LinearMap.id - σ ∘ₗ g) : c = pcomp (pcomp c σ) g := by
  have hid : LinearMap.id = f ∘ₗ r + σ ∘ₗ g := by rw [hfr]; abel
  have h1 : ∀ k, c.1 k ∘ₗ f = 0 := fun k => congrFun (congrArg Prod.fst hcf) k
  have h2 : ∀ k, c.2 k ∘ₗ f = 0 := fun k => congrFun (congrArg Prod.snd hcf) k
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · conv_lhs => rw [← LinearMap.comp_id (c.1 k), hid]
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, h1, LinearMap.zero_comp, zero_add]; rfl
  · conv_lhs => rw [← LinearMap.comp_id (c.2 k), hid]
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, h2, LinearMap.zero_comp, zero_add]; rfl

/-- (V2) **Induction on `M`.** Let `f : Hom M' M`, `g : Hom M (delta A l)` be short exact with
weight-preserving underlying maps, and let `N` be such that every cocycle from `M'` to `N` and
every cocycle from `delta A l` to `N` is a coboundary. Then every cocycle from `M` to `N` is a
coboundary. -/
theorem V2 {M' : DPLattice A} {l : ℕ} {f : Hom M' M} {g : Hom M (delta A l)}
    (h : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (h1 : ∀ c : Pair M' N, IsCocycle c → IsCoboundary c)
    (h2 : ∀ c : Pair (delta A l) N, IsCocycle c → IsCoboundary c) :
    ∀ c : Pair M N, IsCocycle c → IsCoboundary c := by
  intro c hc
  obtain ⟨σ, hσw, hσ⟩ := exists_wtPres_section h.surj hg
  obtain ⟨r, hrf, hfr⟩ := exists_retraction_of_section f.toLin g.toLin h.inj h.exact σ hσ
  have hrw : IsWtPres r := isWtPres_retraction h.inj hf hg hσw hfr
  obtain ⟨ψ', hψ'w, hψ'⟩ := h1 _ (G6a_pcomp hc f hf)
  have hψ0w : IsWtPres (ψ' ∘ₗ r) := isWtPres_comp hψ'w hrw
  have hc1 : IsCocycle (c - d (ψ' ∘ₗ r)) := isCocycle_sub hc (G4 hψ0w)
  have hzero : pcomp (c - d (ψ' ∘ₗ r)) f.toLin = 0 := by
    rw [pcomp_sub, ← G6a_d_pcomp, LinearMap.comp_assoc, hrf, LinearMap.comp_id, hψ', sub_self]
  have key := pcomp_split hzero hfr
  have hc'' : IsCocycle (pcomp (c - d (ψ' ∘ₗ r)) σ) :=
    G6b g h.surj hg (by rw [← key]; exact hc1)
  obtain ⟨ψ'', hψ''w, hψ''⟩ := h2 _ hc''
  refine ⟨ψ' ∘ₗ r + ψ'' ∘ₗ g.toLin, isWtPres_add hψ0w (isWtPres_comp hψ''w hg), ?_⟩
  rw [d_add, G6a_d_pcomp, hψ'', ← key, add_sub_cancel]

/-- (V3) **Induction on `N`.** Let `f : Hom (nabla A m) N`, `g : Hom N N'` be short exact with
weight-preserving underlying maps, and let `M` be such that every cocycle from `M` to
`nabla A m` and every cocycle from `M` to `N'` is a coboundary. Then every cocycle from `M` to
`N` is a coboundary. -/
theorem V3 {N' : DPLattice A} {m : ℕ} {f : Hom (nabla A m) N} {g : Hom N N'}
    (h : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (h1 : ∀ c : Pair M (nabla A m), IsCocycle c → IsCoboundary c)
    (h2 : ∀ c : Pair M N', IsCocycle c → IsCoboundary c) :
    ∀ c : Pair M N, IsCocycle c → IsCoboundary c := by
  intro c hc
  obtain ⟨ψ', hψ'w, hψ'⟩ := h2 _ (G6a_qcomp hc g hg)
  obtain ⟨ψt, hψtw, hψt⟩ := exists_wtPres_lift h.surj hg hψ'w
  have hc1 : IsCocycle (c - d ψt) := isCocycle_sub hc (G4 hψtw)
  have hzero : qcomp g.toLin (c - d ψt) = 0 := by
    rw [qcomp_sub, ← G6a_d_qcomp, hψt, hψ', sub_self]
  obtain ⟨σ, hσ⟩ := exists_section g.toLin h.surj
  obtain ⟨ρ, -, hfρ⟩ := exists_retraction_of_section f.toLin g.toLin h.inj h.exact σ hσ
  have key : qcomp f.toLin (qcomp ρ (c - d ψt)) = c - d ψt := by
    have h1 : ∀ k, g.toLin ∘ₗ (c - d ψt).1 k = 0 := fun k =>
      congrFun (congrArg Prod.fst hzero) k
    have h2 : ∀ k, g.toLin ∘ₗ (c - d ψt).2 k = 0 := fun k =>
      congrFun (congrArg Prod.snd hzero) k
    rw [qcomp_qcomp, hfρ]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · rw [qcomp_fst, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc, h1,
        LinearMap.comp_zero, sub_zero]
    · rw [qcomp_snd, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc, h2,
        LinearMap.comp_zero, sub_zero]
  have hc' : IsCocycle (qcomp ρ (c - d ψt)) := G6c f h.inj hf (by rw [key]; exact hc1)
  obtain ⟨ψ'', hψ''w, hψ''⟩ := h1 _ hc'
  refine ⟨ψt + f.toLin ∘ₗ ψ'', isWtPres_add hψtw (isWtPres_comp hf hψ''w), ?_⟩
  rw [d_add, G6a_d_qcomp, hψ'', key, add_sub_cancel]

/-- (V4, first step) if `HasDeltaFilt M`, every cocycle from `M` to `nabla A m` is a coboundary
(induction on the `Δ`-filtration of `M` by (V2), from (V1)). -/
theorem V4_nabla (hM : HasDeltaFilt M) (m : ℕ) :
    ∀ c : Pair M (nabla A m), IsCocycle c → IsCoboundary c := by
  induction hM with
  | base hM => exact fun c _ => coboundary_of_isEmpty_left hM c
  | step f g h hf hg _ ih => exact V2 h hf hg ih (V1 _ m)

/-- (V4) **Lemma 3.3, second sentence**, cocycle form: if `HasDeltaFilt M` and
`HasNablaFilt N`, every cocycle from `M` to `N` is a coboundary (induction on the
`∇`-filtration of `N` by (V3)). -/
theorem V4_cocycle (hM : HasDeltaFilt M) (hN : HasNablaFilt N) :
    ∀ c : Pair M N, IsCocycle c → IsCoboundary c := by
  induction hN with
  | base hN => exact fun c _ => coboundary_of_isEmpty_right hN c
  | step f g h hf hg _ ih => exact V3 h hf hg (V4_nabla hM _) ih

/-- (V4) **Lemma 3.3, second sentence.** If `HasDeltaFilt M` and `HasNablaFilt N`, then every
cocycle from `M` to `N` is a coboundary, and every short exact sequence `f : Hom N X`,
`g : Hom X M` with `f.toLin`, `g.toLin` weight-preserving splits
(`∃ s : Hom M X, Hom.comp g s = Hom.id M` and `∃ r : Hom X N, Hom.comp r f = Hom.id N`). -/
theorem V4 (hM : HasDeltaFilt M) (hN : HasNablaFilt N) :
    (∀ c : Pair M N, IsCocycle c → IsCoboundary c) ∧
    (∀ {X : DPLattice A} {f : Hom N X} {g : Hom X M}, ShortExact f g → IsWtPres f.toLin →
      IsWtPres g.toLin →
      (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N)) :=
  ⟨V4_cocycle hM hN, fun h hf hg => G7_split (V4_cocycle hM hN) h hf hg⟩

/-- (V5) If `A` is a domain of characteristic zero, the splitting in (V4) holds without the
weight-preservation hypotheses on `f`, `g` (they follow from C25 (P1)). -/
theorem V5 [IsDomain A] [CharZero A] (hM : HasDeltaFilt M) (hN : HasNablaFilt N)
    {X : DPLattice A} {f : Hom N X} {g : Hom X M} (h : ShortExact f g) :
    (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N) :=
  (V4 hM hN).2 h (P1 f) (P1 g)

/-- (V6) The case `A = ℤ_[2]`: if `HasDeltaFilt M` and `HasNablaFilt N`, every cocycle from
`M` to `N` is a coboundary, and every short exact sequence `f : Hom N X`, `g : Hom X M` splits
(no weight-preservation hypotheses needed, by (V5)). -/
theorem V6 {M N : DPLattice ℤ_[2]} (hM : HasDeltaFilt M) (hN : HasNablaFilt N) :
    (∀ c : Pair M N, IsCocycle c → IsCoboundary c) ∧
    (∀ {X : DPLattice ℤ_[2]} {f : Hom N X} {g : Hom X M}, ShortExact f g →
      (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N)) :=
  ⟨V4_cocycle hM hN, fun h => V5 hM hN h⟩

end Cocycle
