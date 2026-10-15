module

public import RequestProject.LemmaW.PartW

/-!
# `C25_lemma_W_and_ext.md`: Part E — Lemma 3.3 for one pair

Encodings (namespace `LemmaW`):

* A short exact sequence `f : Hom N X`, `g : Hom X Z` is C19's `ShortExact f g`. It *splits*
  when `g` has a section `s : Hom Z X` (`Hom.comp g s = Hom.id Z`), equivalently (E1) when `f`
  has a retraction `r : Hom X N` (`Hom.comp r f = Hom.id N`).
* `Ext^1(Δ_A(λ), ∇_A(μ)) = 0` (Lemma 3.3, first sentence) is encoded, inside DP-lattices, as:
  every short exact sequence `nabla A m → X → delta A l` splits (`l = λ`, `m = μ`).
* `ℤ_[2]` is Mathlib's `PadicInt 2`.
-/

@[expose] public section

noncomputable section

namespace LemmaW

open DPLattice WeylFilt Doubling Finset

variable {A : Type*} [CommRing A]

/-! ### Abstract commutation lemmas for (E1) -/

section abstract

variable {N X Z : Type*} [AddCommGroup N] [Module A N] [AddCommGroup X] [Module A X]
  [AddCommGroup Z] [Module A Z]

/-- (E1, auxiliary) If `f ∘ ρ = id − s ∘ g` with `f` injective and `f`, `g`, `s` intertwine
operators `TN`, `TX`, `TZ`, then `ρ` intertwines `TX` and `TN`. -/
lemma retr_comm (f : N →ₗ[A] X) (g : X →ₗ[A] Z) (s : Z →ₗ[A] X) (ρ : X →ₗ[A] N)
    (hinj : Function.Injective f) (hfρ : f ∘ₗ ρ = LinearMap.id - s ∘ₗ g)
    (TN : N →ₗ[A] N) (TX : X →ₗ[A] X) (TZ : Z →ₗ[A] Z)
    (hf : f ∘ₗ TN = TX ∘ₗ f) (hg : g ∘ₗ TX = TZ ∘ₗ g) (hs : s ∘ₗ TZ = TX ∘ₗ s) :
    ρ ∘ₗ TX = TN ∘ₗ ρ := by
  refine LinearMap.ext fun y => hinj ?_
  have h1 : ∀ v, f (ρ v) = v - s (g v) := fun v => by
    have := LinearMap.congr_fun hfρ v
    simpa using this
  have hf' : ∀ v, f (TN v) = TX (f v) := fun v => LinearMap.congr_fun hf v
  have hg' : ∀ v, g (TX v) = TZ (g v) := fun v => LinearMap.congr_fun hg v
  have hs' : ∀ v, s (TZ v) = TX (s v) := fun v => LinearMap.congr_fun hs v
  simp only [LinearMap.comp_apply]
  rw [h1, hf', h1, hg', hs', map_sub]

/-- (E1, auxiliary) If `r ∘ f = id`, `range f = ker g`, `g ∘ σ = id`, and `f`, `g`, `r`
intertwine operators, then `s := (id − f ∘ r) ∘ σ` intertwines `TZ` and `TX`
(compare after the injective map `y ↦ (r y, g y)`). -/
lemma sec_comm (f : N →ₗ[A] X) (g : X →ₗ[A] Z) (r : X →ₗ[A] N) (σ : Z →ₗ[A] X)
    (hex : LinearMap.range f = LinearMap.ker g) (hrf : r ∘ₗ f = LinearMap.id)
    (hσ : g ∘ₗ σ = LinearMap.id)
    (TN : N →ₗ[A] N) (TX : X →ₗ[A] X) (TZ : Z →ₗ[A] Z)
    (hg : g ∘ₗ TX = TZ ∘ₗ g) (hr : r ∘ₗ TX = TN ∘ₗ r) :
    ((LinearMap.id - f ∘ₗ r) ∘ₗ σ) ∘ₗ TZ = TX ∘ₗ ((LinearMap.id - f ∘ₗ r) ∘ₗ σ) := by
  have hrf' : ∀ n, r (f n) = n := fun n => LinearMap.congr_fun hrf n
  have hσ' : ∀ z, g (σ z) = z := fun z => LinearMap.congr_fun hσ z
  have hgf : ∀ n, g (f n) = 0 := fun n => by
    rw [← LinearMap.mem_ker, ← hex]; exact ⟨n, rfl⟩
  have hg' : ∀ v, g (TX v) = TZ (g v) := fun v => LinearMap.congr_fun hg v
  have hr' : ∀ v, r (TX v) = TN (r v) := fun v => LinearMap.congr_fun hr v
  -- injectivity of `y ↦ (r y, g y)`
  have hinj : ∀ y, r y = 0 → g y = 0 → y = 0 := by
    intro y hry hgy
    have : y ∈ LinearMap.range f := by rw [hex]; exact hgy
    obtain ⟨n, rfl⟩ := this
    rw [hrf'] at hry; rw [hry, map_zero]
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [← sub_eq_zero]
  apply hinj
  · simp only [map_sub, hr', hrf', sub_self]
  · simp only [map_sub, hg', hgf, hσ', sub_zero, map_zero, sub_self]

end abstract

/-! ### (E1) -/

/-- (E1) Splitting: for a short exact sequence `f : Hom N X`, `g : Hom X Z` over any commutative
ring, `g` has a section in `Hom Z X` iff `f` has a retraction in `Hom X N`. -/
theorem E1 {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (h : ShortExact f g) :
    (∃ s : Hom Z X, Hom.comp g s = Hom.id Z) ↔ (∃ r : Hom X N, Hom.comp r f = Hom.id N) := by
  constructor
  · rintro ⟨s, hs⟩
    have hσ : g.toLin ∘ₗ s.toLin = LinearMap.id := congrArg Hom.toLin hs
    obtain ⟨ρ, hρf, hfρ⟩ :=
      exists_retraction_of_section f.toLin g.toLin h.inj h.exact s.toLin hσ
    refine ⟨⟨ρ, fun r => ?_, fun r => ?_, ?_⟩, Hom.ext' hρf⟩
    · exact retr_comm f.toLin g.toLin s.toLin ρ h.inj hfρ _ _ _ (f.comm_F r) (g.comm_F r)
        (s.comm_F r)
    · exact retr_comm f.toLin g.toLin s.toLin ρ h.inj hfρ _ _ _ (f.comm_E r) (g.comm_E r)
        (s.comm_E r)
    · exact retr_comm f.toLin g.toLin s.toLin ρ h.inj hfρ _ _ _ f.comm_H g.comm_H s.comm_H
  · rintro ⟨r, hr⟩
    have hrf : r.toLin ∘ₗ f.toLin = LinearMap.id := congrArg Hom.toLin hr
    obtain ⟨σ, hσ⟩ := exists_section g.toLin h.surj
    have hgf : g.toLin ∘ₗ f.toLin = 0 := by
      refine LinearMap.ext fun n => ?_
      rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, ← h.exact]
      exact ⟨n, rfl⟩
    refine ⟨⟨(LinearMap.id - f.toLin ∘ₗ r.toLin) ∘ₗ σ, fun t => ?_, fun t => ?_, ?_⟩, ?_⟩
    · exact (sec_comm f.toLin g.toLin r.toLin σ h.exact hrf hσ _ _ _ (g.comm_F t)
        (r.comm_F t))
    · exact (sec_comm f.toLin g.toLin r.toLin σ h.exact hrf hσ _ _ _ (g.comm_E t)
        (r.comm_E t))
    · exact (sec_comm f.toLin g.toLin r.toLin σ h.exact hrf hσ _ _ _ g.comm_H r.comm_H)
    · apply Hom.ext'
      change g.toLin ∘ₗ ((LinearMap.id - f.toLin ∘ₗ r.toLin) ∘ₗ σ) = LinearMap.id
      rw [← LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.comp_id,
        ← LinearMap.comp_assoc, hgf, LinearMap.zero_comp, sub_zero, hσ]

/-! ### (E2) -/

section E2

variable {l m : ℕ} {X : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X (delta A l)}

/-- (E2), case `m ≤ l`: the weights `m − 2t` of `nabla A m` lie in `[−l, l]`, so (W4) gives a
section of `g`. -/
theorem E2_le (hml : m ≤ l) (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) : ∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _ := by
  refine W4 h hf hg fun i => ?_
  change -(l : ℤ) ≤ weylWt m i ∧ weylWt m i ≤ l
  have := (i : Fin (m + 1)).isLt
  simp only [weylWt]; omega

/-- (E2), case `m > l`: dualize ((D5)), identify the ends with (D4) to get
`nabla A l → dual X → delta A m`, apply (W4), and dualize the section back
((D2), (D3), (D4)) to a retraction of `f`. -/
theorem E2_gt (hml : l < m) (h : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) : ∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _ := by
  have hD := D5 h
  let f' : Hom (nabla A l) (dual X) := Hom.comp (dualHom g) (isoDualDelta l).inv
  let g' : Hom (dual X) (delta A m) := Hom.comp (isoDualNabla m).hom (dualHom f)
  have e1 : f'.toLin = trM g.toLin := LinearMap.comp_id _
  have e2 : g'.toLin = trM f.toLin := LinearMap.id_comp _
  have hD' : ShortExact f' g' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact hD.inj
    · rw [e2]; exact hD.surj
    · rw [e1, e2]; exact hD.exact
  have hf' : IsWtPres f'.toLin := fun i j hij => by
    rw [e1]; exact dualHom_wtPres hg i j hij
  have hg' : IsWtPres g'.toLin := fun i j hij => by
    rw [e2]; exact dualHom_wtPres hf i j hij
  obtain ⟨s', hs'⟩ := W4 hD' hf' hg' fun i => by
    change -(m : ℤ) ≤ weylWt l i ∧ weylWt l i ≤ m
    have := (i : Fin (l + 1)).isLt
    simp only [weylWt]; omega
  have hs'' : trM f.toLin ∘ₗ s'.toLin = LinearMap.id := by
    rw [← e2]; exact congrArg Hom.toLin hs'
  have ht : trM s'.toLin ∘ₗ f.toLin = LinearMap.id := by
    have := congrArg trM hs''
    rwa [trM_comp, trM_trM, trM_id] at this
  refine ⟨Hom.comp (isoDualDelta m).hom (Hom.comp (dualHom s') (isoDualDual X).inv), ?_⟩
  apply Hom.ext'
  change LinearMap.id ∘ₗ (trM s'.toLin ∘ₗ LinearMap.id) ∘ₗ f.toLin = LinearMap.id
  rw [LinearMap.id_comp, LinearMap.comp_id, ht]

/-- (E2) **Lemma 3.3, first sentence.** For all `l m : ℕ`, every short exact sequence
`f : Hom (nabla A m) X`, `g : Hom X (delta A l)` with `f.toLin`, `g.toLin` weight-preserving
splits: `g` has a section and `f` has a retraction. -/
theorem E2 (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X (delta A l)}
    (h : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) := by
  rcases le_or_gt m l with hml | hml
  · have hs := E2_le hml h hf hg
    exact ⟨hs, (E1 h).mp hs⟩
  · have hr := E2_gt hml h hf hg
    exact ⟨(E1 h).mpr hr, hr⟩

end E2

/-- (E3) Over a domain of characteristic zero, (E2) holds without the weight-preservation
hypotheses (they follow from (P1)). -/
theorem E3 [IsDomain A] [CharZero A] (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X}
    {g : Hom X (delta A l)} (h : ShortExact f g) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) :=
  E2 l m h (P1 f) (P1 g)

/-- (E4) The case of the paper: for `A = ℤ_[2]` and all `l m : ℕ`, every short exact sequence
`nabla ℤ_[2] m → X → delta ℤ_[2] l` splits (both forms of (E2)). -/
theorem E4 (l m : ℕ) {X : DPLattice ℤ_[2]} {f : Hom (nabla ℤ_[2] m) X}
    {g : Hom X (delta ℤ_[2] l)} (h : ShortExact f g) :
    (∃ s : Hom (delta ℤ_[2] l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla ℤ_[2] m), Hom.comp r f = Hom.id _) :=
  E3 l m h

end LemmaW
