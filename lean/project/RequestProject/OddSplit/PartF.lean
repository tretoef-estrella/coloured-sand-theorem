module

public import RequestProject.OddSplit.PsiHom

/-!
# `CSI3_the_split.md`: Part F — the functor `Ψ_r` on morphisms

Encoding: for a linear map `f : (ι → A) → (κ → A)`, `psiLin f` is `id ⊗ f` on
`Bool × Fin p × −`: it applies `f` in each slot `(b, j)`, so
`psiLin f (A_j n) = A_j f(n)` and `psiLin f (C_j n) = C_j f(n)` (`psiLin_aV`, `psiLin_cV`).
For `f : Hom N N'`, `psiHom p r f : Hom (psi p N r …) (psi p N' r …)` is built with (Q0c).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

/-! ### `id ⊗ f` on slot vectors -/

section lin

variable {A : Type*} [CommRing A] (p : ℕ) {ι κ : Type*}

/-- (F1) `id ⊗ f`: apply `f` in each slot `(b, j)` of `Bool × Fin p × −`. -/
def psiLin (f : (ι → A) →ₗ[A] (κ → A)) : (Bool × Fin p × ι → A) →ₗ[A] (Bool × Fin p × κ → A) where
  toFun x y := f (fun i => x (y.1, y.2.1, i)) y.2.2
  map_add' x x' := by
    funext y
    simp only [Pi.add_apply]
    rw [show (fun i => x (y.1, y.2.1, i) + x' (y.1, y.2.1, i)) =
      (fun i => x (y.1, y.2.1, i)) + (fun i => x' (y.1, y.2.1, i)) from rfl, map_add]
    rfl
  map_smul' c x := by
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [show (fun i => c • x (y.1, y.2.1, i)) = c • (fun i => x (y.1, y.2.1, i)) from rfl,
      map_smul]
    rfl

lemma psiLin_aV (f : (ι → A) →ₗ[A] (κ → A)) (k : ℕ) (n : ι → A) :
    psiLin p f (aV p k n) = aV p k (f n) := by
  funext ⟨b, j, i⟩
  show f (fun i' => aV p k n (b, j, i')) i = _
  rw [aV_apply]
  by_cases h : b = false ∧ (j : ℕ) = k
  · have : (fun i' => aV p k n (b, j, i')) = n := by
      funext i'; rw [aV_apply, if_pos h]
    rw [this, if_pos h]
  · have : (fun i' => aV p k n (b, j, i')) = 0 := by
      funext i'; rw [aV_apply, if_neg h]; rfl
    rw [this, map_zero, if_neg h]; rfl

lemma psiLin_cV (f : (ι → A) →ₗ[A] (κ → A)) (k : ℕ) (n : ι → A) :
    psiLin p f (cV p k n) = cV p k (f n) := by
  funext ⟨b, j, i⟩
  show f (fun i' => cV p k n (b, j, i')) i = _
  rw [cV_apply]
  by_cases h : b = true ∧ (j : ℕ) = k
  · have : (fun i' => cV p k n (b, j, i')) = n := by
      funext i'; rw [cV_apply, if_pos h]
    rw [this, if_pos h]
  · have : (fun i' => cV p k n (b, j, i')) = 0 := by
      funext i'; rw [cV_apply, if_neg h]; rfl
    rw [this, map_zero, if_neg h]; rfl

lemma psiLin_id [Fintype ι] [DecidableEq ι] :
    psiLin p (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) = LinearMap.id :=
  ext_aV_cV p (fun j i _ => by rw [psiLin_aV]; rfl) (fun j i _ => by rw [psiLin_cV]; rfl)

lemma psiLin_comp [Fintype ι] [DecidableEq ι] {ν : Type*} (g : (κ → A) →ₗ[A] (ν → A))
    (f : (ι → A) →ₗ[A] (κ → A)) : psiLin p (g ∘ₗ f) = psiLin p g ∘ₗ psiLin p f :=
  ext_aV_cV p (fun j i _ => by rw [LinearMap.comp_apply, psiLin_aV, psiLin_aV, psiLin_aV]; rfl)
    (fun j i _ => by rw [LinearMap.comp_apply, psiLin_cV, psiLin_cV, psiLin_cV]; rfl)

end lin

/-! ### (F1) -/

variable (p : ℕ) [Fact p.Prime]

variable {N N' : DPLattice ℤ_[p]} (f : Hom N N')

lemma psiLin_psiFL (r : ℕ) (b : Bool) (j : ℕ) (n : N.ι → ℤ_[p]) :
    psiLin p f.toLin (psiFL p N r b j n) = psiFL p N' r b j (f.toLin n) := by
  cases b <;> simp only [psiFL] <;> split_ifs <;>
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
      map_smul, psiLin_aV, psiLin_cV, Doubling.hom_F]

lemma hom_gA (r j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]) :
    f.toLin (gA p N r j w n) = gA p N' r j w (f.toLin n) := by
  simp only [gA, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
    map_smul, Doubling.hom_F, Doubling.hom_E, LinearMap.id_apply]

lemma hom_gC (r j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]) :
    f.toLin (gC p N r j w n) = gC p N' r j w (f.toLin n) := by
  simp only [gC, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
    map_smul, Doubling.hom_F, Doubling.hom_E, LinearMap.id_apply]

lemma psiLin_psiEL (r : ℕ) (b : Bool) (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]) :
    psiLin p f.toLin (psiEL p N r b j w n) = psiEL p N' r b j w (f.toLin n) := by
  cases b <;> simp only [psiEL] <;> split_ifs <;>
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_add, map_sub, map_smul, psiLin_aV,
      psiLin_cV, Doubling.hom_F, Doubling.hom_E, hom_gA, hom_gC]

lemma psiLin_F (r : ℕ) :
    psiLin p f.toLin ∘ₗ psiF p N r = psiF p N' r ∘ₗ psiLin p f.toLin := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · simp only [LinearMap.comp_apply, psiLin_aV, psiF_aV p _ r hj, psiLin_psiFL]
  · simp only [LinearMap.comp_apply, psiLin_cV, psiF_cV p _ r hj, psiLin_psiFL]

lemma psiLin_E (r : ℕ) :
    psiLin p f.toLin ∘ₗ psiE p N r = psiE p N' r ∘ₗ psiLin p f.toLin := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hδ := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply, psiLin_aV, psiE_aV p _ r hj hδ,
      psiE_aV p _ r hj (Doubling.hom_inWt f hδ), psiLin_psiEL]
  · have hδ := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply, psiLin_cV, psiE_cV p _ r hj hδ,
      psiE_cV p _ r hj (Doubling.hom_inWt f hδ), psiLin_psiEL]

lemma psiLin_H (r : ℕ) :
    psiLin p f.toLin ∘ₗ Hop (psiWt p N r) = Hop (psiWt p N' r) ∘ₗ psiLin p f.toLin := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hδ := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply, psiLin_aV, Doubling.Hop_of_inWt (inWt_aV r j hδ),
      Doubling.Hop_of_inWt (inWt_aV r j (Doubling.hom_inWt f hδ)), map_smul]
  · have hδ := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply, psiLin_cV, Doubling.Hop_of_inWt (inWt_cV r j hδ),
      Doubling.Hop_of_inWt (inWt_cV r j (Doubling.hom_inWt f hδ)), map_smul]

/-- (F1) For `f : Hom N N'`, the map `A_j n ↦ A_j f(n)`, `C_j n ↦ C_j f(n)` (`psiLin`, i.e.
`id ⊗ f` on `Bool × Fin p × −`) as a morphism `Hom (psi p N r …) (psi p N' r …)`. -/
def psiHom (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : Hom (psi p N r h1 h2) (psi p N' r h1 h2) :=
  Q0c (psiLin p f.toLin) (by rw [psi_Fd1, psi_Fd1]; exact psiLin_F p f r)
    (by rw [psi_Ed1, psi_Ed1]; exact psiLin_E p f r) (psiLin_H p f r)

/-- (F1) `psiHom p r f` is a morphism `Hom (psi p N r …) (psi p N' r …)` sending `A_j n` to
`A_j f(n)` and `C_j n` to `C_j f(n)`. -/
theorem F1 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]),
      (psiHom p f r h1 h2).toLin (aV p j n) = aV p j (f.toLin n)) ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]),
      (psiHom p f r h1 h2).toLin (cV p j n) = cV p j (f.toLin n)) :=
  ⟨psiLin_aV p f.toLin, psiLin_cV p f.toLin⟩

/-! ### (F2) -/

/-- (F2) `Ψ_r` sends `Hom.id N` to `Hom.id (psi p N r …)` and `g ∘ f` to
`psiHom g ∘ psiHom f`. -/
theorem F2 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    (∀ N : DPLattice ℤ_[p],
      psiHom p (WeylFilt.Hom.id N) r h1 h2 = WeylFilt.Hom.id (psi p N r h1 h2)) ∧
    (∀ {N N' N'' : DPLattice ℤ_[p]} (g : Hom N' N'') (f : Hom N N'),
      psiHom p (WeylFilt.Hom.comp g f) r h1 h2 =
        WeylFilt.Hom.comp (psiHom p g r h1 h2) (psiHom p f r h1 h2)) :=
  ⟨fun _ => WeylFilt.Hom.ext' (psiLin_id p),
    fun g f => WeylFilt.Hom.ext' (psiLin_comp p g.toLin f.toLin)⟩

end ColouredSand.OddTwist
