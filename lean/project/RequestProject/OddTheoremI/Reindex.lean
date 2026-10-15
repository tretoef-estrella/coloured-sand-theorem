module

public import RequestProject.OddTheoremI.Basic
public import RequestProject.OddPayment.Chain

/-!
# `CSI10_theorem_Dp_and_theorem_I.md`, Part D — linear algebra for the proof of (D1)

Namespace `ColouredSand.OddTwist`. General facts used in the proof of Theorem D_p:

* **Reindexing a system** (the file's "reindex `Payment.Sys` along `eTw` / `ePsi`"): for an
  equivalence of index types `e : κ ≃ ι`, `sysRe e : Sys (fun _ : ι => A) S ≃ Sys (fun _ : κ => A) S`
  (on coefficient functions `x ↦ ((s, k) ↦ x (s, e k))`), and `sysRe_comp_Gp`: it carries the system
  `Gp p fl (opDS (Equiv.refl ι) T) Q` to `Gp p (fl ∘ e) (opDS e T) Q` (`opDS` from CSI9).
* **Counting the torsion factors**: `quotFinEquiv` (`(X → A) ⧸ c • ⊤ ≃ (Fin |X| → A ⧸ (c))`),
  `sysQuotEquiv` (`Sys (fun _ : κ => A) S ⧸ c • ⊤ ≃ (Fin (|κ| · |S|) → A ⧸ (c))`) and
  `piFinQuotEquiv` (`(Fin m → Sys ⧸ c • ⊤) ≃ (Fin (m · |κ| · |S|) → A ⧸ (c))`). Here `A ⧸ (c)` is
  `A ⧸ Ideal.span {c}`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]

/-! ### Function form of a constant system -/

variable (A) in
/-- The module of a system with all modules `A`, as functions on `S × ι`. -/
def sysFun (S ι : Type*) [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι] :
    Payment.Sys (fun _ : ι => A) S ≃ₗ[A] (S × ι → A) :=
  DirectSum.linearEquivFunOnFintype A (S × ι) (fun _ => A)

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma sysFun_lof {ι : Type*} [Fintype ι] [DecidableEq ι] (q : S × ι) (a : A) :
    sysFun A S ι (DirectSum.lof A (S × ι) (fun q => (fun _ : ι => A) q.2) q a) = Pi.single q a :=
  DirectSum.linearEquivFunOnFintype_lof ..

lemma sysFun_oslotE {ι : Type*} [Fintype ι] [DecidableEq ι] (s₀ : S) (y : ⨁ _ : ι, A)
    (s : S) (k : ι) :
    sysFun A S ι (oslotE A (fun _ : ι => A) S s₀ y) (s, k) =
      if s = s₀ then dsE A ι y k else 0 := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of j a =>
    rw [← DirectSum.lof_eq_of A]
    simp only [oslotE, DirectSum.toModule_lof, oslot]
    rw [sysFun_lof, dsE_lof]
    by_cases hs : s = s₀
    · subst hs; by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    · simp [hs]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; split_ifs <;> simp

/-- The function form of a constant system with operator `opDS e T` (CSI7's `Gp`):
`(G x)(s, k) = T (x(s, ·) ∘ e.symm) (e k) + Σ_{s'} p Q(fl k) s s' x(s', k)`. -/
lemma sysFun_Gp {κ ι : Type*} [Fintype κ] [DecidableEq κ] (p : ℕ) (fl : κ → ℕ) (e : κ ≃ ι)
    (T : Module.End A (ι → A)) (Q : ℕ → Matrix S S A) (x : Payment.Sys (fun _ : κ => A) S)
    (s : S) (k : κ) :
    sysFun A S κ (Gp p fl (opDS e T) Q x) (s, k) =
      T (fun j => sysFun A S κ x (s, e.symm j)) (e k) +
        ∑ s', (p : A) * Q (fl k) s s' * sysFun A S κ x (s', k) := by
  induction x using DirectSum.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    have : (fun _ : ι => (0 : A)) = 0 := rfl
    rw [this, map_zero, Pi.zero_apply]
  | of q a =>
    obtain ⟨s₀, k₀⟩ := q
    rw [← DirectSum.lof_eq_of A]
    simp only [Gp, DirectSum.toModule_lof, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [sysFun_oslotE, dsE_opDS, dsE_lof]
    simp only [oslot, sysFun_lof]
    congr 1
    · by_cases hs : s = s₀
      · subst hs
        rw [if_pos rfl]
        have : (fun j => (Pi.single (s, k₀) a : S × κ → A) (s, e.symm j)) =
            Pi.single k₀ a ∘ e.symm := by
          funext j; simp [Pi.single_apply]
        rw [this]
        rfl
      · rw [if_neg hs]
        have : (fun j => (Pi.single (s₀, k₀) a : S × κ → A) (s, e.symm j)) = 0 := by
          funext j; simp [hs]
        rw [this, map_zero, Pi.zero_apply]
    · simp only [Pi.single_apply, Prod.mk.injEq]
      by_cases hk : k = k₀
      · subst hk
        simp [Finset.sum_ite_eq']
      · simp [hk]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
    have : (fun j => sysFun A S κ x (s, e.symm j) + sysFun A S κ y (s, e.symm j)) =
        (fun j => sysFun A S κ x (s, e.symm j)) + (fun j => sysFun A S κ y (s, e.symm j)) := rfl
    rw [this, map_add, Pi.add_apply]
    ring

variable (A S) in
/-- **Reindexing a system** along `e : κ ≃ ι` (Part D of `CSI10_theorem_Dp_and_theorem_I.md`): on
coefficient functions, `x ↦ ((s, k) ↦ x (s, e k))`. -/
def sysRe {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (e : κ ≃ ι) :
    Payment.Sys (fun _ : ι => A) S ≃ₗ[A] Payment.Sys (fun _ : κ => A) S :=
  (sysFun A S ι).trans ((LinearEquiv.funCongrLeft A A (Equiv.prodCongr (Equiv.refl S) e)).trans
    (sysFun A S κ).symm)

lemma sysFun_sysRe {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (e : κ ≃ ι) (x : Payment.Sys (fun _ : ι => A) S) (s : S) (k : κ) :
    sysFun A S κ (sysRe A S e x) (s, k) = sysFun A S ι x (s, e k) := by
  simp only [sysRe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  rfl

/-- `sysRe e` carries `Gp p fl (opDS refl T) Q` to `Gp p (fl ∘ e) (opDS e T) Q` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`: "reindex `Payment.Sys` along `eTw` / `ePsi`"). -/
lemma sysRe_comp_Gp {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (p : ℕ) (fl : ι → ℕ) (e : κ ≃ ι) (T : Module.End A (ι → A)) (Q : ℕ → Matrix S S A) :
    (sysRe A S e).toLinearMap ∘ₗ Gp p fl (opDS (Equiv.refl ι) T) Q =
      Gp p (fl ∘ e) (opDS e T) Q ∘ₗ (sysRe A S e).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  apply (sysFun A S κ).injective
  funext ⟨s, k⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [sysFun_sysRe, sysFun_Gp, sysFun_Gp]
  simp only [sysFun_sysRe, Equiv.apply_symm_apply, Equiv.refl_symm, Equiv.refl_apply,
    Function.comp_apply]

/-- The cokernel of `c • G` is invariant under a conjugation (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
noncomputable def quotConj {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (Φ : M ≃ₗ[A] M') (G : Module.End A M) (G' : Module.End A M')
    (hG : Φ.toLinearMap ∘ₗ G = G' ∘ₗ Φ.toLinearMap) :
    (M ⧸ LinearMap.range G) ≃ₗ[A] (M' ⧸ LinearMap.range G') :=
  Submodule.Quotient.equiv _ _ Φ (by
    rw [← LinearMap.range_comp, hG, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 Φ.surjective)

/-! ### Counting the torsion factors -/

lemma smul_top_eq_span (c : A) : c • (⊤ : Submodule A A) = Ideal.span {c} := by
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    Ideal.mem_span_singleton', smul_eq_mul]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩

lemma map_smul_top {Y Z : Type*} [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (e : Y ≃ₗ[A] Z) (c : A) :
    (c • (⊤ : Submodule A Y)).map (e : Y →ₗ[A] Z) = c • (⊤ : Submodule A Z) := by
  ext z
  simp only [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨e w, by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨c • e.symm w, ⟨e.symm w, rfl⟩, by simp⟩

/-- `Y ⧸ c • ⊤` is transported along a linear equivalence. -/
noncomputable def quotSmulCongr {Y Z : Type*} [AddCommGroup Y] [Module A Y] [AddCommGroup Z]
    [Module A Z] (e : Y ≃ₗ[A] Z) (c : A) :
    (Y ⧸ c • (⊤ : Submodule A Y)) ≃ₗ[A] (Z ⧸ c • (⊤ : Submodule A Z)) :=
  Submodule.Quotient.equiv _ _ e (map_smul_top e c)

/-- `(Fin n → A) ⧸ c • ⊤ ≃ (Fin n → A ⧸ (c))`. -/
noncomputable def finQuotEquiv (n : ℕ) (c : A) :
    ((Fin n → A) ⧸ c • (⊤ : Submodule A (Fin n → A))) ≃ₗ[A] (Fin n → A ⧸ Ideal.span {c}) :=
  ((Submodule.quotEquivOfEq _ _ (smul_top_pi_eq (X := A) c)).trans
    (Submodule.quotientPi _)).trans
    (LinearEquiv.piCongrRight fun _ => Submodule.quotEquivOfEq _ _ (smul_top_eq_span c))

/-- `(X → A) ⧸ c • ⊤ ≃ (Fin |X| → A ⧸ (c))` for a finite type `X`. -/
noncomputable def quotFinEquiv (X : Type*) [Fintype X] (c : A) :
    ((X → A) ⧸ c • (⊤ : Submodule A (X → A))) ≃ₗ[A] (Fin (Fintype.card X) → A ⧸ Ideal.span {c}) :=
  (quotSmulCongr (LinearEquiv.funCongrLeft A A (Fintype.equivFin X).symm) c).trans
    (finQuotEquiv _ c)

/-- Changing the number of copies along an equality. -/
noncomputable def finCongrPi {B : Type*} [AddCommGroup B] [Module A B] {m n : ℕ} (h : m = n) :
    (Fin m → B) ≃ₗ[A] (Fin n → B) :=
  LinearEquiv.funCongrLeft A B (finCongr h).symm

/-- `(Fin m → Fin n → B) ≃ (Fin (m n) → B)`. -/
noncomputable def finPiPi (B : Type*) [AddCommGroup B] [Module A B] (m n : ℕ) :
    (Fin m → Fin n → B) ≃ₗ[A] (Fin (m * n) → B) :=
  (LinearEquiv.curry A B (Fin m) (Fin n)).symm.trans
    (LinearEquiv.funCongrLeft A B finProdFinEquiv.symm)

/-- `Sys (fun _ : κ => A) S ⧸ c • ⊤ ≃ (Fin (|κ| · |S|) → A ⧸ (c))` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`: the factor `Sys/c` of a move). -/
noncomputable def sysQuotEquiv (κ : Type*) [Fintype κ] [DecidableEq κ] (c : A) :
    (Payment.Sys (fun _ : κ => A) S ⧸ c • (⊤ : Submodule A (Payment.Sys (fun _ : κ => A) S)))
      ≃ₗ[A] (Fin (Fintype.card κ * Fintype.card S) → A ⧸ Ideal.span {c}) :=
  ((quotSmulCongr (sysFun A S κ) c).trans (quotFinEquiv _ c)).trans
    (finCongrPi (by rw [Fintype.card_prod, mul_comm]))

/-- `(Fin m → Sys ⧸ c • ⊤) ≃ (Fin (m · |κ| · |S|) → A ⧸ (c))` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`: the `(p−1)` resp. `2(p−1)` copies of `Sys/c`). -/
noncomputable def piFinQuotEquiv (m : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ] (c : A) :
    (Fin m → Payment.Sys (fun _ : κ => A) S ⧸ c • (⊤ : Submodule A (Payment.Sys (fun _ : κ => A) S)))
      ≃ₗ[A] (Fin (m * (Fintype.card κ * Fintype.card S)) → A ⧸ Ideal.span {c}) :=
  (LinearEquiv.piCongrRight fun _ => sysQuotEquiv κ c).trans (finPiPi _ _ _)

end ColouredSand.OddTwist
