module

public import RequestProject.Dance.Basic

/-!
# Part D, (D2), of `C13_the_dance.md`: the clocks are free quotients

* `card_Idx`: the tower `T(ds)` has `2^{n(ds) + m(ds)}` indices.
* `sysFinEquiv`: `Sys(T(ds), Fin r) ≃ (Fin (r · 2^{n(ds)+m(ds)}) → A)` (a choice of basis).
* `quotSmulTopCongr`, `quotSmulTopProd`: `M ⧸ c⊤` is functorial in linear equivalences, and
  `(X ⧸ c⊤) × (Y ⧸ c⊤) ≅ (X × Y) ⧸ c⊤`.
* **(D2)** `D2_clocks`: `Clocks(ds, r, h) ≅ Π_{j < n(ds)} ((Fin (r·2^{n(ds)+m(ds)−1−j}) → A) ⧸ 2^{h+j}·⊤)`.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment
open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- The tower `T(ds)` has `2^{n(ds) + m(ds)}` indices (`Φ` doubles them, `Ψ` multiplies them by
`4`) (*Part D*, (D2), *Proof*, of `C13_the_dance.md`). -/
lemma card_Idx (ds : List Bool) : Fintype.card (Idx ds) = 2 ^ (nLen ds + mCount ds) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    cases d
    · change Fintype.card (Idx rest × Fin 2) = _
      rw [Fintype.card_prod, ih, Fintype.card_fin]
      simp only [nLen, List.length_cons, mCount]
      ring
    · change Fintype.card (Idx rest × Fin 4) = _
      rw [Fintype.card_prod, ih, Fintype.card_fin]
      simp only [nLen, List.length_cons, mCount]
      ring

/-- `(X → A) ≃ (Fin a → A)` for a finite type `X` with `a` elements (a choice of basis; *Part D*,
(D2), *Proof*, of `C13_the_dance.md`). -/
noncomputable def funFinEquiv (X : Type*) [Fintype X] {a : ℕ} (ha : Fintype.card X = a) :
    (X → A) ≃ₗ[A] (Fin a → A) :=
  LinearEquiv.funCongrLeft A A (Fintype.equivFinOfCardEq ha).symm

variable (A) in
/-- `Sys(T(ds), Fin r)` is free of rank `r · 2^{n(ds) + m(ds)}`:
`Sys(T(ds), Fin r) ≃ (Fin (r · 2^{n(ds)+m(ds)}) → A)` (*Part D*, (D2), *Proof*, of
`C13_the_dance.md`). -/
noncomputable def sysFinEquiv (ds : List Bool) (r : ℕ) :
    SysT A ds (Fin r) ≃ₗ[A] (Fin (r * 2 ^ (nLen ds + mCount ds)) → A) :=
  (DirectSum.linearEquivFunOnFintype A (Fin r × Idx ds) (fun _ => A)).trans
    (funFinEquiv _ (by rw [Fintype.card_prod, Fintype.card_fin, card_Idx]))

/-- A linear equivalence `M ≃ M'` induces `M ⧸ c·⊤ ≃ M' ⧸ c·⊤` (*Part D*, (D2), *Proof*, of
`C13_the_dance.md`). -/
noncomputable def quotSmulTopCongr {M M' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (E : M ≃ₗ[A] M') (c : A) :
    (M ⧸ c • (⊤ : Submodule A M)) ≃ₗ[A] (M' ⧸ c • (⊤ : Submodule A M')) :=
  Submodule.Quotient.equiv _ _ E (by
    change (c • (⊤ : Submodule A M)).map (E : M →ₗ[A] M') = _
    rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range])

/-- `(X ⧸ c·⊤) × (Y ⧸ c·⊤) ≃ (X × Y) ⧸ c·⊤` (*Part D*, (D2), *Proof*, of `C13_the_dance.md`). -/
noncomputable def quotSmulTopProd {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (c : A) :
    ((X ⧸ c • (⊤ : Submodule A X)) × (Y ⧸ c • (⊤ : Submodule A Y))) ≃ₗ[A]
      ((X × Y) ⧸ c • (⊤ : Submodule A (X × Y))) :=
  ((quotProdEquiv _ _).symm).trans (Submodule.quotEquivOfEq _ _ (by
    ext ⟨x, y⟩
    simp only [Submodule.mem_prod, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and]
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, h⟩
      simp only [Prod.smul_mk, Prod.mk.injEq] at h
      exact ⟨⟨a, h.1⟩, ⟨b, h.2⟩⟩))

variable (A) in
/-- The factor `(Fin a → A) ⧸ 2^e·⊤` of (D2) of `C13_the_dance.md`. -/
abbrev PQ (a e : ℕ) : Type u := (Fin a → A) ⧸ (2 : A) ^ e • (⊤ : Submodule A (Fin a → A))

/-- `PQ a e ≃ PQ b e'` when `a = b` and `e = e'` (*Part D*, (D2), of `C13_the_dance.md`). -/
noncomputable def pqCast {a b e e' : ℕ} (ha : a = b) (he : e = e') :
    PQ A a e ≃ₗ[A] PQ A b e' := by
  subst ha he; exact LinearEquiv.refl A _

/-- `(Fin a → A) × (Fin a → A) ≃ (Fin (2a) → A)` (*Part D*, (D2), *Proof*, of
`C13_the_dance.md`). -/
noncomputable def finProdFinFun (a : ℕ) : ((Fin a → A) × (Fin a → A)) ≃ₗ[A] (Fin (a + a) → A) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin a) A A).symm.trans
    (LinearEquiv.funCongrLeft A A finSumFinEquiv.symm)

/-- **(D2) The clocks are free quotients with the paper's counts** of `C13_the_dance.md`: for
every `ds`, `r`, `h`,
`Clocks(ds, r, h) ≅ Π_{j < n(ds)} ((Fin (r · 2^{n(ds) + m(ds) − 1 − j}) → A) ⧸ 2^{h+j}·⊤)`
as `A`-modules. -/
theorem D2_clocks (ds : List Bool) : ∀ (r h : ℕ),
    Nonempty ((Clocks A ds r h) ≃ₗ[A] ((j : Fin (nLen ds)) →
      (Fin (r * 2 ^ (nLen ds + mCount ds - 1 - j)) → A) ⧸
        (2 : A) ^ (h + (j : ℕ)) •
          (⊤ : Submodule A (Fin (r * 2 ^ (nLen ds + mCount ds - 1 - j)) → A)))) := by
  induction ds with
  | nil =>
    intro r h
    haveI : Subsingleton (Clocks A [] r h) := inferInstanceAs (Subsingleton PUnit)
    haveI : IsEmpty (Fin (nLen ([] : List Bool))) := inferInstanceAs (IsEmpty (Fin 0))
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | cons d rest ih =>
    intro r h
    obtain ⟨e⟩ := ih (if d then r * 2 else r) (h + 1)
    cases d with
    | false =>
      let M : Fin (nLen rest + 1) → Type u := fun j =>
        PQ A (r * 2 ^ (nLen rest + 1 + mCount rest - 1 - j)) (h + j)
      let e0 : (SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r))))
          ≃ₗ[A] M 0 :=
        (quotSmulTopCongr (sysFinEquiv A rest r) _).trans
          (pqCast (by simp) (by simp))
      let e1 : ((j : Fin (nLen rest)) →
          PQ A (r * 2 ^ (nLen rest + mCount rest - 1 - j)) (h + 1 + j)) ≃ₗ[A]
          ((j : Fin (nLen rest)) → M j.succ) :=
        LinearEquiv.piCongrRight fun j => pqCast (by simp only [Fin.val_succ]; congr 2; omega)
          (by simp only [Fin.val_succ]; omega)
      exact ⟨(LinearEquiv.prodCongr e0 (e.trans e1)).trans (Fin.consLinearEquiv A M)⟩
    | true =>
      let M : Fin (nLen rest + 1) → Type u := fun j =>
        PQ A (r * 2 ^ (nLen rest + 1 + (mCount rest + 1) - 1 - j)) (h + j)
      have ha : r * 2 ^ (nLen rest + mCount rest) + r * 2 ^ (nLen rest + mCount rest) =
          r * 2 ^ (nLen rest + 1 + (mCount rest + 1) - 1 - ((0 : Fin (nLen rest + 1)) : ℕ)) := by
        rw [Fin.val_zero, ← two_mul, ← mul_left_comm, ← pow_succ']
        congr 2
        omega
      let e0 : ((SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r)))) ×
          (SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r)))))
          ≃ₗ[A] M 0 :=
        (quotSmulTopProd _).trans ((quotSmulTopCongr
          ((LinearEquiv.prodCongr (sysFinEquiv A rest r) (sysFinEquiv A rest r)).trans
            (finProdFinFun _)) _).trans
          (pqCast ha (by simp)))
      let e1 : ((j : Fin (nLen rest)) →
          PQ A (r * 2 * 2 ^ (nLen rest + mCount rest - 1 - j)) (h + 1 + j)) ≃ₗ[A]
          ((j : Fin (nLen rest)) → M j.succ) :=
        LinearEquiv.piCongrRight fun j => pqCast
          (by
            simp only [Fin.val_succ]
            rw [mul_assoc, ← pow_succ']
            congr 2
            have := j.isLt
            omega)
          (by simp only [Fin.val_succ]; omega)
      exact ⟨((LinearEquiv.prodAssoc A _ _ _).symm.trans
        (LinearEquiv.prodCongr e0 (e.trans e1))).trans (Fin.consLinearEquiv A M)⟩

end Dance
