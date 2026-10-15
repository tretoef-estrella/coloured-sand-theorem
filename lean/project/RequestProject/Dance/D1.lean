module

public import RequestProject.Dance.Relabel

/-!
# Part D, (D1), of `C13_the_dance.md`: the scaled dance

* `D1_aux`: (D1) for the dance data `danceAux ds r p κ` on `Fin (slots ds r)` (induction on `ds`,
  as in the file's *Proof*).
* **(D1)** `D1_scaled_dance`: for every digit list `ds`, every `r`, all halved data `(p, κ)` on
  `Fin r` and every `h`,
  `Sys(T(ds), Fin r) ⧸ range(2^h · G[fl_ds, F_ds, p, κ]) ≅
    Clocks(ds, r, h) × Sys(T([]), Fin (r·2^{m(ds)})) ⧸ range(2^{h+n(ds)} · G[0, 0, dance ds r p κ])`.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment Split
open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- (D1) of `C13_the_dance.md` for the dance data `danceAux ds r p κ` on `Fin (slots ds r)`
(the recursion of the Setting before the final cast to `Fin (r * 2^{m(ds)})`); proved by induction
on `ds`, with Theorem A of C11 for a digit `false` and Theorem B of C12 followed by (R1) for a
digit `true` (*Part D*, (D1), *Proof*, of `C13_the_dance.md`). -/
theorem D1_aux (ds : List Bool) : ∀ (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A)
    (h : ℕ),
    Nonempty ((SysT A ds (Fin r) ⧸ LinearMap.range ((2 : A) ^ h • G (fl ds) (F A ds) p κ)) ≃ₗ[A]
      (Clocks A ds r h) × (SysT A [] (Fin (slots ds r)) ⧸
        LinearMap.range ((2 : A) ^ (h + nLen ds) •
          G (fl []) (F A []) (danceAux ds r p κ).1 (danceAux ds r p κ).2))) := by
  induction ds with
  | nil =>
    intro r p κ h
    haveI : Unique (Clocks A [] r h) := inferInstanceAs (Unique PUnit)
    exact ⟨LinearEquiv.uniqueProd.symm⟩
  | cons d rest ih =>
    intro r p κ h
    cases d with
    | false =>
      have h1 := theorem_A (N := fun _ : Idx rest => A) (S := Fin r) (fl rest) (F A rest) p κ
        ((2 : A) ^ h)
      rw [smul_smul, ← pow_succ] at h1
      obtain ⟨e1⟩ := h1
      obtain ⟨e2⟩ := ih r (pT p) (κT p κ) (h + 1)
      rw [show h + nLen (false :: rest) = h + 1 + nLen rest by simp only [nLen, List.length_cons]; omega]
      exact ⟨e1.trans ((LinearEquiv.prodCongr (LinearEquiv.refl A _) e2).trans
        (LinearEquiv.prodAssoc A _ _ _).symm)⟩
    | true =>
      have h1 := theorem_B (N := fun _ : Idx rest => A) (S := Fin r) (fl rest) (F A rest) p κ
        ((2 : A) ^ h)
      rw [smul_smul, ← pow_succ] at h1
      obtain ⟨e1⟩ := h1
      obtain ⟨e3⟩ := R1_coker (N := fun _ : Idx rest => A) (fl rest) (F A rest)
        (splitIso r).symm (pSp p) (κSp p κ) ((2 : A) ^ (h + 1))
      obtain ⟨e2⟩ := ih (r * 2) (relabP (splitIso r).symm (pSp p))
        (relabK (splitIso r).symm (κSp p κ)) (h + 1)
      rw [show h + nLen (true :: rest) = h + 1 + nLen rest by simp only [nLen, List.length_cons]; omega]
      exact ⟨e1.trans ((LinearEquiv.prodCongr (LinearEquiv.refl A _)
        (LinearEquiv.prodCongr (LinearEquiv.refl A _) (e3.symm.trans e2))).trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl A _) (LinearEquiv.prodAssoc A _ _ _).symm).trans
          (LinearEquiv.prodAssoc A _ _ _).symm))⟩

/-- **(D1) The scaled dance** of `C13_the_dance.md`: for every digit list `ds`, every `r`, all
halved data `(p, κ)` on `Fin r` for `T(ds)` and every `h ∈ ℕ`, there is an `A`-linear isomorphism
`Sys(T(ds), Fin r) ⧸ range(2^h · G[fl_ds, F_ds, p, κ])
  ≅ Clocks(ds, r, h) × Sys(T([]), Fin (r·2^{m(ds)})) ⧸ range(2^{h + n(ds)} · G[0, 0, dance ds r p κ])`.
-/
theorem D1_scaled_dance (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) (h : ℕ) :
    Nonempty ((SysT A ds (Fin r) ⧸ LinearMap.range ((2 : A) ^ h • G (fl ds) (F A ds) p κ)) ≃ₗ[A]
      (Clocks A ds r h) × (SysT A [] (Fin (r * 2 ^ mCount ds)) ⧸
        LinearMap.range ((2 : A) ^ (h + nLen ds) •
          G (fl []) (F A []) (dance ds r p κ).1 (dance ds r p κ).2))) := by
  obtain ⟨e1⟩ := D1_aux ds r p κ h
  obtain ⟨e2⟩ := R1_coker (N := fun _ : Idx [] => A) (fl []) (F A [])
    (Fin.castOrderIso (slots_eq ds r).symm) (danceAux ds r p κ).1 (danceAux ds r p κ).2
    ((2 : A) ^ (h + nLen ds))
  exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl A _) e2.symm)⟩

end Dance
