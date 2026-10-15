module

public import RequestProject.OddSES.PartS1b

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S2)–(S3) — the maps `π_r` and `π_1`

Encodings:

* `r = s + 1` with `1 ≤ s` and `s + 2 ≤ p` (so `2 ≤ r ≤ p − 1`); `Z_r` is
  `Tensor2.tensor (V ℤ_[p]) (psi p N (s+1) _ _)` and `ι_r` is CSI3's
  `iotaHom p N s hs1 hsp : Hom (psi p N (s+1) _ _) (V ⊗ psi p N s _ _)`.
* `piHom p N s hs1 hsp : Hom Z_r (psi p N s _ _)` is `π_r`, the composite
  `contr ∘ (id_V ⊗ ι_r)` where `contr = (unit) ∘ (ω ⊗ id) ∘ assoc⁻¹` (`contrHom`, identifying
  `one ⊗ M` with `M` via C23's `unitLeftIso`).
* `pi1Hom p N h1 h2 : Hom Z_1 (dsum (twist p N) (twist p N))` is `π_1`, the pair
  `(contr ∘ (id_V ⊗ κ), act ∘ (id_V ⊗ κ))` (`pairHom`), with `κ = kappaHom p N h1 h2` of CSI3 (B1)
  and `act` the action of `Sym² V ≅ 𝔤` times 2 (`actHom`). A vector of the `dsum` is a function
  on `ι ⊕ ι`, i.e. `Sum.elim (first component) (second component)`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

/-- `(id_V ⊗ g)(b̂_e ⊗ x) = b̂_e ⊗ g x`. -/
lemma kronHom_id_tv {A : Type*} [CommRing A] {M M' : DPLattice A} (g : Hom M M') (e : Fin 2)
    (x : M.ι → A) :
    (Tensor2.kronHom (WeylFilt.Hom.id (V A)) g).toLin (tv e x) = tv e (g.toLin x) :=
  Tensor2.kron_tprod _ _ _ _

/-- `contr (b̂_e ⊗ (b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1))`: `y_1` for `e = 0`, `−y_0` for `e = 1`. -/
lemma contr_tv_pair {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (M : DPLattice A)
    (y0 y1 : M.ι → A) :
    (contrHom M).toLin (tv 0 (tv 0 y0 + tv 1 y1)) = y1 ∧
    (contrHom M).toLin (tv 1 (tv 0 y0 + tv 1 y1)) = -y0 := by
  constructor
  · rw [map_add, map_add, contr_tv00, contr_tv01, zero_add]
  · rw [map_add, map_add, contr_tv10, contr_tv11, add_zero]

/-- `act (b̂_e ⊗ (b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1))`: `2E y_0 − H y_1` for `e = 0`, `−H y_0 − 2F y_1` for
`e = 1`. -/
lemma act_tv_pair {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (M : DPLattice A)
    (y0 y1 : M.ι → A) :
    (actHom M).toLin (tv 0 (tv 0 y0 + tv 1 y1)) = (2 : A) • M.Ed 1 y0 - H M y1 ∧
    (actHom M).toLin (tv 1 (tv 0 y0 + tv 1 y1)) = -H M y0 - (2 : A) • M.Fd 1 y1 := by
  rw [actHom, Q0c_toLin]
  constructor
  · rw [map_add, map_add, actL_00, actL_01, sub_eq_add_neg]
  · rw [map_add, map_add, actL_10, actL_11, sub_eq_add_neg]

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-! ### (S2) `π_r`, `2 ≤ r ≤ p − 1` -/

/-- (S2) `π_r : Z_r → psi p (r−1) N` for `r = s + 1`, `2 ≤ r ≤ p − 1`: the composite
`(ω ⊗ id) ∘ assoc⁻¹ ∘ (id_V ⊗ ι_r)` (followed by the identification `one ⊗ M ≅ M`). -/
def piHom (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    Hom (Tensor2.tensor (V ℤ_[p]) (psi p N (s + 1) (by omega) (by omega)))
      (psi p N s hs1 (by omega)) :=
  WeylFilt.Hom.comp (contrHom (psi p N s hs1 (by omega)))
    (Tensor2.kronHom (WeylFilt.Hom.id (V ℤ_[p])) (iotaHom p N s hs1 hsp))

/-- (S2) **The formula for `π_r`**, `r = s + 1`, `2 ≤ r ≤ p − 1`: if
`ι_r(x) = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1`, then `π_r(b̂_0 ⊗ x) = y_1` and `π_r(b̂_1 ⊗ x) = −y_0`. -/
theorem S2 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
    (x : (psi p N (s + 1) (by omega) (by omega)).ι → ℤ_[p])
    (y0 y1 : (psi p N s hs1 (by omega)).ι → ℤ_[p])
    (h : (iotaHom p N s hs1 hsp).toLin x = tv 0 y0 + tv 1 y1) :
    (piHom p N s hs1 hsp).toLin (tv 0 x) = y1 ∧ (piHom p N s hs1 hsp).toLin (tv 1 x) = -y0 := by
  simp only [piHom, WeylFilt.Hom.comp, LinearMap.comp_apply]
  rw [kronHom_id_tv, kronHom_id_tv, h]
  exact contr_tv_pair _ y0 y1

/-! ### (S3) `π_1` -/

/-- (S3) `π_1 : Z_1 → dsum (twist p N) (twist p N)`: first component `contr ∘ (id_V ⊗ κ)`,
second component `act ∘ (id_V ⊗ κ)`. -/
def pi1Hom (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Hom (Tensor2.tensor (V ℤ_[p]) (psi p N 1 h1 h2)) (Lemma35.dsum (twist p N) (twist p N)) :=
  pairHom
    (WeylFilt.Hom.comp (contrHom (twist p N))
      (Tensor2.kronHom (WeylFilt.Hom.id (V ℤ_[p])) (kappaHom p N h1 h2)))
    (WeylFilt.Hom.comp (actHom (twist p N))
      (Tensor2.kronHom (WeylFilt.Hom.id (V ℤ_[p])) (kappaHom p N h1 h2)))

/-- (S3) **The formula for `π_1`**: if `κ(x) = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1`, then
`π_1(b̂_0 ⊗ x) = (y_1, 2E y_0 − H y_1)` and `π_1(b̂_1 ⊗ x) = (−y_0, −H y_0 − 2F y_1)`,
with `F, E, H` of `twist p N` (a vector of the `dsum` is `Sum.elim first second`). -/
theorem S3 (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) (x : (psi p N 1 h1 h2).ι → ℤ_[p])
    (y0 y1 : (twist p N).ι → ℤ_[p]) (h : kappa p N x = tv 0 y0 + tv 1 y1) :
    (pi1Hom p N h1 h2).toLin (tv 0 x) =
      Sum.elim y1 ((2 : ℤ_[p]) • (twist p N).Ed 1 y0 - H (twist p N) y1) ∧
    (pi1Hom p N h1 h2).toLin (tv 1 x) =
      Sum.elim (-y0) (-H (twist p N) y0 - (2 : ℤ_[p]) • (twist p N).Fd 1 y1) := by
  have hk : (kappaHom p N h1 h2).toLin x = tv 0 y0 + tv 1 y1 := by
    rw [kappaHom, Q0c_toLin]; exact h
  simp only [pi1Hom, pairHom_apply, WeylFilt.Hom.comp, LinearMap.comp_apply]
  rw [kronHom_id_tv, kronHom_id_tv, hk, (contr_tv_pair _ y0 y1).1, (contr_tv_pair _ y0 y1).2,
    (act_tv_pair _ y0 y1).1, (act_tv_pair _ y0 y1).2]
  exact ⟨rfl, rfl⟩

end ColouredSand.OddTwist
