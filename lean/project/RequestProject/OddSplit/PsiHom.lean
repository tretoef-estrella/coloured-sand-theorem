module

public import RequestProject.OddSplit.Psi

/-!
# `CSI3_the_split.md`: (I6) and (B4) — `ι` as a morphism, and `Ψ_1(N) ≅ V ⊗ Φ_p(N)`

* `iotaHom p N s hs1 hsp : Hom (psi p N (s + 1) …) (Tensor2.tensor (V ℤ_[p]) (psi p N s …))` is
  the map `ι` of (I1) (for `r = s + 1`, i.e. `2 ≤ r ≤ p − 1`), built with (Q0c).
* `kappaHom p N : Hom (psi p N 1 …) (Tensor2.tensor (V ℤ_[p]) (twist p N))` is the map `κ` of
  (B1), and `kappaIso p N` the isomorphism of (B4) (`Doubling.Iso.ofInverse` with `κ⁻¹` of (B2)).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-! ### (I6) -/

/-- (I6) `ι` (of (I1), for `r = s + 1`) as a morphism
`Hom (psi p N r …) (Tensor2.tensor (V ℤ_[p]) (psi p N (r − 1) …))`. -/
def iotaHom (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    Hom (psi p N (s + 1) (by omega) (by omega))
      (Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))) :=
  Q0c (iota (psiD p N s hs1 (by omega)))
    (by rw [psi_Fd1]; exact iota_F _ hs1 hsp)
    (by rw [psi_Ed1]; exact iota_E _ hs1 hsp)
    (iota_H _ hs1 hsp)

/-- (I6) (Prop 1.4 (b)) For `2 ≤ r ≤ p − 1` (written `r = s + 1`): the morphism `iotaHom` has
underlying linear map `ι` of (I1), it is injective, and `ρ` of (I3) is a left inverse. -/
theorem I6 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    (iotaHom p N s hs1 hsp).toLin = iota (psiD p N s hs1 (by omega)) ∧
    Function.Injective (iotaHom p N s hs1 hsp).toLin ∧
    rho (psiD p N s hs1 (by omega)) ∘ₗ (iotaHom p N s hs1 hsp).toLin = LinearMap.id := by
  have h := rho_iota (psiD p N s hs1 (by omega)) hs1 hsp
  refine ⟨rfl, fun x y hxy => ?_, h⟩
  have := congrArg (rho (psiD p N s hs1 (by omega))) hxy
  have hx := LinearMap.congr_fun h x
  have hy := LinearMap.congr_fun h y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  exact hx.symm.trans (this.trans hy)

/-! ### (B4) -/

/-- (B4) `κ` of (B1) as a morphism `Hom (psi p N 1 …) (Tensor2.tensor (V ℤ_[p]) (twist p N))`. -/
def kappaHom (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Hom (psi p N 1 h1 h2) (Tensor2.tensor (V ℤ_[p]) (twist p N)) :=
  Q0c (kappa p N) (by rw [psi_Fd1]; exact kappa_F) (by rw [psi_Ed1]; exact kappa_E) kappa_H

/-- (B4) the isomorphism `psi p N 1 ≅ V ⊗ Φ_p(N)` given by `κ` and `κ⁻¹`. -/
def kappaIso (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Doubling.Iso (psi p N 1 h1 h2) (Tensor2.tensor (V ℤ_[p]) (twist p N)) :=
  Doubling.Iso.ofInverse (kappaHom p N h1 h2) (kappaInv p N) kappaInv_kappa kappa_kappaInv

/-- (B4) (Prop 1.4 (b), `r = 1`) `Ψ_1(N) ≅ V ⊗ Φ_p(N)`, via `κ` of (B1). -/
theorem B4_iso (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Nonempty (Doubling.Iso (psi p N 1 h1 h2) (Tensor2.tensor (V ℤ_[p]) (twist p N))) :=
  ⟨kappaIso p N h1 h2⟩

/-- (B4) the single operators of `psi p N 1`, together with the isomorphism. -/
theorem B4 (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    (psi p N 1 h1 h2).Fd 1 = psiF p N 1 ∧ (psi p N 1 h1 h2).Ed 1 = psiE p N 1 ∧
    Nonempty (Doubling.Iso (psi p N 1 h1 h2) (Tensor2.tensor (V ℤ_[p]) (twist p N))) :=
  ⟨psi_Fd1 p N 1 h1 h2, psi_Ed1 p N 1 h1 h2, B4_iso p N h1 h2⟩

end ColouredSand.OddTwist
