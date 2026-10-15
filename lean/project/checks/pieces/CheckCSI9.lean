import RequestProject.OddLevels.All

/-!
# CheckCSI9 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI9 (`CSI9_last_level_and_floors.md`): Part L, the last level
(Proposition 2.3) over `ℤ_[p]` and over any ring in which `1, …, d − 1` are units, with
`Mlast = Q 0 ⋯ Q (d−1)` written out as a list product; Part G: the floor `flL` written out,
`wt = λ − 2 flL`, parity, `F` raises the floor by one, the base case `Δ(λ)`, the recursive
description (twist and split), (G2) the dance lattice as a moved graded family, (G3) the
operator `F + p^e (D_fl + i)` as a one-slot system, with `Q₀` and `D_fl` written out.
Then `#print axioms`.
-/

namespace CheckCSI9

open ColouredSand.OddTwist DirectSum DPLattice
open scoped Pointwise

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- `Mlast` written out. -/
theorem hMlast {A : Type*} [CommRing A] (Q : ℕ → Matrix S S A) (d : ℕ) :
    prodQ Q 0 d = ((List.range d).map Q).prod := by
  simp [prodQ]

/-- (L1) over `ℤ_[p]`, with `Mlast` as a list product. -/
theorem hL1 (p : ℕ) [Fact p.Prime] (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1)
    (Q : ℕ → Matrix S S ℤ_[p]) (c : ℤ_[p]) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => ℤ_[p]) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta ℤ_[p] (d - 1))) Q)) ≃ₗ[ℤ_[p]]
      ((Fin (d - 1) → (S → ℤ_[p]) ⧸ c • (⊤ : Submodule ℤ_[p] (S → ℤ_[p]))) ×
        ((S → ℤ_[p]) ⧸ LinearMap.range
          (c • (p : ℤ_[p]) ^ d • (((List.range d).map Q).prod).mulVecLin)))) := by
  rw [← hMlast]
  exact L1 p d hd1 hd2 Q c

/-- (L1) over any commutative ring in which `1, …, d − 1` are units. -/
theorem hL1general {A : Type*} [CommRing A] (p d : ℕ) (hd : 1 ≤ d)
    (hu : ∀ k : ℕ, 1 ≤ k → k < d → IsUnit (k : A)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => A) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta A (d - 1))) Q)) ≃ₗ[A]
      ((Fin (d - 1) → (S → A) ⧸ c • (⊤ : Submodule A (S → A))) ×
        ((S → A) ⧸ LinearMap.range
          (c • (p : A) ^ d • (((List.range d).map Q).prod).mulVecLin)))) := by
  rw [← hMlast]
  exact L1_general p d hd hu Q c

variable (p : ℕ) [Fact p.Prime]

/-- (G1): the floor written out, `wt = λ − 2 flL`, parity, and `F` raises the floor by one. -/
theorem hG1 (l : ℕ) (i j : (danceL p l).ι) :
    flL p l i = (((l : ℤ) - (danceL p l).wt i) / 2).toNat ∧
    (danceL p l).wt i = (l : ℤ) - 2 * (flL p l i : ℤ) ∧
    (danceL p l).wt i ≡ (l : ℤ) [ZMOD 2] ∧
    ((danceL p l).Fd 1 (Pi.single i 1) j ≠ 0 → flL p l j = flL p l i + 1) :=
  ⟨rfl, wt_danceL p l i, G1_parity p l i, G1_Fd p l i j⟩

/-- (G1), vector form: a vector on floor `φ` is sent to floor `φ + 1`. -/
theorem hG1vec (l φ : ℕ) (v : (danceL p l).ι → ℤ_[p])
    (hv : ∀ i, flL p l i ≠ φ → v i = 0) (j : (danceL p l).ι) (hj : flL p l j ≠ φ + 1) :
    (danceL p l).Fd 1 v j = 0 :=
  G1_Fd_floor p l φ v hv j hj

/-- (G1): base case and recursive description. -/
theorem hG1rec (l : ℕ) :
    (∀ (h : l + 1 < p) (r : Fin (l + 1)), flL p l ((idxDelta p l h).symm r) = r.val) ∧
    (∀ (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) (j : Fin p)
        (i : (danceL p ((l + 1) / p - 1)).ι),
      flL p l ((idxTw p l h hd).symm (j, i)) = p * flL p ((l + 1) / p - 1) i + j) ∧
    (∀ (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) (j : Fin p)
        (i : (danceL p ((l + 1) / p - 1)).ι),
      flL p l ((idxPsi p l h hd).symm (false, j, i)) = p * flL p ((l + 1) / p - 1) i + j ∧
      flL p l ((idxPsi p l h hd).symm (true, j, i)) =
        p * flL p ((l + 1) / p - 1) i + (l + 1) % p + j) :=
  ⟨G1_delta p l, G1_twist p l, G1_psi p l⟩

/-- (G2): the dance lattice is the twist / split of the previous one as a graded family. -/
theorem hG2 (l : ℕ) (h : ¬ l + 1 < p) :
    (∀ hd : (l + 1) % p = 0,
      (∀ q, flL p l (eTw p l h hd q) = flT p (flL p ((l + 1) / p - 1)) q) ∧
      opDS (eTw p l h hd) ((danceL p l).Fd 1) = FT p (famF (danceL p ((l + 1) / p - 1)))) ∧
    (∀ hd : 1 ≤ (l + 1) % p,
      (∀ q, flL p l (ePsi p l h hd q) = flS p ((l + 1) % p) (flL p ((l + 1) / p - 1)) q) ∧
      opDS (ePsi p l h hd) ((danceL p l).Fd 1) =
        FS p ((l + 1) % p) hd (famF (danceL p ((l + 1) / p - 1)))) :=
  ⟨G2_twist p l h, G2_psi p l h⟩

/-- `Q₀` and `D_fl` written out. -/
theorem hQ0Dop (e i φ : ℕ) {ι : Type*} (fl : ι → ℕ) (x : ι → ℤ_[p]) (j : ι) :
    Q0 ℤ_[p] p e i φ () () = (p : ℤ_[p]) ^ (e - 1) * ((φ : ℤ_[p]) + i) ∧
    Dop fl x j = (fl j : ℤ_[p]) * x j :=
  ⟨rfl, rfl⟩

/-- (G3): `F + p^e (D_fl + i)` on `danceL p λ` is the one-slot system with `Q₀`. -/
theorem hG3 (l e i : ℕ) (he : 1 ≤ e) :
    (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap ∘ₗ
        Gp p (flL p l) (famF (danceL p l)) (Q0 ℤ_[p] p e i) =
      ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
          (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p])))) ∘ₗ
        (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap :=
  G3_operator p l e i he

end CheckCSI9

#print axioms CheckCSI9.hMlast
#print axioms CheckCSI9.hL1
#print axioms CheckCSI9.hL1general
#print axioms CheckCSI9.hG1
#print axioms CheckCSI9.hG1vec
#print axioms CheckCSI9.hG1rec
#print axioms CheckCSI9.hG2
#print axioms CheckCSI9.hQ0Dop
#print axioms CheckCSI9.hG3
#print axioms ColouredSand.OddTwist.Gp_Q0_eq
#print axioms ColouredSand.OddTwist.opDS_twist
#print axioms ColouredSand.OddTwist.opDS_psi
