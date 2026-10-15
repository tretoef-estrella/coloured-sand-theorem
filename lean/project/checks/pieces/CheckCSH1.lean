import RequestProject.ThmH.All

/-! CheckCSH1 — Grepy Sand, 13 Oct 2026. Theorem H of «The Coloured Sand Theorem» (paper v3,
doi:10.5281/zenodo.23329314): the prime 2, every d. Restated by hand with the objects written on
their face: the operator q(c+H)+U, X_q(m,c) as a quotient, the sandpile group as the torsion of the
cokernel of the Laplacian, and the family group as the cokernel of F + 2^{e−1}(λ + 2i − H) on T(λ). -/

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.ThmH FamDec Families Filt

-- the objects, on their face
#print ColouredSand.Strings.opM
#print ColouredSand.Strings.H
#print ColouredSand.Strings.U
#print ColouredSand.Splitting.Xq
#print ColouredSand.Splitting.Mq
#print ColouredSand.TheoremB.sandpile
#print ColouredSand.TheoremB.cokerL
#print FamilyGroup.X
#print Families.sigL
#print ColouredSand.ThmH.Psi
#print ColouredSand.ThmH.beta
#check @FamDec.D2
#check @Families.B2Z

-- (D1)–(D3) as stated
#check @ColouredSand.ThmH.D1
#check @ColouredSand.ThmH.D2
#check @ColouredSand.ThmH.D3

-- (T1) restated by hand: the operator written out, and the family group written as the cokernel of
-- σ = F + 2^{e−1}((λ + 2i)·id − H) on T(λ), with i = c + (m − λ)/2.
example (e m c : ℕ) (he : 1 ≤ e) :
    Nonempty ((B m ℤ_[2] ⧸ LinearMap.range
        (((2 : ℤ_[2]) ^ e) • ((c : ℤ_[2]) • LinearMap.id + H m ℤ_[2]) + U m ℤ_[2])) ≃ₗ[ℤ_[2]]
      ((j : Fin (L m).length) →
        (((T ℤ_[2] ((L m).get j)).ι → ℤ_[2]) ⧸ LinearMap.range
          ((T ℤ_[2] ((L m).get j)).Fd 1 + ((2 : ℤ_[2]) ^ (e - 1)) •
            ((((L m).get j : ℤ_[2]) + 2 * (((c + (m - (L m).get j) / 2 : ℕ)) : ℤ_[2])) •
                LinearMap.id - DPLattice.H (T ℤ_[2] ((L m).get j))))))) := by
  obtain ⟨φ⟩ := T1 e m c he
  exact ⟨φ.trans (LinearEquiv.piCongrRight fun j => (sigEquivZ _ _ _).symm)⟩

-- (T3) restated by hand: X_q(m,c) written as B_m(ℤ) modulo the range of q(c+H)+U.
example (q m c : ℕ) (hq : 1 ≤ q) (heven : Even q) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (B m ℤ ⧸ LinearMap.range
          (((q : ℤ)) • (((c : ℤ)) • LinearMap.id + H m ℤ) + U m ℤ))) 2) ≃+
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) (padicValNat 2 q) (c + (m - (L m).get j) / 2))) :=
  T3 q m c hq heven

-- (T4) restated by hand: the sandpile group written as the torsion of the cokernel of the
-- Laplacian of H(d,q), Syl_2 as Mathlib's primary component.
example (d q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) 2) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (L (d - σ.1)).length) →
          FamilyGroup.X (ds ((L (d - σ.1)).get t)) (padicValNat 2 q)
            (σ.1 + (d - σ.1 - (L (d - σ.1)).get t) / 2))) :=
  T4 d q hq heven

-- (T5) the cube Q_d = H(d,2)
example (d : ℕ) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin 2) → ℤ) ⧸ LinearMap.range (laplacian d 2))) 2) ≃+
      ((t : Fin (L d).length) → FamilyGroup.X (ds ((L d).get t)) 1 ((d - (L d).get t) / 2))) :=
  T5 d

#check @ColouredSand.ThmH.T2
#check @ColouredSand.ThmH.N1
#check @ColouredSand.ThmH.N2_lists
#check @ColouredSand.ThmH.N2_halves

#print axioms ColouredSand.ThmH.D1
#print axioms ColouredSand.ThmH.D2
#print axioms ColouredSand.ThmH.D3
#print axioms ColouredSand.ThmH.freeTorsionEquiv
#print axioms ColouredSand.ThmH.T1
#print axioms ColouredSand.ThmH.T2
#print axioms ColouredSand.ThmH.T3
#print axioms ColouredSand.ThmH.T4
#print axioms ColouredSand.ThmH.T5
#print axioms ColouredSand.ThmH.T5_exponent
#print axioms ColouredSand.ThmH.N1
#print axioms ColouredSand.ThmH.N2_lists
#print axioms ColouredSand.ThmH.N2_halves
