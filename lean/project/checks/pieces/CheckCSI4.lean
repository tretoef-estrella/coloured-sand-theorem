import RequestProject.OddSES.All

/-!
# CheckCSI4 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI4 (`CSI4_the_short_exact_sequences.md`):
the Casimir written out (C1); (C2) on `Ψ_s` with `p • (ι → ℤ_[p])` written as `∃ z, x = p • z`;
(C3) on `Φ_p`; (C4) on the ambient; `Ψ_p(N) := Φ_p(V ⊗ N)` and the slot correspondence (P1);
`α`, `γ` written out and `ι_p` on `b_j(b̂_e ⊗ n)` (P2); `ι_p` a morphism, injective, with a left
inverse (P3); `ω` (S1); `π_r`, `π_1` on `b̂_e ⊗ x` (S2, S3); surjectivity (S4); and the three short
exact sequences (S5) with their sources and targets written out. Then `#print axioms`.
-/

namespace CheckCSI4

open ColouredSand.OddTwist DPLattice

variable {p : ℕ} [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- The Casimir and `Ω − c`, by hand. -/
theorem hCas {A : Type*} [CommRing A] (M : DPLattice A) (c : A) :
    casimir M = (4 : A) • (M.Fd 1 ∘ₗ M.Ed 1) + (H M + 1) ^ 2 ∧
    Dcas M c = casimir M - c • LinearMap.id := ⟨rfl, rfl⟩

/-- `pSub p X` is `p • X`, by hand. -/
theorem hpSub {X : Type*} [AddCommGroup X] [Module ℤ_[p] X] (x : X) :
    x ∈ pSub p X ↔ ∃ z, x = (p : ℤ_[p]) • z := mem_pSub

/-- (C1) over any domain of characteristic 0. -/
theorem hC1 {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (M : DPLattice A) :
    casimir M ∘ₗ H M = H M ∘ₗ casimir M ∧
    (∀ r, casimir M ∘ₗ M.Fd r = M.Fd r ∘ₗ casimir M) ∧
    (∀ r, casimir M ∘ₗ M.Ed r = M.Ed r ∘ₗ casimir M) ∧
    (∀ (M' : DPLattice A) (f : Hom M M'), f.toLin ∘ₗ casimir M = casimir M' ∘ₗ f.toLin) :=
  by first | exact C1 M | exact C1 (M := M)

/-- (C2) on `Ψ_s`, `1 ≤ s ≤ p − 1`. -/
theorem hC2 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s ≤ p - 1) :
    (∀ (j : ℕ) (i : N.ι), j < p →
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) (aV p j (Pi.single i 1)) ∈ pSub p _) ∧
    (∀ (j : ℕ) (i : N.ι), j < p →
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) (cV p j (Pi.single i 1)) ∈
        ASpan p N ⊔ pSub p _) ∧
    ∃ R, Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) ∘ₗ
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) = (p : ℤ_[p]) • R :=
  by first | exact C2 s hs1 hsp | exact C2 (N := N) s hs1 hsp

/-- (C3) on `Φ_p(N)`. -/
theorem hC3 : ∃ R, casimir (twist p N) = (p : ℤ_[p]) • R := C3

/-- (C4) on the ambient `V ⊗ Ψ_r`, `1 ≤ r ≤ p − 1`, `p` odd. -/
theorem hC4 (hp3 : 3 ≤ p) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    ∃ R, (Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) + 1) ^ 2) ∘ₗ
        Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) + 1) ^ 2)) ∘ₗ
      (Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) - 1) ^ 2) ∘ₗ
        Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) - 1) ^ 2)) =
      (p : ℤ_[p]) • R :=
  by first | exact C4 hp3 r h1 h2 | exact C4 (N := N) hp3 r h1 h2

/-- (P1) `Ψ_p(N) := Φ_p(V ⊗ N)`, by hand. -/
theorem hPsip : Psip p N = twist p (Tensor2.tensor (V ℤ_[p]) N) := rfl

/-- (P1) the slot correspondence and the weights. -/
theorem hP1 :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), Pmap p N (aV p j n) = bv p j (tv 0 n)) ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), Pmap p N (cV p j n) = -bv p j (tv 1 n)) ∧
    (∀ (j : Fin p) (i : N.ι),
      (Psip p N).wt (j, ((0 : Fin 2), i)) = p * (N.wt i + 1) + p - 1 - 2 * ((j : ℕ) : ℤ)) ∧
    (∀ (j : Fin p) (i : N.ι),
      (Psip p N).wt (j, ((1 : Fin 2), i)) = p * (N.wt i - 1) + p - 1 - 2 * ((j : ℕ) : ℤ)) ∧
    Pmap p N ∘ₗ psiF p N p = (Psip p N).Fd 1 ∘ₗ Pmap p N ∧
    Pmap p N ∘ₗ psiE p N p = (Psip p N).Ed 1 ∘ₗ Pmap p N := by
  obtain ⟨_, _, a, c, w0, w1, f, e⟩ := P1 (p := p) (N := N)
  exact ⟨a, c, fun j i => (w0 j i).1, fun j i => (w1 j i).1, f, e⟩

/-- (P2) `α`, `γ` written out (CSI3 (I1) with `r = p`). -/
theorem hAlphaGamma (w : ℤ) :
    alphaP p N = tv 0 ∘ₗ aV p 0 - (p : ℤ_[p]) • (tv 1 ∘ₗ cV p 0 ∘ₗ N.Ed 1) ∧
    gammaP p N w = tv 0 ∘ₗ cV p 1 + tv 1 ∘ₗ aV p (p - 1) - ((p : ℤ_[p]) * w) • (tv 1 ∘ₗ cV p 0) :=
  ⟨rfl, rfl⟩

/-- (P2) `ι_p(b_j(b̂_0 ⊗ n)) = F^j α(n)`, `ι_p(b_j(b̂_1 ⊗ n)) = −F^j γ(n)`. -/
theorem hP2 (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ p - 1) (ht : t + 1 = p) :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), j < p →
      iotaP p N t h1 h2 (bv p j (tv 0 n)) =
        ((Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Fd 1 ^ j) (alphaP p N n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), j < p → InWt N.wt w n →
      iotaP p N t h1 h2 (bv p j (tv 1 n)) =
        -((Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Fd 1 ^ j) (gammaP p N w n)) := by
  first | exact P2 t h1 h2 ht | exact P2 t h1 h2 | exact P2 (N := N) t h1 h2 ht | exact P2 (N := N) t h1 h2

/-- (P3) `ι_p : Ψ_p(N) → V ⊗ Ψ_{p−1}(N)` is a morphism, injective, with a left inverse. -/
theorem hP3 (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ p - 1) (ht : t + 1 = p) :
    (iotaPHom p N t h1 h2 ht).toLin = iotaP p N t h1 h2 ∧
    Function.Injective (iotaPHom p N t h1 h2 ht).toLin ∧
    rhoP p N t h1 h2 ∘ₗ (iotaPHom p N t h1 h2 ht).toLin = LinearMap.id := by
  obtain ⟨a, b, c, -⟩ := (by first | exact P3 t h1 h2 ht | exact P3 (N := N) t h1 h2 ht :
    (iotaPHom p N t h1 h2 ht).toLin = iotaP p N t h1 h2 ∧
    Function.Injective (iotaPHom p N t h1 h2 ht).toLin ∧
    rhoP p N t h1 h2 ∘ₗ (iotaPHom p N t h1 h2 ht).toLin = LinearMap.id ∧
    (∀ z k, (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).wt z ≠ (Psip p N).wt k →
      rhoP p N t h1 h2 (Pi.single z 1) k = 0) ∧
    (∀ k k', ∃ e, iota (psiD p N t h1 h2) (Pi.single k 1) (sel p N k') -
      (if k' = k then dval p N t k else 0) = (p : ℤ_[p]) * e) ∧
    (∀ k, IsUnit (dval p N t k)) ∧
    IsUnit (blkMat (psiD p N t h1 h2)).det)
  exact ⟨a, b, c⟩

/-- (S1) the symplectic form `ω`. -/
theorem hS1 :
    (omegaHom ℤ_[p]).toLin (Pi.single ((0 : Fin 2), (1 : Fin 2)) 1) = (fun _ => (1 : ℤ_[p])) ∧
    (omegaHom ℤ_[p]).toLin (Pi.single ((1 : Fin 2), (0 : Fin 2)) 1) = (fun _ => (-1 : ℤ_[p])) ∧
    (omegaHom ℤ_[p]).toLin (Pi.single ((0 : Fin 2), (0 : Fin 2)) 1) = 0 ∧
    (omegaHom ℤ_[p]).toLin (Pi.single ((1 : Fin 2), (1 : Fin 2)) 1) = 0 :=
  S1 ℤ_[p]

/-- (S2) `π_r : V ⊗ Ψ_r → Ψ_{r−1}` (`r = s+1`), from `ι_r x = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1`. -/
theorem hS2 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) (h2 : s ≤ p - 1) (h1' : 1 ≤ s + 1)
    (h2' : s + 1 ≤ p - 1)
    (x : (psi p N (s + 1) h1' h2').ι → ℤ_[p])
    (y0 y1 : (psi p N s hs1 h2).ι → ℤ_[p])
    (h : (iotaHom p N s hs1 hsp).toLin x = tv 0 y0 + tv 1 y1) :
    (piHom p N s hs1 hsp).toLin (tv 0 x) = y1 ∧ (piHom p N s hs1 hsp).toLin (tv 1 x) = -y0 :=
  S2 p N s hs1 hsp x y0 y1 h

/-- (S3) `π_1 : V ⊗ Ψ_1 → Φ_p ⊕ Φ_p`, from `κ x = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1`. -/
theorem hS3 (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) (x : (psi p N 1 h1 h2).ι → ℤ_[p])
    (y0 y1 : (twist p N).ι → ℤ_[p]) (h : kappa p N x = tv 0 y0 + tv 1 y1) :
    (pi1Hom p N h1 h2).toLin (tv 0 x) =
      Sum.elim y1 ((2 : ℤ_[p]) • (twist p N).Ed 1 y0 - H (twist p N) y1) ∧
    (pi1Hom p N h1 h2).toLin (tv 1 x) =
      Sum.elim (-y0) (-H (twist p N) y0 - (2 : ℤ_[p]) • (twist p N).Fd 1 y1) :=
  S3 p N h1 h2 x y0 y1 h

/-- (S4) `π_r` and `π_1` are surjective (`p` odd for `π_1`). -/
theorem hS4 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) (hp2 : p ≠ 2) :
    Function.Surjective (piHom p N s hs1 hsp).toLin ∧
    Function.Surjective (pi1Hom p N h1 h2).toLin :=
  ⟨by first | exact S4_pi s hs1 hsp | exact S4_pi (N := N) s hs1 hsp,
   by first | exact S4_pi1 h1 h2 hp2 | exact S4_pi1 (N := N) h1 h2 hp2⟩

/-- (S5), `r = 1`: `0 → Ψ_2 → V ⊗ Ψ_1 → Φ_p ⊕ Φ_p → 0`. -/
theorem hS5one (hp3 : 3 ≤ p) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    WeylFilt.ShortExact (iotaHom p N 1 le_rfl hp3) (pi1Hom p N h1 h2) := by
  first | exact S5_one hp3 h1 h2 | exact S5_one (N := N) hp3 h1 h2

/-- (S5), `2 ≤ r = s+1 ≤ p − 2`: `0 → Ψ_{r+1} → V ⊗ Ψ_r → Ψ_{r−1} → 0`. -/
theorem hS5mid (s : ℕ) (hs1 : 1 ≤ s) (hsp3 : s + 3 ≤ p) :
    WeylFilt.ShortExact (iotaHom p N (s + 1) (by omega) hsp3) (piHom p N s hs1 (by omega)) := by
  first | exact S5_mid s hs1 hsp3 | exact S5_mid (N := N) s hs1 hsp3

/-- (S5), `r = s+1 = p − 1`: `0 → Φ_p(V ⊗ N) → V ⊗ Ψ_{p−1} → Ψ_{p−2} → 0`. -/
theorem hS5last (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 = p) :
    WeylFilt.ShortExact (iotaPHom p N (s + 1) (by omega) (by omega) (by omega))
      (piHom p N s hs1 (by omega)) := by
  first | exact S5_last s hs1 hsp | exact S5_last (N := N) s hs1 hsp

end CheckCSI4

#print axioms CheckCSI4.hCas
#print axioms CheckCSI4.hpSub
#print axioms CheckCSI4.hC1
#print axioms CheckCSI4.hC2
#print axioms CheckCSI4.hC3
#print axioms CheckCSI4.hC4
#print axioms CheckCSI4.hPsip
#print axioms CheckCSI4.hP1
#print axioms CheckCSI4.hAlphaGamma
#print axioms CheckCSI4.hP2
#print axioms CheckCSI4.hP3
#print axioms CheckCSI4.hS1
#print axioms CheckCSI4.hS2
#print axioms CheckCSI4.hS3
#print axioms CheckCSI4.hS4
#print axioms CheckCSI4.hS5one
#print axioms CheckCSI4.hS5mid
#print axioms CheckCSI4.hS5last
