import RequestProject.OddSplit.All

/-!
# CheckCSI3 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI3 (`CSI3_the_split.md`): the slots `A_j n`, `C_j n`, `b̂_e ⊗ x` written out;
the weights of Part D; the ten formulas of Definition 1.3 with `u = −1` and `X = F E`; the `sl_2`
relation (D1); the lattice `psi p N r` with its single operators (I5) and uniqueness; the maps
`α`, `γ`, `ι` written out (I1), intertwining (I2), the retraction (I3), `ι` as a morphism (I6);
`κ` written out and `Ψ_1 ≅ V ⊗ Φ_p(N)` (B); the functor (F1), (F2); and (Q0a)–(Q0e).
Then `#print axioms`.
-/

namespace CheckCSI3

open ColouredSand.OddTwist DPLattice

variable {p : ℕ} [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- The slots written out: `A_k n`, `C_k n`, `b̂_e ⊗ x`. -/
theorem hSlots {ι : Type*} (k : ℕ) (n : ι → ℤ_[p]) (x : Bool × Fin p × ι)
    (e : Fin 2) (y : ι → ℤ_[p]) (z : Fin 2 × ι) :
    aV p k n x = (if x.1 = false ∧ (x.2.1 : ℕ) = k then n x.2.2 else 0) ∧
    cV p k n x = (if x.1 = true ∧ (x.2.1 : ℕ) = k then n x.2.2 else 0) ∧
    tv e y z = (if z.1 = e then y z.2 else 0) :=
  ⟨aV_apply p k n x, cV_apply p k n x, tv_apply e y z⟩

/-- The weights of Part D, by hand. -/
theorem hWt (r : ℕ) (b : Bool) (j : Fin p) (i : N.ι) :
    psiWt p N r (b, j, i) =
      (p : ℤ) * N.wt i + p - 1 + (if b then -(r : ℤ) else r) - 2 * ((j : ℕ) : ℤ) := rfl

/-- (I5) the lattice, by hand: basis, weights, single operators. -/
theorem hI5 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    (psi p N r h1 h2).ι = (Bool × Fin p × N.ι) ∧
    (∀ x : Bool × Fin p × N.ι, (psi p N r h1 h2).wt x = psiWt p N r x) ∧
    (psi p N r h1 h2).Fd 1 = psiF p N r ∧ (psi p N r h1 h2).Ed 1 = psiE p N r :=
  I5 p N r h1 h2

/-- (I5) uniqueness, by hand. -/
theorem hUnique (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1)
    (Fd Ed : ℕ → Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]))
    (h : IsDP (psiWt p N r) Fd Ed) (hF : Fd 1 = psiF p N r) (hE : Ed 1 = psiE p N r) :
    Fd = (psi p N r h1 h2).Fd ∧ Ed = (psi p N r h1 h2).Ed :=
  I5_unique p N r h1 h2 Fd Ed h hF hE

/-- Part D, the formulas for `F`, by hand. -/
theorem hF (r j : ℕ) (n : N.ι → ℤ_[p]) :
    (j + 1 < p → psiF p N r (aV p j n) = aV p (j + 1) n ∧ psiF p N r (cV p j n) = cV p (j + 1) n) ∧
    psiF p N r (aV p (p - 1) n) =
      (-(p : ℤ_[p])) • aV p 0 (N.Fd 1 n) + (p : ℤ_[p]) • cV p (p - r) n ∧
    psiF p N r (cV p (p - 1) n) = (-(p : ℤ_[p])) • cV p 0 (N.Fd 1 n) :=
  ⟨fun hj => ⟨psiF_A_lt r hj n, psiF_C_lt r hj n⟩, psiF_A_last r n, psiF_C_last r n⟩

/-- Part D, the formulas for `E` on `A_j n`, by hand (`n` of weight `w`, `X = F E`). -/
theorem hEA (r j : ℕ) (hj : j < p) (w : ℤ) (n : N.ι → ℤ_[p]) (hn : InWt N.wt w n) :
    (j = 0 → psiE p N r (aV p j n) = (-(p : ℤ_[p])) • aV p (p - 1) (N.Ed 1 n) +
        (((p : ℤ_[p]) - r) * p) • cV p (p - 1 - r) (N.Ed 1 n)) ∧
    (1 ≤ j → j ≤ r → psiE p N r (aV p j n) =
      aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) -
      ((r : ℤ_[p]) * p) • cV p (p + j - 1 - r) (N.Ed 1 n)) ∧
    (r + 1 ≤ j → psiE p N r (aV p j n) =
      aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) +
      ((r : ℤ_[p]) * p ^ 2) • cV p (j - 1 - r) (N.Fd 1 (N.Ed 1 n))) :=
  ⟨fun h0 => by subst h0; exact psiE_A_zero r hn, fun h1 h2 => psiE_A_low r h1 h2 hj hn,
    fun h1 => psiE_A_high r h1 hj hn⟩

/-- Part D, the formulas for `E` on `C_j n`, by hand. -/
theorem hEC (r j : ℕ) (hj : j < p) (w : ℤ) (n : N.ι → ℤ_[p]) (hn : InWt N.wt w n) :
    (j = 0 → psiE p N r (cV p j n) =
      (r : ℤ_[p]) • aV p (r - 1) n - (p : ℤ_[p]) • cV p (p - 1) (N.Ed 1 n)) ∧
    (1 ≤ j → j ≤ p - r → psiE p N r (cV p j n) =
      cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j)) • n) + (r : ℤ_[p]) • aV p (j + r - 1) n) ∧
    (p - r + 1 ≤ j → psiE p N r (cV p j n) =
      cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j) + r * p) • n) -
      ((r : ℤ_[p]) * p) • aV p (j + r - 1 - p) (N.Fd 1 n)) :=
  ⟨fun h0 => by subst h0; exact psiE_C_zero r hn, fun h1 h2 => psiE_C_low r h1 h2 hj hn,
    fun h1 => psiE_C_high r h1 hj hn⟩

/-- (D1) the `sl_2` relation, by hand. -/
theorem hD1 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    psiE p N r ∘ₗ psiF p N r - psiF p N r ∘ₗ psiE p N r = Hop (psiWt p N r) :=
  psi_D1 p N r h1 h2

/-- (I1) `ι(A_j n) = F^j α(n)` and `ι(C_j n) = F^j γ(n)` with `α`, `γ` written out, `r = s + 1`,
inside `V ⊗ psi p N s`. -/
theorem hIota (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) (j : ℕ) (hj : j < p) (w : ℤ)
    (n : N.ι → ℤ_[p]) (hn : InWt N.wt w n) :
    iota (psiD p N s hs1 (by omega)) (aV p j n) =
      ((Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))).Fd 1 ^ j)
        (tv 0 (aV p 0 n) - (p : ℤ_[p]) • tv 1 (cV p (p - (s + 1)) (N.Ed 1 n))) ∧
    iota (psiD p N s hs1 (by omega)) (cV p j n) =
      ((Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))).Fd 1 ^ j)
        (tv 0 (cV p 1 n) + tv 1 (aV p s n) -
          ((p : ℤ_[p]) * w + p - (s + 1)) • tv 1 (cV p 0 n)) :=
  ⟨iota_aV _ hj n, iota_cV _ hj hn⟩

/-- (I2), (I3) intertwining and the retraction, by hand. -/
theorem hI23 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    iota (psiD p N s hs1 (by omega)) ∘ₗ psiF p N (s + 1) =
      (Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))).Fd 1 ∘ₗ
        iota (psiD p N s hs1 (by omega)) ∧
    iota (psiD p N s hs1 (by omega)) ∘ₗ psiE p N (s + 1) =
      (Tensor2.tensor (V ℤ_[p]) (psi p N s hs1 (by omega))).Ed 1 ∘ₗ
        iota (psiD p N s hs1 (by omega)) ∧
    rho (psiD p N s hs1 (by omega)) ∘ₗ iota (psiD p N s hs1 (by omega)) = LinearMap.id :=
  ⟨iota_F _ hs1 hsp, iota_E _ hs1 hsp, rho_iota _ hs1 hsp⟩

/-- (I4), (I6): `psi p N (s+1)` is the sub-lattice cut out by `ι`, and `ι` is an injective
morphism `psi p N (s+1) → V ⊗ psi p N s` with left inverse `ρ`. -/
theorem hI46 (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    psi p N (s + 1) (by omega) (by omega) = psiSubStep (psiD p N s hs1 (by omega)) hs1 hsp ∧
    (iotaHom p N s hs1 hsp).toLin = iota (psiD p N s hs1 (by omega)) ∧
    Function.Injective (iotaHom p N s hs1 hsp).toLin ∧
    rho (psiD p N s hs1 (by omega)) ∘ₗ (iotaHom p N s hs1 hsp).toLin = LinearMap.id :=
  ⟨psi_succ_eq p N s hs1 hsp, I6 p N s hs1 hsp⟩

/-- (B1)–(B4) by hand: `κ` written out, its inverse, intertwining, and `Ψ_1 ≅ V ⊗ Φ_p(N)`. -/
theorem hB (j : ℕ) (hj : j < p) (n : N.ι → ℤ_[p]) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    kappa p N (aV p j n) = tv 0 (bv p j n) + (j : ℤ_[p]) • tv 1 (bv p (j - 1) n) ∧
    kappa p N (cV p j n) = tv 1 (bv p j n) ∧
    kappaInv p N ∘ₗ kappa p N = LinearMap.id ∧ kappa p N ∘ₗ kappaInv p N = LinearMap.id ∧
    kappa p N ∘ₗ psiF p N 1 = (Tensor2.tensor (V ℤ_[p]) (twist p N)).Fd 1 ∘ₗ kappa p N ∧
    kappa p N ∘ₗ psiE p N 1 = (Tensor2.tensor (V ℤ_[p]) (twist p N)).Ed 1 ∘ₗ kappa p N ∧
    psi p N 1 h1 h2 = psiSub1 p N ∧
    Nonempty (Doubling.Iso (psi p N 1 h1 h2) (Tensor2.tensor (V ℤ_[p]) (twist p N))) :=
  ⟨kappa_aV hj n, kappa_cV hj n, kappaInv_kappa, kappa_kappaInv, kappa_F,
    kappa_E, psi_one_eq p N h1 h2, (B4 p N h1 h2).2.2⟩

/-- (F1), (F2) the functor, by hand. -/
theorem hF12 {N N' : DPLattice ℤ_[p]} (f : Hom N N') (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), (psiHom p f r h1 h2).toLin (aV p j n) = aV p j (f.toLin n)) ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), (psiHom p f r h1 h2).toLin (cV p j n) = cV p j (f.toLin n)) ∧
    (∀ M : DPLattice ℤ_[p], psiHom p (WeylFilt.Hom.id M) r h1 h2 = WeylFilt.Hom.id (psi p M r h1 h2)) ∧
    (∀ {M M' M'' : DPLattice ℤ_[p]} (g : Hom M' M'') (k : Hom M M'),
      psiHom p (WeylFilt.Hom.comp g k) r h1 h2 =
        WeylFilt.Hom.comp (psiHom p g r h1 h2) (psiHom p k r h1 h2)) :=
  ⟨(F1 p f r h1 h2).1, (F1 p f r h1 h2).2, (F2 p r h1 h2).1, (F2 p r h1 h2).2⟩

/-- (Q0a) by hand. -/
theorem hQ0a {A : Type*} [CommRing A] (M : DPLattice A) (r : ℕ) :
    ((r.factorial : ℕ) : A) • M.Fd r = M.Fd 1 ^ r ∧ ((r.factorial : ℕ) : A) • M.Ed r = M.Ed 1 ^ r :=
  Q0a M r

/-- (Q0b) by hand, over `ℤ_[p]`. -/
theorem hQ0b {ι : Type} [Fintype ι] [DecidableEq ι] (wt : ι → ℤ)
    {Fd Ed Fd' Ed' : ℕ → Module.End ℤ_[p] (ι → ℤ_[p])}
    (h : IsDP wt Fd Ed) (h' : IsDP wt Fd' Ed') (hF : Fd 1 = Fd' 1) (hE : Ed 1 = Ed' 1) :
    Fd = Fd' ∧ Ed = Ed' :=
  Q0b wt h h' hF hE

/-- (Q0e) by hand, over `ℤ_[p]`. -/
theorem hQ0e (X : DPLattice ℤ_[p]) {κ : Type*} [AddCommGroup κ] [Module ℤ_[p] κ]
    (j : κ →ₗ[ℤ_[p]] (X.ι → ℤ_[p])) (ρ : (X.ι → ℤ_[p]) →ₗ[ℤ_[p]] κ)
    (hρ : ρ ∘ₗ j = LinearMap.id) (T S : Module.End ℤ_[p] κ) (hT : j ∘ₗ T = X.Fd 1 ∘ₗ j)
    (hS : j ∘ₗ S = X.Ed 1 ∘ₗ j) :
    (∀ r x, X.Fd r (j x) ∈ LinearMap.range j) ∧ (∀ r x, X.Ed r (j x) ∈ LinearMap.range j) :=
  Q0e X j ρ hρ T S hT hS

end CheckCSI3

#print axioms CheckCSI3.hSlots
#print axioms CheckCSI3.hWt
#print axioms CheckCSI3.hI5
#print axioms CheckCSI3.hUnique
#print axioms CheckCSI3.hF
#print axioms CheckCSI3.hEA
#print axioms CheckCSI3.hEC
#print axioms CheckCSI3.hD1
#print axioms CheckCSI3.hIota
#print axioms CheckCSI3.hI23
#print axioms CheckCSI3.hI46
#print axioms CheckCSI3.hB
#print axioms CheckCSI3.hF12
#print axioms CheckCSI3.hQ0a
#print axioms CheckCSI3.hQ0b
#print axioms CheckCSI3.hQ0e
