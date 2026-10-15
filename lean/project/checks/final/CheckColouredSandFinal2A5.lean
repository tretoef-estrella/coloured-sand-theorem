-- CheckColouredSandFinal2A5.lean (part A5 of half A: every import, pieces 16-18) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
-- Assembled by assemble_final.py (Grepy Ship, 14 Oct 2026; v2 15 Oct 2026) from the 36 certified per-piece check files, each body unchanged
-- inside its own namespace FinalCheck.<piece>. Every `#print axioms` line must read [propext, Classical.choice, Quot.sound].
import RequestProject.BlockOp.All
import RequestProject.Blocks.All
import RequestProject.Corollaries.All
import RequestProject.Exponent.All
import RequestProject.Glue.All
import RequestProject.NumberOfFactors.All
import RequestProject.OddCeiling.All
import RequestProject.OddCellFloor.All
import RequestProject.OddDance.All
import RequestProject.OddDeficit.All
import RequestProject.OddHouses.All
import RequestProject.OddLevels.All
import RequestProject.OddPayment.All
import RequestProject.OddPotential.All
import RequestProject.OddRulers.All
import RequestProject.OddSES.All
import RequestProject.OddSmith.All
import RequestProject.OddSplit.All
import RequestProject.OddSplitMove.All
import RequestProject.OddSplitting.All
import RequestProject.OddTheoremI.All
import RequestProject.OddTotal.All
import RequestProject.OddTwist.All
import RequestProject.OddTwistModP.All
import RequestProject.OddWindows.All
import RequestProject.Splitting.All
import RequestProject.Strings.All
import RequestProject.StringsAll.All
import RequestProject.TheoremB.All
import RequestProject.ThmG.All
import RequestProject.ThmGTwo.All
import RequestProject.ThmH.All
import RequestProject.TiltDec.All
import RequestProject.TiltP.All
import RequestProject.TiltRules.All
import RequestProject.TwoTheoremI.All

-- ======== piece CSI2 (from lean/proyecto_cubo/checks/CheckCSI2.lean) ========
namespace FinalCheck.CSI2

/-!
# CheckCSI2 (Grepy Sand, 14 Oct 2026)

Hand restatement of CSI2 (`CSI2_reduction_mod_p.md`): Lucas at `p` (T0), the Frobenius twist
`frobP` written out (weights `p·wt`, `F^{(r)} = F^{(r/p)}` if `p ∣ r`, else `0`), the Steinberg
lattice `St = baseChange g0 Δ(p−1)`, Wilson (C0), the formulas mod `p` (C1), the diagonal map
`D(b_j e_i) = j!·(e_j ⊗ e_i)` with the isomorphism (C2), and the case of the paper (C3) with
`ZMod p`, `PadicInt.toZMod` and `delta ℤ_[p] (p − 1)` written out. Then `#print axioms`.
-/

namespace CheckCSI2

open ColouredSand.OddTwist DPLattice

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime]

/-- (T0) by hand. -/
theorem hT0 (hp : (p : B) = 0) (x : ℤ) (j : ℕ) :
    ((Ring.choose ((p : ℤ) * x) (p * j) : ℤ) : B) = ((Ring.choose x j : ℤ) : B) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ p - 1 → ((Ring.choose ((p : ℤ) * x) (p * j + t) : ℤ) : B) = 0 :=
  T0 hp x j

/-- The Frobenius twist written out. -/
theorem hFrob (hp : (p : B) = 0) (M : DPLattice B) :
    (frobP hp M).ι = M.ι ∧ (∀ i, (frobP hp M).wt i = (p : ℤ) * M.wt i) ∧
    (∀ r, (frobP hp M).Fd r = if p ∣ r then M.Fd (r / p) else 0) ∧
    (∀ r, (frobP hp M).Ed r = if p ∣ r then M.Ed (r / p) else 0) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `St` is the base change of `Δ(p − 1)`. -/
theorem hSt (g0 : ℤ_[p] →+* B) : St g0 = Twist.baseChange g0 (delta ℤ_[p] (p - 1)) := rfl

/-- (C0) Wilson, by hand. -/
theorem hC0 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (c t : ℕ) (ht : t ≤ p - 1) :
    g0 (qc p c (p * c + t)) * ((Nat.factorial t : ℕ) : B) = (-1) ^ c ∧
    ∀ c' : ℕ, c + 1 ≤ c' → g0 (qc p c' (p * c + t)) = 0 :=
  C0 hp g0 c t ht

/-- (C1) by hand. -/
theorem hC1 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (N : DPLattice ℤ_[p]) (c t : ℕ) (ht : t ≤ p - 1)
    (j : ℕ) (hj : j < p) (n : N.ι → B) :
    (j + t ≤ p - 1 → ((Nat.factorial t : ℕ) : B) • (Twist.baseChange g0 (twist p N)).Fd (p * c + t) (bv p j n) =
      bv p (j + t) ((Twist.baseChange g0 N).Fd c n)) ∧
    (p - 1 < j + t → (Twist.baseChange g0 (twist p N)).Fd (p * c + t) (bv p j n) = 0) ∧
    (t ≤ j → ((Nat.factorial (j - t) : ℕ) : B) • (Twist.baseChange g0 (twist p N)).Ed (p * c + t) (bv p j n) =
      (((Nat.factorial j : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        bv p (j - t) ((Twist.baseChange g0 N).Ed c n)) ∧
    (j < t → (Twist.baseChange g0 (twist p N)).Ed (p * c + t) (bv p j n) = 0) :=
  oddModP_C1 hp g0 N c t ht j hj n

/-- (C2) by hand: `D(b_j e_i) = j!·(e_j ⊗ e_i)` and the isomorphism with `St ⊗ N̄^{[1]}`. -/
theorem hC2 (hp : (p : B) = 0) (g0 : ℤ_[p] →+* B) (N : DPLattice ℤ_[p]) :
    (∀ (j : ℕ) (hj : j < p - 1 + 1) (i : N.ι),
      Dmap B p N.ι (bv p j (Pi.single i 1)) =
        ((Nat.factorial j : ℕ) : B) • Tensor2.tprod (Pi.single (⟨j, hj⟩ : Fin (p - 1 + 1)) 1)
          (Pi.single i 1)) ∧
    ∃ u : Doubling.Iso (Twist.baseChange g0 (twist p N))
        (Tensor2.tensor (Twist.baseChange g0 (delta ℤ_[p] (p - 1)))
          (frobP hp (Twist.baseChange g0 N))),
      u.hom.toLin = Dmap B p N.ι ∧ u.inv.toLin = Dinv B p N.ι :=
  oddModP_C2 hp g0 N

/-- (C3) the case of the paper, by hand. -/
theorem hC3 (N : DPLattice ℤ_[p]) :
    Nonempty (Doubling.Iso (Twist.baseChange PadicInt.toZMod (twist p N))
      (Tensor2.tensor (Twist.baseChange PadicInt.toZMod (delta ℤ_[p] (p - 1)))
        (frobP (ZMod.natCast_self p) (Twist.baseChange PadicInt.toZMod N)))) :=
  oddModP_C3 N

end CheckCSI2

#print axioms CheckCSI2.hT0
#print axioms CheckCSI2.hFrob
#print axioms CheckCSI2.hSt
#print axioms CheckCSI2.hC0
#print axioms CheckCSI2.hC1
#print axioms CheckCSI2.hC2
#print axioms CheckCSI2.hC3
#print axioms ColouredSand.OddTwist.T1
#print axioms ColouredSand.OddTwist.T2
#print axioms ColouredSand.OddTwist.oddModP_S1
#print axioms ColouredSand.OddTwist.C3_hyp
#print axioms ColouredSand.OddTwist.prop12Iso

end FinalCheck.CSI2

-- ======== piece CSI3 (from lean/proyecto_cubo/checks/CheckCSI3.lean) ========
namespace FinalCheck.CSI3

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

end FinalCheck.CSI3

-- ======== piece CSI4 (from lean/proyecto_cubo/checks/CheckCSI4.lean) ========
namespace FinalCheck.CSI4

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

end FinalCheck.CSI4
