module

public import RequestProject.OddSplit.PartB

/-!
# `CSI3_the_split.md`: Part I (I4)–(I6) and Part B (B4) — the lattice `Ψ_r(N)`

Encodings:

* `psiSub1 p N = Filt.sub W (psiWt p N 1) κ κ⁻¹ …` is the sub-lattice of (B4)
  (`W = V ⊗ Φ_p(N)`), and `psiSubStep L … = Filt.sub (V ⊗ M) (psiWt p N r) ι ρ …` the one of
  (I4) (`M = L.lat`, `r = s + 1`), with stability of `range κ` (trivial: `κ` is onto) resp.
  `range ι` (from (Q0e)).
* `psiData p N k : PsiData p N (k + 1)` (for `k + 2 ≤ p`) is defined by recursion on `k`:
  `psiData 0 = psiSub1`, `psiData (k + 1) = psiSubStep (psiData k)`; `psiD p N r` is the same
  for `1 ≤ r ≤ p − 1` (transported along `r − 1 + 1 = r`), and
  `psi p r N h1 h2 = (psiD p N r h1 h2).lat` is `Ψ_r(N)`: basis `Bool × Fin p × N.ι` (by
  definition), weights `psiWt p N r` (by definition).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-! ### The base case `r = 1` -/

lemma kappa_rangeF (r : ℕ) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    (Wt p N).Fd r (kappa p N x) ∈ LinearMap.range (kappa p N) :=
  ⟨kappaInv p N ((Wt p N).Fd r (kappa p N x)), LinearMap.congr_fun kappa_kappaInv _⟩

lemma kappa_rangeE (r : ℕ) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    (Wt p N).Ed r (kappa p N x) ∈ LinearMap.range (kappa p N) :=
  ⟨kappaInv p N ((Wt p N).Ed r (kappa p N x)), LinearMap.congr_fun kappa_kappaInv _⟩

/-- (B4) the sub-lattice `Filt.sub W (psiWt p N 1) κ κ⁻¹ …` of `W = V ⊗ Φ_p(N)`. -/
def psiSub1 : DPLattice ℤ_[p] :=
  Filt.sub (Wt p N) (psiWt p N 1) (kappa p N) (kappaInv p N) kappaInv_kappa kappa_wtPres
    kappaInv_wtPres (kappa_rangeF p N) (kappa_rangeE p N)

lemma psiSub1_F1 : (psiSub1 p N).Fd 1 = psiF p N 1 := by
  change kappaInv p N ∘ₗ WF p N ∘ₗ kappa p N = psiF p N 1
  rw [← kappa_F, ← LinearMap.comp_assoc, kappaInv_kappa, LinearMap.id_comp]

lemma psiSub1_E1 : (psiSub1 p N).Ed 1 = psiE p N 1 := by
  change kappaInv p N ∘ₗ WE p N ∘ₗ kappa p N = psiE p N 1
  rw [← kappa_E, ← LinearMap.comp_assoc, kappaInv_kappa, LinearMap.id_comp]

/-- (B4) `Ψ_1(N)` as a `PsiData`. -/
def psiBase : PsiData p N 1 :=
  ⟨(psiSub1 p N).Fd, (psiSub1 p N).Ed, (psiSub1 p N).isDP, psiSub1_F1 p N, psiSub1_E1 p N⟩

/-! ### The step `r − 1 → r` -/

variable {p N}

section step

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I4) stability of `range ι` under every `F^{(k)}`, `E^{(k)}` of `V ⊗ M`, from (Q0e). -/
lemma iota_range :
    (∀ r x, (Zs L).Fd r (iota L x) ∈ LinearMap.range (iota L)) ∧
    (∀ r x, (Zs L).Ed r (iota L x) ∈ LinearMap.range (iota L)) :=
  Q0e (Zs L) (iota L) (rho L) (rho_iota L hs1 hsp) (psiF p N (s + 1)) (psiE p N (s + 1))
    (iota_F L hs1 hsp) (iota_E L hs1 hsp)

/-- (I4) the sub-lattice `Filt.sub (V ⊗ M) (psiWt p N r) ι ρ …`, `r = s + 1`. -/
def psiSubStep : DPLattice ℤ_[p] :=
  Filt.sub (Zs L) (psiWt p N (s + 1)) (iota L) (rho L) (rho_iota L hs1 hsp)
    (iota_wtPres L hs1 hsp) (rho_wtPres L hs1 hsp) (iota_range L hs1 hsp).1
    (iota_range L hs1 hsp).2

lemma psiSubStep_F1 : (psiSubStep L hs1 hsp).Fd 1 = psiF p N (s + 1) := by
  change rho L ∘ₗ ZF L ∘ₗ iota L = psiF p N (s + 1)
  rw [← iota_F L hs1 hsp, ← LinearMap.comp_assoc, rho_iota L hs1 hsp, LinearMap.id_comp]

lemma psiSubStep_E1 : (psiSubStep L hs1 hsp).Ed 1 = psiE p N (s + 1) := by
  change rho L ∘ₗ ZE L ∘ₗ iota L = psiE p N (s + 1)
  rw [← iota_E L hs1 hsp, ← LinearMap.comp_assoc, rho_iota L hs1 hsp, LinearMap.id_comp]

/-- (I4) the step as a `PsiData`. -/
def psiStep : PsiData p N (s + 1) :=
  ⟨(psiSubStep L hs1 hsp).Fd, (psiSubStep L hs1 hsp).Ed, (psiSubStep L hs1 hsp).isDP,
    psiSubStep_F1 L hs1 hsp, psiSubStep_E1 L hs1 hsp⟩

end step

variable (p N)

/-- (I4) the recursion: `psiData p N k` is `Ψ_{k+1}(N)` (for `k + 2 ≤ p`). -/
def psiData : (k : ℕ) → k + 2 ≤ p → PsiData p N (k + 1)
  | 0, _ => psiBase p N
  | k + 1, h => psiStep (psiData k (by omega)) (by omega) (by omega)

/-- (I4) `Ψ_r(N)` as a `PsiData`, for `1 ≤ r ≤ p − 1`. -/
def psiD (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : PsiData p N r :=
  (Nat.sub_add_cancel h1) ▸ psiData p N (r - 1) (by have := two_le_p' (p := p); omega)

/-- (I4) **The lattice `Ψ_r(N)` of Definition 1.3** (`1 ≤ r ≤ p − 1`): `psi p 1 N` is the
sub-lattice of `V ⊗ Φ_p(N)` cut out by `κ` (Part B), and for `2 ≤ r ≤ p − 1`, `psi p r N` is the
sub-lattice `Filt.sub (V ⊗ psi p (r−1) N) … ι ρ …` (see `psi_succ_eq`). -/
def psi (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : DPLattice ℤ_[p] := (psiD p N r h1 h2).lat

/-! ### (I5) the single operators of `psi p r N`, and uniqueness -/

/-- (I5) For every `1 ≤ r ≤ p − 1`: `(psi p r N).ι = Bool × Fin p × N.ι`, the weights are those
of Part D, `(psi p r N).Fd 1 = psiF p r N` and `(psi p r N).Ed 1 = psiE p r N`. -/
theorem I5 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    (psi p N r h1 h2).ι = (Bool × Fin p × N.ι) ∧
    (∀ x : Bool × Fin p × N.ι, (psi p N r h1 h2).wt x = psiWt p N r x) ∧
    (psi p N r h1 h2).Fd 1 = psiF p N r ∧ (psi p N r h1 h2).Ed 1 = psiE p N r :=
  ⟨rfl, fun _ => rfl, (psiD p N r h1 h2).F1, (psiD p N r h1 h2).E1⟩

lemma psi_Fd1 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : (psi p N r h1 h2).Fd 1 = psiF p N r :=
  (psiD p N r h1 h2).F1

lemma psi_Ed1 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) : (psi p N r h1 h2).Ed 1 = psiE p N r :=
  (psiD p N r h1 h2).E1

/-- (I5) Uniqueness: any DP-lattice structure over `ℤ_[p]` on the basis `Bool × Fin p × N.ι`
with the weights of Part D and single operators `psiF p r N`, `psiE p r N` has the divided powers
of `psi p r N`. So `psi p r N` is the lattice `Ψ_r(N)` of Definition 1.3, and the construction
does not matter. -/
theorem I5_unique (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1)
    (Fd Ed : ℕ → Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]))
    (h : IsDP (psiWt p N r) Fd Ed) (hF : Fd 1 = psiF p N r) (hE : Ed 1 = psiE p N r) :
    Fd = (psi p N r h1 h2).Fd ∧ Ed = (psi p N r h1 h2).Ed :=
  Q0b (psiWt p N r) h (psiD p N r h1 h2).isDP (hF.trans (psiD p N r h1 h2).F1.symm)
    (hE.trans (psiD p N r h1 h2).E1.symm)

/-! ### (I4) `psi p r N` is the sub-lattice `Filt.sub (V ⊗ psi p (r−1) N) … ι ρ …` -/

/-- (I4) For `2 ≤ r ≤ p − 1` (written `r = s + 1`, `1 ≤ s`, `s + 2 ≤ p`): `psi p r N` is the
sub-lattice `Filt.sub (Tensor2.tensor (V ℤ_[p]) (psi p (r−1) N)) (psiWt p N r) ι ρ …` of C29. -/
theorem psi_succ_eq (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p) :
    psi p N (s + 1) (by omega) (by omega) =
      psiSubStep (psiD p N s hs1 (by omega)) hs1 hsp := by
  obtain ⟨e1, e2⟩ := Q0b (psiWt p N (s + 1)) (psiD p N (s + 1) (by omega) (by omega)).isDP
    (psiSubStep (psiD p N s hs1 (by omega)) hs1 hsp).isDP
    ((psiD p N (s + 1) (by omega) (by omega)).F1.trans (psiSubStep_F1 _ hs1 hsp).symm)
    ((psiD p N (s + 1) (by omega) (by omega)).E1.trans (psiSubStep_E1 _ hs1 hsp).symm)
  simp only [psi, PsiData.lat, psiSubStep, Filt.sub]
  congr

/-- (B4) `psi p 1 N` is the sub-lattice `Filt.sub W (psiWt p N 1) κ κ⁻¹ …` of
`W = V ⊗ Φ_p(N)`. -/
theorem psi_one_eq (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) : psi p N 1 h1 h2 = psiSub1 p N := by
  obtain ⟨e1, e2⟩ := Q0b (psiWt p N 1) (psiD p N 1 h1 h2).isDP (psiSub1 p N).isDP
    ((psiD p N 1 h1 h2).F1.trans (psiSub1_F1 p N).symm)
    ((psiD p N 1 h1 h2).E1.trans (psiSub1_E1 p N).symm)
  simp only [psi, PsiData.lat, psiSub1, Filt.sub]
  congr

end ColouredSand.OddTwist
