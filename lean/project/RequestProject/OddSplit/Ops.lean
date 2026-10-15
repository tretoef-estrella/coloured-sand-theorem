module

public import RequestProject.OddSplit.Basic

/-!
# `CSI3_the_split.md`: Part D — the single operators of Definition 1.3

Encodings (see also `Basic.lean`): `N : DPLattice ℤ_[p]`, `F = N.Fd 1`, `E = N.Ed 1`,
`X = F ∘ E`; the unit `u` of the report is `u = −1`.

* `psiWt p r N (b, j, i) = p·w_i + p − 1 ± r − 2j` (`+r` for `b = false`, i.e. `A_j e_i`, and
  `−r` for `b = true`, i.e. `C_j e_i`).
* `psiFL p N r b j` and `psiEL p N r b j w` are the formulas of Definition 1.3 for `F(A_j n)`,
  `F(C_j n)`, `E(A_j n)`, `E(C_j n)` as linear maps of `n` (for `E`, with `w` the weight of `n`).
  The scalars `(p − r)p`, `rp`, `rp²` and `g^A_j = p²X + j(pw + p + r − j)`,
  `g^C_j = p²X + j(pw + p − r − j)` are written in `ℤ_[p]`.
* `psiF p r N`, `psiE p r N` are the `ℤ_[p]`-linear extensions of these formulas on the basis
  vectors `A_j e_i`, `C_j e_i` (`Basis.constr`), exactly as CSI1 built `twFd`, `twEd`. The
  formulas on arbitrary vectors (`F`) and on vectors of weight `w` (`E`) are `psiF_A_lt`, …,
  `psiE_C_high`, collected in `D_formulas`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- Part D, weights: `wt(A_j e_i) = p·w_i + p − 1 + r − 2j`, `wt(C_j e_i) = p·w_i + p − 1 − r − 2j`. -/
def psiWt (r : ℕ) (x : Bool × Fin p × N.ι) : ℤ :=
  p * N.wt x.2.2 + p - 1 + (if x.1 then -(r : ℤ) else r) - 2 * ((x.2.1 : ℕ) : ℤ)

/-- Part D: the formulas for `F(A_j n)` (`b = false`) and `F(C_j n)` (`b = true`) as linear maps
of `n`. -/
def psiFL (r : ℕ) (b : Bool) (j : ℕ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) :=
  match b with
  | false => if j + 1 < p then aV p (j + 1)
      else (-(p : ℤ_[p])) • (aV p 0 ∘ₗ N.Fd 1) + (p : ℤ_[p]) • cV p (p - r)
  | true => if j + 1 < p then cV p (j + 1) else (-(p : ℤ_[p])) • (cV p 0 ∘ₗ N.Fd 1)

/-- Part D: `g^A_j = p²X + j(pw + p + r − j)` on `N`. -/
def gA (r j : ℕ) (w : ℤ) : Module.End ℤ_[p] (N.ι → ℤ_[p]) :=
  ((p : ℤ_[p]) ^ 2) • (N.Fd 1 ∘ₗ N.Ed 1) +
    ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • LinearMap.id

/-- Part D: `g^C_j = p²X + j(pw + p − r − j)` on `N`. -/
def gC (r j : ℕ) (w : ℤ) : Module.End ℤ_[p] (N.ι → ℤ_[p]) :=
  ((p : ℤ_[p]) ^ 2) • (N.Fd 1 ∘ₗ N.Ed 1) +
    ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j)) • LinearMap.id

/-- Part D: the formulas for `E(A_j n)` (`b = false`) and `E(C_j n)` (`b = true`), `n` of weight
`w`, as linear maps of `n`. -/
def psiEL (r : ℕ) (b : Bool) (j : ℕ) (w : ℤ) :
    (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) :=
  match b with
  | false =>
    if j = 0 then (-(p : ℤ_[p])) • (aV p (p - 1) ∘ₗ N.Ed 1) +
        (((p : ℤ_[p]) - r) * p) • (cV p (p - 1 - r) ∘ₗ N.Ed 1)
    else if j ≤ r then aV p (j - 1) ∘ₗ gA p N r j w -
        ((r : ℤ_[p]) * p) • (cV p (p + j - 1 - r) ∘ₗ N.Ed 1)
    else aV p (j - 1) ∘ₗ gA p N r j w +
        ((r : ℤ_[p]) * p ^ 2) • (cV p (j - 1 - r) ∘ₗ (N.Fd 1 ∘ₗ N.Ed 1))
  | true =>
    if j = 0 then (r : ℤ_[p]) • aV p (r - 1) - (p : ℤ_[p]) • (cV p (p - 1) ∘ₗ N.Ed 1)
    else if j ≤ p - r then cV p (j - 1) ∘ₗ gC p N r j w + (r : ℤ_[p]) • aV p (j + r - 1)
    else cV p (j - 1) ∘ₗ (gC p N r j w + ((r : ℤ_[p]) * p) • LinearMap.id) -
        ((r : ℤ_[p]) * p) • (aV p (j + r - 1 - p) ∘ₗ N.Fd 1)

/-- Part D: `F` on the basis vector `(b, j, i)`. -/
def psiFB (r : ℕ) (x : Bool × Fin p × N.ι) : Bool × Fin p × N.ι → ℤ_[p] :=
  psiFL p N r x.1 x.2.1 (Pi.single x.2.2 1)

/-- Part D: `E` on the basis vector `(b, j, i)` (with `w = w_i`). -/
def psiEB (r : ℕ) (x : Bool × Fin p × N.ι) : Bool × Fin p × N.ι → ℤ_[p] :=
  psiEL p N r x.1 x.2.1 (N.wt x.2.2) (Pi.single x.2.2 1)

/-- Part D: the single operator `F` of `Ψ_r(N)` (Definition 1.3 with `u = −1`), the linear
extension of the formulas on basis vectors. -/
def psiF (r : ℕ) : Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Bool × Fin p × N.ι)).constr ℤ_[p] (psiFB p N r)

/-- Part D: the single operator `E` of `Ψ_r(N)` (Definition 1.3 with `u = −1`), the linear
extension of the formulas on basis vectors. -/
def psiE (r : ℕ) : Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]) :=
  (Pi.basisFun ℤ_[p] (Bool × Fin p × N.ι)).constr ℤ_[p] (psiEB p N r)

lemma psiF_single (r : ℕ) (x : Bool × Fin p × N.ι) : psiF p N r (Pi.single x 1) = psiFB p N r x := by
  rw [psiF, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma psiE_single (r : ℕ) (x : Bool × Fin p × N.ι) : psiE p N r (Pi.single x 1) = psiEB p N r x := by
  rw [psiE, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis]

lemma psiF_aV (r : ℕ) {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    psiF p N r (aV p j n) = psiFL p N r false j n := by
  have : psiF p N r ∘ₗ aV p j = psiFL p N r false j := ext_single fun i => by
    rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_false,
      psiF_single]; rfl
  exact LinearMap.congr_fun this n

lemma psiF_cV (r : ℕ) {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    psiF p N r (cV p j n) = psiFL p N r true j n := by
  have : psiF p N r ∘ₗ cV p j = psiFL p N r true j := ext_single fun i => by
    rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_true,
      psiF_single]; rfl
  exact LinearMap.congr_fun this n

lemma psiE_aV (r : ℕ) {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (aV p j n) = psiEL p N r false j w n :=
  Doubling.eq_on_inWt (psiE p N r ∘ₗ aV p j) (psiEL p N r false j w)
    (fun i hi => by
      rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_false,
        psiE_single, psiEB]
      simp only [hi]) hn

lemma psiE_cV (r : ℕ) {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (cV p j n) = psiEL p N r true j w n :=
  Doubling.eq_on_inWt (psiE p N r ∘ₗ cV p j) (psiEL p N r true j w)
    (fun i hi => by
      rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_true,
        psiE_single, psiEB]
      simp only [hi]) hn

/-! ### The formulas of Definition 1.3 -/

variable {p N}

lemma two_le_p' : 2 ≤ p := (Fact.out : p.Prime).two_le

/-- Part D: `F(A_j n) = A_{j+1} n` for `j ≤ p − 2`. -/
lemma psiF_A_lt (r : ℕ) {j : ℕ} (hj : j + 1 < p) (n : N.ι → ℤ_[p]) :
    psiF p N r (aV p j n) = aV p (j + 1) n := by
  rw [psiF_aV p N r (by omega), psiFL, if_pos hj]

/-- Part D: `F(A_{p−1} n) = −p·A_0(Fn) + p·C_{p−r} n`. -/
lemma psiF_A_last (r : ℕ) (n : N.ι → ℤ_[p]) :
    psiF p N r (aV p (p - 1) n) = (-(p : ℤ_[p])) • aV p 0 (N.Fd 1 n) + (p : ℤ_[p]) • cV p (p - r) n := by
  have := two_le_p' (p := p)
  rw [psiF_aV p N r (by omega), psiFL, if_neg (by omega)]; rfl

/-- Part D: `F(C_j n) = C_{j+1} n` for `j ≤ p − 2`. -/
lemma psiF_C_lt (r : ℕ) {j : ℕ} (hj : j + 1 < p) (n : N.ι → ℤ_[p]) :
    psiF p N r (cV p j n) = cV p (j + 1) n := by
  rw [psiF_cV p N r (by omega), psiFL, if_pos hj]

/-- Part D: `F(C_{p−1} n) = −p·C_0(Fn)`. -/
lemma psiF_C_last (r : ℕ) (n : N.ι → ℤ_[p]) :
    psiF p N r (cV p (p - 1) n) = (-(p : ℤ_[p])) • cV p 0 (N.Fd 1 n) := by
  have := two_le_p' (p := p)
  rw [psiF_cV p N r (by omega), psiFL, if_neg (by omega)]; rfl

/-- Part D: `E(A_0 n) = −p·A_{p−1}(En) + (p − r)p·C_{p−1−r}(En)`. -/
lemma psiE_A_zero (r : ℕ) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (aV p 0 n) = (-(p : ℤ_[p])) • aV p (p - 1) (N.Ed 1 n) +
      (((p : ℤ_[p]) - r) * p) • cV p (p - 1 - r) (N.Ed 1 n) := by
  have := two_le_p' (p := p)
  rw [psiE_aV p N r (by omega) hn, psiEL, if_pos rfl]; rfl

/-- Part D: `E(A_j n) = A_{j−1}(g^A_j n) − rp·C_{p+j−1−r}(En)` for `1 ≤ j ≤ r`. -/
lemma psiE_A_low (r : ℕ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ r) (hj : j < p) {w : ℤ}
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (aV p j n) = aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) -
      ((r : ℤ_[p]) * p) • cV p (p + j - 1 - r) (N.Ed 1 n) := by
  rw [psiE_aV p N r hj hn, psiEL, if_neg (by omega), if_pos h2]; rfl

/-- Part D: `E(A_j n) = A_{j−1}(g^A_j n) + rp²·C_{j−1−r}(Xn)` for `r + 1 ≤ j ≤ p − 1`. -/
lemma psiE_A_high (r : ℕ) {j : ℕ} (h1 : r + 1 ≤ j) (hj : j < p) {w : ℤ}
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (aV p j n) = aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) +
      ((r : ℤ_[p]) * p ^ 2) • cV p (j - 1 - r) (N.Fd 1 (N.Ed 1 n)) := by
  rw [psiE_aV p N r hj hn, psiEL, if_neg (by omega), if_neg (by omega)]; rfl

/-- Part D: `E(C_0 n) = r·A_{r−1} n − p·C_{p−1}(En)`. -/
lemma psiE_C_zero (r : ℕ) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (cV p 0 n) = (r : ℤ_[p]) • aV p (r - 1) n - (p : ℤ_[p]) • cV p (p - 1) (N.Ed 1 n) := by
  have := two_le_p' (p := p)
  rw [psiE_cV p N r (by omega) hn, psiEL, if_pos rfl]; rfl

/-- Part D: `E(C_j n) = C_{j−1}(g^C_j n) + r·A_{j+r−1} n` for `1 ≤ j ≤ p − r`. -/
lemma psiE_C_low (r : ℕ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ p - r) (hj : j < p) {w : ℤ}
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (cV p j n) = cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j)) • n) + (r : ℤ_[p]) • aV p (j + r - 1) n := by
  rw [psiE_cV p N r hj hn, psiEL, if_neg (by omega), if_pos h2]; rfl

/-- Part D: `E(C_j n) = C_{j−1}((g^C_j + rp) n) − rp·A_{j+r−1−p}(Fn)` for
`p − r + 1 ≤ j ≤ p − 1`. -/
lemma psiE_C_high (r : ℕ) {j : ℕ} (h1 : p - r + 1 ≤ j) (hj : j < p) {w : ℤ}
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (cV p j n) = cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j) + r * p) • n) -
      ((r : ℤ_[p]) * p) • aV p (j + r - 1 - p) (N.Fd 1 n) := by
  rw [psiE_cV p N r hj hn, psiEL, if_neg (by omega), if_neg (by omega)]
  simp only [gC, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  congr 2
  rw [add_assoc, ← add_smul]

/-! ### Weights -/

lemma inWt_aV (r k : ℕ) {μ : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt μ n) :
    InWt (psiWt p N r) (p * μ + p - 1 + r - 2 * (k : ℤ)) (aV p k n) := by
  intro ⟨b, j, i⟩ h
  rw [aV_apply]
  split_ifs with hb
  · obtain ⟨hb, hj⟩ := hb
    subst hb
    simp only at hj
    exact hn i fun hi => h (by simp [psiWt, hi, ← hj])
  · rfl

lemma inWt_cV (r k : ℕ) {μ : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt μ n) :
    InWt (psiWt p N r) (p * μ + p - 1 - r - 2 * (k : ℤ)) (cV p k n) := by
  intro ⟨b, j, i⟩ h
  rw [cV_apply]
  split_ifs with hb
  · obtain ⟨hb, hj⟩ := hb
    subst hb
    simp only at hj
    exact hn i fun hi => h (by simp [psiWt, hi, ← hj]; ring)
  · rfl

/-- Part D, weights: `H(A_j n) = (pw + p − 1 + r − 2j) A_j n` for `n` of weight `w`. -/
lemma H_aV (r k : ℕ) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    Hop (psiWt p N r) (aV p k n) = ((p * w + p - 1 + r - 2 * (k : ℤ) : ℤ) : ℤ_[p]) • aV p k n :=
  Doubling.Hop_of_inWt (inWt_aV r k hn)

/-- Part D, weights: `H(C_j n) = (pw + p − 1 − r − 2j) C_j n` for `n` of weight `w`. -/
lemma H_cV (r k : ℕ) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    Hop (psiWt p N r) (cV p k n) = ((p * w + p - 1 - r - 2 * (k : ℤ) : ℤ) : ℤ_[p]) • cV p k n :=
  Doubling.Hop_of_inWt (inWt_cV r k hn)

/-- Part D: the formulas of Definition 1.3 (with `u = −1`) hold for the operators `psiF`,
`psiE` and the weights `psiWt`; `F` on every vector `n`, `E` on every vector `n` of weight `w`. -/
theorem D_formulas (r : ℕ) :
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n →
      Hop (psiWt p N r) (aV p j n) = ((p * w + p - 1 + r - 2 * (j : ℤ) : ℤ) : ℤ_[p]) • aV p j n ∧
      Hop (psiWt p N r) (cV p j n) = ((p * w + p - 1 - r - 2 * (j : ℤ) : ℤ) : ℤ_[p]) • cV p j n) ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), j + 1 < p →
      psiF p N r (aV p j n) = aV p (j + 1) n ∧ psiF p N r (cV p j n) = cV p (j + 1) n) ∧
    (∀ n : N.ι → ℤ_[p], psiF p N r (aV p (p - 1) n) =
      (-(p : ℤ_[p])) • aV p 0 (N.Fd 1 n) + (p : ℤ_[p]) • cV p (p - r) n) ∧
    (∀ n : N.ι → ℤ_[p], psiF p N r (cV p (p - 1) n) = (-(p : ℤ_[p])) • cV p 0 (N.Fd 1 n)) ∧
    (∀ (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n →
      psiE p N r (aV p 0 n) = (-(p : ℤ_[p])) • aV p (p - 1) (N.Ed 1 n) +
        (((p : ℤ_[p]) - r) * p) • cV p (p - 1 - r) (N.Ed 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), 1 ≤ j → j ≤ r → j < p → InWt N.wt w n →
      psiE p N r (aV p j n) = aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) -
      ((r : ℤ_[p]) * p) • cV p (p + j - 1 - r) (N.Ed 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), r + 1 ≤ j → j < p → InWt N.wt w n →
      psiE p N r (aV p j n) = aV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p + r - j)) • n) +
      ((r : ℤ_[p]) * p ^ 2) • cV p (j - 1 - r) (N.Fd 1 (N.Ed 1 n))) ∧
    (∀ (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n →
      psiE p N r (cV p 0 n) = (r : ℤ_[p]) • aV p (r - 1) n - (p : ℤ_[p]) • cV p (p - 1) (N.Ed 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), 1 ≤ j → j ≤ p - r → j < p → InWt N.wt w n →
      psiE p N r (cV p j n) = cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j)) • n) + (r : ℤ_[p]) • aV p (j + r - 1) n) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), p - r + 1 ≤ j → j < p → InWt N.wt w n →
      psiE p N r (cV p j n) = cV p (j - 1) ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) +
        ((j : ℤ_[p]) * (p * (w : ℤ_[p]) + p - r - j) + r * p) • n) -
      ((r : ℤ_[p]) * p) • aV p (j + r - 1 - p) (N.Fd 1 n)) :=
  ⟨fun j _ _ hn => ⟨H_aV r j hn, H_cV r j hn⟩, fun _ n hj => ⟨psiF_A_lt r hj n, psiF_C_lt r hj n⟩,
    psiF_A_last r, psiF_C_last r, fun _ _ hn => psiE_A_zero r hn,
    fun _ _ _ h1 h2 hj hn => psiE_A_low r h1 h2 hj hn,
    fun _ _ _ h1 hj hn => psiE_A_high r h1 hj hn, fun _ _ hn => psiE_C_zero r hn,
    fun _ _ _ h1 h2 hj hn => psiE_C_low r h1 h2 hj hn,
    fun _ _ _ h1 hj hn => psiE_C_high r h1 hj hn⟩

end ColouredSand.OddTwist
