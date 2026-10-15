module

public import RequestProject.OddSES.CasimirTwist

/-!
# `CSI4_the_short_exact_sequences.md`: Part P, (P1) — `Ψ_p(N) := Φ_p(V ⊗ N)`

Encodings:

* `Psip p N := twist p (Tensor2.tensor (V ℤ_[p]) N)` is `Φ_p(V ⊗ N)`, with basis
  `Fin p × (Fin 2 × N.ι)`; the vector `b_j (b̂_e ⊗ n)` is `bv p j (tv e n)`.
* `Pmap p N : (Bool × Fin p × N.ι → ℤ_[p]) → (Fin p × (Fin 2 × N.ι) → ℤ_[p])` is the
  identification of (P1) of the coordinates of Definition 1.3 (with `r = p`) with those of
  `Φ_p(V ⊗ N)`: `A_j n ↦ b_j (b̂_0 ⊗ n)` and `C_j n ↦ −b_j (b̂_1 ⊗ n)` (`Pmap_aV`, `Pmap_cV`);
  `Pinv p N` is its inverse.
* (P1) is `P1`: `Pmap` is a linear isomorphism with these values, the weights agree
  (`p(w+1) + p − 1 − 2j` for `A_j δ_i` and `p(w−1) + p − 1 − 2j` for `C_j δ_i`, `w = w_i`), and
  moreover the single operators `psiF p N p`, `psiE p N p` of Definition 1.3 with `r = p`
  correspond to `F`, `E` of `Φ_p(V ⊗ N)` (`Pmap_F`, `Pmap_E`): so `Φ_p(V ⊗ N)` is the lattice of
  Definition 1.3 for `r = p`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

/-- (P1) `Ψ_p(N) := Φ_p(V ⊗ N)`, basis `Fin p × (Fin 2 × N.ι)`. -/
abbrev Psip : DPLattice ℤ_[p] := twist p (Tensor2.tensor (V ℤ_[p]) N)

/-- (P1) the identification `A_j n ↦ b_j (b̂_0 ⊗ n)`, `C_j n ↦ −b_j (b̂_1 ⊗ n)`. -/
def Pmap : (Bool × Fin p × N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × (Fin 2 × N.ι) → ℤ_[p]) where
  toFun x y := if y.2.1 = 0 then x (false, y.1, y.2.2) else -x (true, y.1, y.2.2)
  map_add' x x' := by
    funext y; by_cases h : y.2.1 = 0 <;> simp only [h, if_true, if_false, Pi.add_apply] <;> abel
  map_smul' c x := by
    funext y; by_cases h : y.2.1 = 0 <;> simp [h]

/-- (P1) the inverse identification `b_j (b̂_0 ⊗ n) ↦ A_j n`, `b_j (b̂_1 ⊗ n) ↦ −C_j n`. -/
def Pinv : (Fin p × (Fin 2 × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) where
  toFun y x := if x.1 then -y (x.2.1, (1, x.2.2)) else y (x.2.1, (0, x.2.2))
  map_add' y y' := by
    funext x; by_cases h : x.1 <;> simp only [h, if_true, if_false, Pi.add_apply,
      Bool.false_eq_true] <;> abel
  map_smul' c y := by
    funext x; by_cases h : x.1 <;> simp [h]

variable {p N}

lemma Pmap_apply (x : Bool × Fin p × N.ι → ℤ_[p]) (y : Fin p × (Fin 2 × N.ι)) :
    Pmap p N x y = if y.2.1 = 0 then x (false, y.1, y.2.2) else -x (true, y.1, y.2.2) := rfl

lemma Pinv_apply (y : Fin p × (Fin 2 × N.ι) → ℤ_[p]) (x : Bool × Fin p × N.ι) :
    Pinv p N y x = if x.1 then -y (x.2.1, (1, x.2.2)) else y (x.2.1, (0, x.2.2)) := rfl

lemma fin2_cases (e : Fin 2) : e = 0 ∨ e = 1 := by fin_cases e <;> simp

/-- (P1) `A_j n ↦ b_j (b̂_0 ⊗ n)`. -/
lemma Pmap_aV (k : ℕ) (n : N.ι → ℤ_[p]) : Pmap p N (aV p k n) = bv p k (tv 0 n) := by
  funext ⟨j, e, i⟩
  rcases fin2_cases e with rfl | rfl <;>
    simp [Pmap_apply, aV_apply, tv_apply, bv_apply]

/-- (P1) `C_j n ↦ −b_j (b̂_1 ⊗ n)`. -/
lemma Pmap_cV (k : ℕ) (n : N.ι → ℤ_[p]) : Pmap p N (cV p k n) = -bv p k (tv 1 n) := by
  funext ⟨j, e, i⟩
  rcases fin2_cases e with rfl | rfl <;>
    simp [Pmap_apply, cV_apply, tv_apply, bv_apply]

lemma Pinv_bv0 (k : ℕ) (n : N.ι → ℤ_[p]) : Pinv p N (bv p k (tv 0 n)) = aV p k n := by
  funext ⟨b, j, i⟩
  cases b <;> simp [Pinv_apply, aV_apply, tv_apply, bv_apply]

lemma Pinv_bv1 (k : ℕ) (n : N.ι → ℤ_[p]) : Pinv p N (bv p k (tv 1 n)) = -cV p k n := by
  funext ⟨b, j, i⟩
  cases b <;> simp [Pinv_apply, cV_apply, tv_apply, bv_apply]

lemma Pinv_Pmap : Pinv p N ∘ₗ Pmap p N = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun ⟨b, j, i⟩ => ?_
  cases b <;> simp [Pinv_apply, Pmap_apply]

lemma Pmap_Pinv : Pmap p N ∘ₗ Pinv p N = LinearMap.id := by
  refine LinearMap.ext fun y => funext fun ⟨j, e, i⟩ => ?_
  rcases fin2_cases e with rfl | rfl <;> simp [Pinv_apply, Pmap_apply]

lemma Pmap_injective : Function.Injective (Pmap p N) := fun x y h => by
  have := congrArg (Pinv p N) h
  rwa [← LinearMap.comp_apply, Pinv_Pmap, ← LinearMap.comp_apply, Pinv_Pmap] at this

/-! ### Weights -/

lemma Psip_wt (j : Fin p) (e : Fin 2) (i : N.ι) :
    (Psip p N).wt (j, (e, i)) = p * (wtV e + N.wt i) + p - 1 - 2 * ((j : ℕ) : ℤ) := by
  simp [Psip, twist, twWt, Tensor2.tensor, V]

/-- (P1) the weight of `b_j (b̂_0 ⊗ δ_i)` is `p(w+1) + p − 1 − 2j`, that of `A_j δ_i` for
`r = p`. -/
lemma Psip_wt_zero (j : Fin p) (i : N.ι) :
    (Psip p N).wt (j, ((0 : Fin 2), i)) = p * (N.wt i + 1) + p - 1 - 2 * ((j : ℕ) : ℤ) ∧
    (Psip p N).wt (j, ((0 : Fin 2), i)) = psiWt p N p (false, j, i) := by
  rw [Psip_wt]; simp only [wtV_zero, psiWt, Bool.false_eq_true, if_false]; constructor <;> ring

/-- (P1) the weight of `b_j (b̂_1 ⊗ δ_i)` is `p(w−1) + p − 1 − 2j`, that of `C_j δ_i` for
`r = p`. -/
lemma Psip_wt_one (j : Fin p) (i : N.ι) :
    (Psip p N).wt (j, ((1 : Fin 2), i)) = p * (N.wt i - 1) + p - 1 - 2 * ((j : ℕ) : ℤ) ∧
    (Psip p N).wt (j, ((1 : Fin 2), i)) = psiWt p N p (true, j, i) := by
  rw [Psip_wt]; simp only [wtV_one, psiWt, if_true]; constructor <;> ring

/-- (P1) the identification preserves the weights. -/
lemma Pmap_H : Pmap p N ∘ₗ Hop (psiWt p N p) = H (Psip p N) ∘ₗ Pmap p N := by
  refine LinearMap.ext fun x => funext fun ⟨j, e, i⟩ => ?_
  change Pmap p N (Hop (psiWt p N p) x) (j, e, i) = (Psip p N).wt (j, e, i) * Pmap p N x (j, e, i)
  simp only [Hop_apply, Pmap_apply]
  rcases fin2_cases e with rfl | rfl
  · simp only [if_true]; rw [(Psip_wt_zero j i).2]
  · simp only [show (1 : Fin 2) ≠ 0 from by decide, if_false, mul_neg]
    rw [(Psip_wt_one j i).2]

/-! ### The single operators -/

section ops

/-- `F^{p}`-coordinates: the vector space `Fin p × (Fin 2 × N.ι) → ℤ_[p]` of `Φ_p(V ⊗ N)`. -/
abbrev PV (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p]) : Type := Fin p × (Fin 2 × N.ι) → ℤ_[p]

variable (N) in
lemma Psip_F_lt {j : ℕ} (hj : j + 1 < p) (e : Fin 2) (n : N.ι → ℤ_[p]) :
    (Psip p N).Fd 1 (bv p j (tv e n) : PV p N) = (bv p (j + 1) (tv e n) : PV p N) :=
  (B1 p (Tensor2.tensor (V ℤ_[p]) N)).1 j (tv e n) hj

lemma Psip_F_last0 (n : N.ι → ℤ_[p]) :
    (Psip p N).Fd 1 (bv p (p - 1) (tv 0 n) : PV p N) =
      (-(p : ℤ_[p])) • (bv p 0 (tv 1 n + tv 0 (N.Fd 1 n)) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.1 (tv 0 n)
  rw [tensorV_Fd1_tv0] at this; exact this

lemma Psip_F_last1 (n : N.ι → ℤ_[p]) :
    (Psip p N).Fd 1 (bv p (p - 1) (tv 1 n) : PV p N) =
      (-(p : ℤ_[p])) • (bv p 0 (tv 1 (N.Fd 1 n)) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.1 (tv 1 n)
  rw [tensorV_Fd1_tv1] at this; exact this

lemma Psip_E_zero0 (n : N.ι → ℤ_[p]) :
    (Psip p N).Ed 1 (bv p 0 (tv 0 n) : PV p N) =
      (-(p : ℤ_[p])) • (bv p (p - 1) (tv 0 (N.Ed 1 n)) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.2.2.1 (tv 0 n)
  rw [tensorV_Ed1_tv0] at this; exact this

lemma Psip_E_zero1 (n : N.ι → ℤ_[p]) :
    (Psip p N).Ed 1 (bv p 0 (tv 1 n) : PV p N) =
      (-(p : ℤ_[p])) • (bv p (p - 1) (tv 0 n + tv 1 (N.Ed 1 n)) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.2.2.1 (tv 1 n)
  rw [tensorV_Ed1_tv1] at this; exact this

lemma Psip_E_pos0 {j : ℕ} (h1 : 1 ≤ j) (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) : (Psip p N).Ed 1 (bv p j (tv 0 n) : PV p N) = (bv p (j - 1)
      ((p : ℤ_[p]) ^ 2 • (tv 1 (N.Ed 1 n) + tv 0 (N.Fd 1 (N.Ed 1 n))) +
        (((j : ℤ) * (p * (1 + w) + p - j) : ℤ) : ℤ_[p]) • tv 0 n) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.2.1 j (wtV 0 + w) (tv 0 n) h1 hj
    (inWt_tv N 0 hn)
  rw [tensorV_Ed1_tv0, tensorV_Fd1_tv0, wtV_zero] at this; exact this

lemma Psip_E_pos1 {j : ℕ} (h1 : 1 ≤ j) (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) : (Psip p N).Ed 1 (bv p j (tv 1 n) : PV p N) = (bv p (j - 1)
      ((p : ℤ_[p]) ^ 2 • (tv 1 n + tv 0 (N.Fd 1 n) + tv 1 (N.Fd 1 (N.Ed 1 n))) +
        (((j : ℤ) * (p * (-1 + w) + p - j) : ℤ) : ℤ_[p]) • tv 1 n) : PV p N) := by
  have := (B1 p (Tensor2.tensor (V ℤ_[p]) N)).2.2.1 j (wtV 1 + w) (tv 1 n) h1 hj
    (inWt_tv N 1 hn)
  rw [tensorV_Ed1_tv1, ((Tensor2.tensor (V ℤ_[p]) N).Fd 1).map_add, tensorV_Fd1_tv0,
    tensorV_Fd1_tv1, wtV_one] at this
  exact this

end ops

/-- (P1) `F` of Definition 1.3 with `r = p` corresponds to `F` of `Φ_p(V ⊗ N)`. -/
theorem Pmap_F : Pmap p N ∘ₗ psiF p N p = (Psip p N).Fd 1 ∘ₗ Pmap p N := by
  have hp := two_le_p' (p := p)
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · change Pmap p N (psiF p N p (aV p j (Pi.single i 1))) =
      (Psip p N).Fd 1 (Pmap p N (aV p j (Pi.single i 1)))
    rw [Pmap_aV]
    by_cases hl : j + 1 < p
    · rw [psiF_A_lt p hl, Pmap_aV, Psip_F_lt N hl]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_A_last, map_add, map_smul, map_smul, Pmap_aV, Pmap_cV, Psip_F_last0,
        Nat.sub_self]
      simp only [map_add, smul_add, smul_neg]
      module
  · change Pmap p N (psiF p N p (cV p j (Pi.single i 1))) =
      (Psip p N).Fd 1 (Pmap p N (cV p j (Pi.single i 1)))
    rw [Pmap_cV, map_neg]
    by_cases hl : j + 1 < p
    · rw [psiF_C_lt p hl, Pmap_cV, Psip_F_lt N hl]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_C_last, map_smul, Pmap_cV, Psip_F_last1]
      simp only [smul_neg, neg_smul, neg_neg]

/-- (P1) `E` of Definition 1.3 with `r = p` corresponds to `E` of `Φ_p(V ⊗ N)`. -/
theorem Pmap_E : Pmap p N ∘ₗ psiE p N p = (Psip p N).Ed 1 ∘ₗ Pmap p N := by
  have hp := two_le_p' (p := p)
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    change Pmap p N (psiE p N p (aV p j (Pi.single i 1))) =
      (Psip p N).Ed 1 (Pmap p N (aV p j (Pi.single i 1)))
    rw [Pmap_aV]
    rcases Nat.eq_zero_or_pos j with rfl | h1
    · rw [psiE_A_zero p hn, map_add, map_smul, map_smul, Pmap_aV, Pmap_cV, Psip_E_zero0, sub_self, zero_mul, zero_smul, add_zero]
    · rw [psiE_A_low p h1 (by omega) hj hn, map_sub, map_smul, Pmap_aV, Pmap_cV,
        Psip_E_pos0 h1 hj hn, show p + j - 1 - p = j - 1 by omega]
      simp only [map_add, map_smul, smul_neg, sub_neg_eq_add]
      push_cast
      module
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    change Pmap p N (psiE p N p (cV p j (Pi.single i 1))) =
      (Psip p N).Ed 1 (Pmap p N (cV p j (Pi.single i 1)))
    rw [Pmap_cV, map_neg]
    rcases Nat.eq_zero_or_pos j with rfl | h1
    · rw [psiE_C_zero p hn, map_sub, map_smul, map_smul, Pmap_aV, Pmap_cV, Psip_E_zero1]
      simp only [map_add, smul_add, smul_neg, neg_smul, neg_neg, sub_neg_eq_add]
      module
    · rw [psiE_C_high p (by omega) hj hn, map_sub, map_smul, Pmap_aV, Pmap_cV,
        Psip_E_pos1 h1 hj hn, show j + p - 1 - p = j - 1 by omega]
      simp only [map_add, map_smul, map_neg, wtV_one, smul_neg, smul_add]
      push_cast
      module

/-- (D1) for `r = p`: `E F = F E + H` for the operators of Definition 1.3 with `r = p`
(transported from `Φ_p(V ⊗ N)` along (P1)). -/
lemma psi_D1_p (y : Bool × Fin p × N.ι → ℤ_[p]) :
    psiE p N p (psiF p N p y) = psiF p N p (psiE p N p y) + Hop (psiWt p N p) y := by
  apply Pmap_injective
  have hF : ∀ z, Pmap p N (psiF p N p z) = (Psip p N).Fd 1 (Pmap p N z) :=
    fun z => LinearMap.congr_fun (Pmap_F (p := p) (N := N)) z
  have hE : ∀ z, Pmap p N (psiE p N p z) = (Psip p N).Ed 1 (Pmap p N z) :=
    fun z => LinearMap.congr_fun (Pmap_E (p := p) (N := N)) z
  have hH : ∀ z, Pmap p N (Hop (psiWt p N p) z) = H (Psip p N) (Pmap p N z) :=
    fun z => LinearMap.congr_fun (Pmap_H (p := p) (N := N)) z
  rw [map_add, hE, hF, hF, hE, hH]
  exact Doubling.dp_lie (Psip p N) _

/-- (P1) **`Ψ_p(N) := Φ_p(V ⊗ N)`.** The identification `Pmap` (with inverse `Pinv`) sends
`A_j n ↦ b_j (b̂_0 ⊗ n)` and `C_j n ↦ −b_j (b̂_1 ⊗ n)`; the weights agree
(`p(w+1) + p − 1 − 2j` and `p(w−1) + p − 1 − 2j`, those of Definition 1.3 with `r = p`); and
(more than the file states explicitly) the single operators of Definition 1.3 with `r = p`
correspond to those of `Φ_p(V ⊗ N)`. -/
theorem P1 :
    Pinv p N ∘ₗ Pmap p N = LinearMap.id ∧ Pmap p N ∘ₗ Pinv p N = LinearMap.id ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), Pmap p N (aV p j n) = bv p j (tv 0 n)) ∧
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), Pmap p N (cV p j n) = -bv p j (tv 1 n)) ∧
    (∀ (j : Fin p) (i : N.ι),
      (Psip p N).wt (j, ((0 : Fin 2), i)) = p * (N.wt i + 1) + p - 1 - 2 * ((j : ℕ) : ℤ) ∧
      (Psip p N).wt (j, ((0 : Fin 2), i)) = psiWt p N p (false, j, i)) ∧
    (∀ (j : Fin p) (i : N.ι),
      (Psip p N).wt (j, ((1 : Fin 2), i)) = p * (N.wt i - 1) + p - 1 - 2 * ((j : ℕ) : ℤ) ∧
      (Psip p N).wt (j, ((1 : Fin 2), i)) = psiWt p N p (true, j, i)) ∧
    Pmap p N ∘ₗ psiF p N p = (Psip p N).Fd 1 ∘ₗ Pmap p N ∧
    Pmap p N ∘ₗ psiE p N p = (Psip p N).Ed 1 ∘ₗ Pmap p N :=
  ⟨Pinv_Pmap, Pmap_Pinv, Pmap_aV, Pmap_cV, Psip_wt_zero, Psip_wt_one, Pmap_F, Pmap_E⟩

end ColouredSand.OddTwist
