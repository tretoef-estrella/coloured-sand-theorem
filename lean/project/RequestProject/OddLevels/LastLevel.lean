module

public import RequestProject.OddLevels.Basic
public import RequestProject.OddPayment.Chain
public import RequestProject.OddSplitMove.Basic
public import RequestProject.DPLattice.Weyl
public import RequestProject.OddTwist.Basic

/-!
# `CSI9_last_level_and_floors.md`, Part L — the last level (Proposition 2.3)

Namespace `ColouredSand.OddTwist`. Reuses C11's `Payment.Sys`, CSI7's `Gp`, `oslot`, `oslotE`,
`lproj`, `chainOp`, `chainProd`, `chainCokerEquiv` (`RequestProject/OddPayment/`), CSI8's `prodQ`
(`RequestProject/OddSplitMove/`), C18's `DPLattice.delta` and CSI1's
`isUnit_natCast_of_not_dvd`.

## Encoding

* `Δ(d−1)` is C18's `DPLattice.delta A (d − 1)`: basis `Fin (d − 1 + 1)` (the vectors `e_s`,
  `s ≤ d − 1`), and `F = Fd 1` with `F e_s = (s+1) e_{s+1}` (`F e_{d−1} = 0`). As a graded family
  (Basic.lean): modules `N s = A`, operator `famF (delta A (d−1))`, floor `fl e_s = s`
  (`Fin.val`).
* The system is CSI7's `Gp p Fin.val (famF (delta A (d−1))) Q` on
  `Payment.Sys (fun _ : Fin (d − 1 + 1) => A) S = ⨁ (s, k) : S × Fin (d−1+1), A`.
* `Mlast := Q 0 * Q 1 * ⋯ * Q (d−1)` is CSI8's `prodQ Q 0 d`.
* **Convention for `Mlast` (as asked by the file).** The cokernel `S → A` is the last factor;
  the basis vector `Pi.single s 1` is the class of the generator `e_0 ι_s`. CSI7's relations are
  read on row vectors: the relation attached to the generator `x ι_{s'}` is
  `g(Fx) + Σ_s g(x ι_s) (p Q)_{s s'} = 0`, i.e. the row vector of generators `g` is multiplied on
  the right by `p Q`. The coefficient vector of the `s'`-th entry of `g · M` is the `s'`-th column
  of `M`, so the submodule of relations of the last level is the range of the linear map
  `v ↦ M *ᵥ v` on coefficient (column) vectors, `Matrix.mulVecLin M`, with
  `M = p^d • Mlast`. (Over a principal ideal ring such as `ℤ_[p]` the cokernel of `M` and of its
  transpose are isomorphic by the Smith form, but the isomorphism stated here is the natural one,
  with `Mlast` acting on coefficient vectors.)
* `Fin (d − 1) → (S → A) ⧸ c • ⊤` are the `d − 1` copies of `(S → A) ⧸ c`.

## Generality

The theorem `L1_general` holds over any commutative ring `A` in which `1, 2, …, d − 1` are units
(this is the only thing the proof uses: the pivots `c (s + 1)` are `c` times units); for `ℤ_[p]`
with `p` prime and `1 ≤ d ≤ p − 1` this holds (`L1`). Neither oddness of `p` nor `1 ≤ d` beyond
`d − 1 + 1 = d` is used.

## Proof (as in the report)

1. `layerL`: `Payment.Sys (fun _ : Fin m => A) S ≃ (Fin m → S → A)` (layer `k`, slot `s`); the system
   becomes `Gch`: `(Gch w)_k = k • w_{k−1} + p Q(k) *ᵥ w_k` (`layerL_comp_Gp`).
2. Rescaling the layers by `k!` (units) turns `Gch` into CSI7's chain operator
   `chainOp m D 0` with `D k = p Q(k) *ᵥ ·` (`Gch_comp_diag`): `g_{s+1} = −g_s · pQ(s)/(s+1)`.
3. CSI7's `chainCokerEquiv` (with `E = 0`) gives the `d − 1` copies of `(S → A) ⧸ c` and the last
   relation `(−1)^{d−1} D 0 ⋯ D (d−1) = (−1)^{d−1} p^d Mlast`; the unit `(−1)^{d−1}` does not
   change the cokernel.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DirectSum

open scoped Pointwise

variable {A : Type*} [CommRing A] {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Layers -/

variable (A S) in
/-- The layers of a system on a family indexed by `Fin m` with all modules `A` (Part L, *Proof*,
of `CSI9_last_level_and_floors.md`): `x ↦ (k ↦ (s ↦ x (s, k)))`, the coordinate of the generator
`e_k ι_s`. -/
def layerL (m : ℕ) : Payment.Sys (fun _ : Fin m => A) S ≃ₗ[A] (Fin m → S → A) :=
  (DirectSum.linearEquivFunOnFintype A (S × Fin m) (fun _ => A)).trans
    ((LinearEquiv.funCongrLeft A A (Equiv.prodComm (Fin m) S)).trans
      (LinearEquiv.curry A A (Fin m) S))

lemma layerL_oslot (m : ℕ) (s : S) (k : Fin m) (a : A) :
    layerL A S m (oslot A (fun _ : Fin m => A) S s k a) = Pi.single k (Pi.single s a) := by
  funext k' s'
  simp only [layerL, oslot, LinearEquiv.trans_apply]
  rw [DirectSum.linearEquivFunOnFintype_lof]
  by_cases hk : k' = k <;> by_cases hs : s' = s <;>
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, hk, hs]

lemma layerL_oslotE (m : ℕ) (s : S) (y : ⨁ _ : Fin m, A) :
    layerL A S m (oslotE A (fun _ : Fin m => A) S s y) = fun k => Pi.single s (dsE A (Fin m) y k) := by
  have : (layerL A S m).toLinearMap ∘ₗ oslotE A (fun _ : Fin m => A) S s =
      (LinearMap.pi fun k => (LinearMap.single A (fun _ : S => A) s) ∘ₗ
        LinearMap.proj (R := A) (φ := fun _ : Fin m => A) k) ∘ₗ (dsE A (Fin m)).toLinearMap := by
    refine DirectSum.linearMap_ext A fun k => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, oslotE, DirectSum.toModule_lof]
    rw [layerL_oslot, dsE_lof]
    funext k'
    by_cases hk : k' = k
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have h := LinearMap.congr_fun this y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [h]
  funext k
  simp

/-- The system on `Δ(m − 1)` read in the layers (Part L, *Proof*, of
`CSI9_last_level_and_floors.md`): `(Gch w)_k = k • w_{k−1} + p • (Q k *ᵥ w_k)` (with no first term
for `k = 0`). -/
def Gch (p m : ℕ) (Q : ℕ → Matrix S S A) : (Fin m → S → A) →ₗ[A] (Fin m → S → A) :=
  LinearMap.pi fun k =>
    (if h : k.val = 0 then 0 else (k.val : A) • lproj (A := A) (X := S → A) ⟨k.val - 1, by omega⟩) +
      ((p : A) • (Q k.val).mulVecLin) ∘ₗ lproj (A := A) (X := S → A) k

omit [DecidableEq S] in
lemma Gch_apply (p m : ℕ) (Q : ℕ → Matrix S S A) (w : Fin m → S → A) (k : Fin m) :
    Gch p m Q w k = (if h : k.val = 0 then 0 else (k.val : A) • w ⟨k.val - 1, by omega⟩) +
      (p : A) • (Q k.val).mulVec (w k) := by
  unfold Gch
  by_cases h : k.val = 0 <;> simp [h]

/-- **Step 1** (Part L, *Proof*, of `CSI9_last_level_and_floors.md`): in the layers, the system
`Gp p Fin.val (famF Δ(n)) Q` is `Gch`. -/
theorem layerL_comp_Gp (p n : ℕ) (Q : ℕ → Matrix S S A) :
    (layerL A S (n + 1)).toLinearMap ∘ₗ Gp p Fin.val (famF (DPLattice.delta A n)) Q =
      Gch p (n + 1) Q ∘ₗ (layerL A S (n + 1)).toLinearMap := by
  refine DirectSum.linearMap_ext A fun q => LinearMap.ext_ring ?_
  obtain ⟨s', k⟩ := q
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Gp, DirectSum.toModule_lof,
    LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  rw [map_add, map_sum]
  simp only [map_smul]
  rw [layerL_oslotE]
  simp only [layerL_oslot]
  rw [show (DirectSum.lof A (S × Fin (n + 1)) (fun q => (fun _ : Fin (n + 1) => A) q.2) (s', k) 1)
    = oslot A (fun _ : Fin (n + 1) => A) S s' k 1 from rfl, layerL_oslot]
  have hF : dsE A (Fin (n + 1)) ((famF (DPLattice.delta A n)) (DirectSum.lof A _ _ k 1)) =
      DPLattice.deltaF n 1 (Pi.single k 1) := by
    erw [dsE_famF, dsE_lof]
  funext k2 s2
  rw [Gch_apply]
  simp only [Pi.add_apply]
  erw [hF]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, DPLattice.deltaF_single_apply]
  by_cases h2 : k2 = k
  · subst h2
    have hne : ¬ ((k2 : ℕ) = k2 + 1) := by omega
    rw [if_neg hne]
    simp only [Pi.single_eq_same]
    rw [Matrix.mulVec_single_one]
    split_ifs with h0
    · simp [Pi.single_apply]
    · have h3 : (⟨(k2 : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ k2 := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      simp [Pi.single_eq_of_ne h3, Pi.single_apply]
  · simp only [Pi.single_eq_of_ne h2, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      Matrix.mulVec_zero]
    split_ifs with h3 h0 h0
    · exfalso; apply h2; ext; omega
    · have h4 : (⟨(k2 : ℕ) - 1, by omega⟩ : Fin (n + 1)) = k := Fin.ext (by simp; omega)
      rw [h4, Pi.single_eq_same]
      by_cases hs : s2 = s'
      · subst hs; simp [h3]
      · simp [Pi.single_eq_of_ne hs]
    · simp
    · have h4 : (⟨(k2 : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ k := fun h => by
        apply h3; have := congrArg Fin.val h; simp at this; omega
      simp [Pi.single_eq_of_ne h4]

/-! ### Rescaling the layers -/

/-- The layer operators `D k = p • (Q k *ᵥ ·)` (Part L, *Proof*, of
`CSI9_last_level_and_floors.md`). -/
def Dlay (p : ℕ) (Q : ℕ → Matrix S S A) (k : ℕ) : Module.End A (S → A) :=
  (p : A) • (Q k).mulVecLin

/-- The rescaling of the layers by the units `k!` (Part L, *Proof*, of
`CSI9_last_level_and_floors.md`). -/
def diagL (m : ℕ) (hu : ∀ k : ℕ, k < m → IsUnit ((k.factorial : ℕ) : A)) :
    (Fin m → S → A) ≃ₗ[A] (Fin m → S → A) :=
  LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfUnit (hu k.val k.isLt).unit

omit [Fintype S] [DecidableEq S] in
lemma diagL_apply (m : ℕ) (hu : ∀ k : ℕ, k < m → IsUnit ((k.factorial : ℕ) : A))
    (w : Fin m → S → A) (k : Fin m) :
    diagL m hu w k = ((k.val.factorial : ℕ) : A) • w k := by
  simp [diagL, LinearEquiv.smulOfUnit]

omit [DecidableEq S] in
/-- **Step 2** (Part L, *Proof*, of `CSI9_last_level_and_floors.md`): after rescaling the layer
`k` by `k!`, `Gch` is CSI7's chain operator `chainOp m D 0`. -/
theorem Gch_comp_diag (p m : ℕ) (Q : ℕ → Matrix S S A)
    (hu : ∀ k : ℕ, k < m → IsUnit ((k.factorial : ℕ) : A)) :
    Gch p m Q ∘ₗ (diagL m hu).toLinearMap =
      (diagL m hu).toLinearMap ∘ₗ chainOp m (Dlay p Q) 0 := by
  refine LinearMap.ext fun w => funext fun k => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Gch_apply]
  simp only [diagL_apply]
  rw [chainOp_apply]
  simp only [ Dlay, LinearMap.smul_apply, Matrix.mulVecLin_apply,
    LinearMap.zero_apply, add_zero, Matrix.mulVec_smul]
  split_ifs with h0
  · rw [h0]; simp
  · obtain ⟨j, hj⟩ : ∃ j, k.val = j + 1 := ⟨k.val - 1, by omega⟩
    have e : (⟨k.val - 1, by omega⟩ : Fin m) = ⟨j, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, smul_add, smul_smul, hj, Nat.factorial_succ, smul_comm (p : A)]
    push_cast
    ring_nf

/-! ### The product of the layers -/

lemma prodQ_zero_succ (Q : ℕ → Matrix S S A) (m : ℕ) :
    prodQ Q 0 (m + 1) = prodQ Q 0 m * Q m := by
  simp [prodQ, List.range_succ, List.map_append, List.prod_append]

/-- The product of the layer operators (step 3 of Part L, *Proof*, of
`CSI9_last_level_and_floors.md`): `D 0 ⋯ D m = p^{m+1} • (Q 0 ⋯ Q m *ᵥ ·)`. -/
lemma chainProd_Dlay (p : ℕ) (Q : ℕ → Matrix S S A) (m : ℕ) :
    chainProd (Dlay p Q) m = (p : A) ^ (m + 1) • (prodQ Q 0 (m + 1)).mulVecLin := by
  induction m with
  | zero => simp [chainProd_zero, Dlay, prodQ]
  | succ m ih =>
    rw [chainProd_succ, ih, prodQ_zero_succ Q (m + 1), Matrix.mulVecLin_mul, Dlay,
      smul_mul_smul_comm, Module.End.mul_eq_comp]
    congr 1; ring

/-! ### Ranges -/

lemma range_map_of_comm {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (f : M ≃ₗ[A] M') (T : Module.End A M) (T' : Module.End A M')
    (h : f.toLinearMap ∘ₗ T = T' ∘ₗ f.toLinearMap) (c : A) :
    (LinearMap.range (c • T)).map f.toLinearMap = LinearMap.range (c • T') := by
  rw [← LinearMap.range_comp, LinearMap.comp_smul, h, ← LinearMap.smul_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 f.surjective)]

lemma range_unit_smul {M : Type*} [AddCommGroup M] [Module A M] (u : Aˣ) (T : Module.End A M) :
    LinearMap.range ((u : A) • T) = LinearMap.range T := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(u : A) • x, by simp⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨(↑u⁻¹ : A) • x, ?_⟩
    simp [smul_smul]

/-! ### Theorem (L1) -/

/-- The core of **(L1)** with `d = n + 1` (Part L of `CSI9_last_level_and_floors.md`), over any
commutative ring in which `1, …, n` are units. -/
theorem L1_core (p n : ℕ) (hu : ∀ k : ℕ, 1 ≤ k → k ≤ n → IsUnit (k : A))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (fun _ : Fin (n + 1) => A) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta A n)) Q)) ≃ₗ[A]
      ((Fin n → (S → A) ⧸ c • (⊤ : Submodule A (S → A))) ×
        ((S → A) ⧸ LinearMap.range (c • (p : A) ^ (n + 1) • (prodQ Q 0 (n + 1)).mulVecLin)))) := by
  have hfu : ∀ k : ℕ, k < n + 1 → IsUnit ((k.factorial : ℕ) : A) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact (hu (k + 1) (by omega) (by omega)).mul (ih (by omega))
  -- step 1
  have e1 := Submodule.Quotient.equiv _ _ (layerL A S (n + 1))
    (range_map_of_comm (layerL A S (n + 1)) _ _ (layerL_comp_Gp p n Q) c)
  -- step 2
  have hcomm : (diagL (n + 1) hfu).toLinearMap ∘ₗ chainOp (n + 1) (Dlay p Q) 0 =
      Gch p (n + 1) Q ∘ₗ (diagL (n + 1) hfu).toLinearMap := (Gch_comp_diag p (n + 1) Q hfu).symm
  have e2 := Submodule.Quotient.equiv _ _ (diagL (n + 1) hfu)
    (range_map_of_comm (diagL (n + 1) hfu) _ _ hcomm c)
  -- step 3
  have e3 := chainCokerEquiv (n + 1) (Nat.succ_pos n) (Dlay p Q) 0 c
  have hR : LinearMap.range (c • (0 + (-1 : A) ^ (n + 1 - 1) • chainProd (Dlay p Q) (n + 1 - 1))) =
      LinearMap.range (c • (p : A) ^ (n + 1) • (prodQ Q 0 (n + 1)).mulVecLin) := by
    rw [Nat.add_sub_cancel, zero_add, chainProd_Dlay, smul_comm c]
    simpa using range_unit_smul ((-1 : Aˣ) ^ n) (c • (p : A) ^ (n + 1) • (prodQ Q 0 (n + 1)).mulVecLin)
  exact ⟨(e1.trans (e2.symm.trans e3)).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl A _) (Submodule.quotEquivOfEq _ _ hR))⟩

/-- **(L1) Theorem, general form** (Part L, Proposition 2.3, of `CSI9_last_level_and_floors.md`;
more general than the file: any commutative ring `A` in which `1, …, d − 1` are units, and any
`p : ℕ`). For `1 ≤ d`, every `Q` and every `c`:
`Sys Δ(d−1) S ⧸ range (c • Gp p fl F Q) ≃
  (Fin (d−1) → (S → A) ⧸ c • ⊤) × ((S → A) ⧸ range (c • p^d • Mlast))`,
with `Δ(d−1) = delta A (d−1)`, `F = famF Δ(d−1)` (its `Fd 1`), `fl e_s = s`, and
`Mlast = Q 0 ⋯ Q (d−1) = prodQ Q 0 d` acting on coefficient vectors by `Matrix.mulVecLin` (see the
convention in the module docstring). -/
theorem L1_general (p d : ℕ) (hd : 1 ≤ d) (hu : ∀ k : ℕ, 1 ≤ k → k < d → IsUnit (k : A))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => A) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta A (d - 1))) Q)) ≃ₗ[A]
      ((Fin (d - 1) → (S → A) ⧸ c • (⊤ : Submodule A (S → A))) ×
        ((S → A) ⧸ LinearMap.range (c • (p : A) ^ d • (prodQ Q 0 d).mulVecLin)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact L1_core p n (fun k h1 h2 => hu k h1 (by omega)) Q c

/-- **(L1) Theorem** (Part L, Proposition 2.3, of `CSI9_last_level_and_floors.md`): for `p` prime
(oddness is not needed), `1 ≤ d ≤ p − 1`, every `Q : ℕ → Matrix S S ℤ_[p]` and every
`c : ℤ_[p]`:
`Sys Δ(d−1) S ⧸ range (c • Gp p fl F Q) ≃ₗ[ℤ_[p]]
  (Fin (d−1) → (S → ℤ_[p]) ⧸ c • ⊤) × ((S → ℤ_[p]) ⧸ range (c • p^d • Mlast))`,
with `Mlast = Q 0 * Q 1 * ⋯ * Q (d−1)` (`prodQ Q 0 d`) acting on coefficient vectors
(`Matrix.mulVecLin`, i.e. the row vector of generators multiplied on the right by `Mlast`). -/
theorem L1 (p : ℕ) [Fact p.Prime] (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1)
    (Q : ℕ → Matrix S S ℤ_[p]) (c : ℤ_[p]) :
    Nonempty ((Payment.Sys (fun _ : Fin (d - 1 + 1) => ℤ_[p]) S ⧸
        LinearMap.range (c • Gp p Fin.val (famF (DPLattice.delta ℤ_[p] (d - 1))) Q)) ≃ₗ[ℤ_[p]]
      ((Fin (d - 1) → (S → ℤ_[p]) ⧸ c • (⊤ : Submodule ℤ_[p] (S → ℤ_[p]))) ×
        ((S → ℤ_[p]) ⧸ LinearMap.range (c • (p : ℤ_[p]) ^ d • (prodQ Q 0 d).mulVecLin)))) :=
  L1_general p d hd1 (fun k h1 h2 => isUnit_natCast_of_not_dvd p fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)) Q c

end ColouredSand.OddTwist
