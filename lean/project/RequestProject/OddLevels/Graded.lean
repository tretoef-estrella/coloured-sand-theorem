module

public import RequestProject.OddLevels.Floors
public import RequestProject.OddSplitMove.Basic

/-!
# `CSI9_last_level_and_floors.md`, Part G (G2) and (G3) — the dance lattice as a moved graded family

Namespace `ColouredSand.OddTwist`. Reuses CSI7's twist `flT`, `embT`, `FT`
(`RequestProject/OddPayment/`), CSI8's split `flS`, `embS`, `FS` (`RequestProject/OddSplitMove/`),
CSI1's (B1) single operators of `twist` (`F1_lt`, `F1_last`), CSI3's `psiF` formulas
(`psiF_A_lt`, `psiF_A_last`, `psiF_C_lt`, `psiF_C_last`, `psi_Fd1`) and CSI6's `danceL`.

## Encoding

* A DP-lattice `M` is read as the graded family `(M.ι, fl, N i = A, famF M)` (Basic.lean), where
  `famF M` is `Fd 1` transported to `⨁ _ : M.ι, A` by the standard finite identification `dsE`.
* **Index orders.** CSI1/CSI3 index `Fin p × N.ι` and `Bool × Fin p × N.ι`, CSI7/CSI8 index
  `ι × Fin p` and `ι × Bool × Fin p`. The reindexing equivalences are
  `Equiv.prodComm N.ι (Fin p)` (`(i, j) ↦ (j, i)`) and `splitEqv p N.ι` (`(i, b, j) ↦ (b, j, i)`),
  composed with CSI6's identification of index types `idxTw`, `idxPsi` (Floors.lean):
  `eTw p l h hd : (danceL p b).ι × Fin p ≃ (danceL p l).ι` and
  `ePsi p l h hd : (danceL p b).ι × Bool × Fin p ≃ (danceL p l).ι`.
* "Equality of linear maps after the reindexing" is `opDS e (M.Fd 1) = FT p (famF N)` resp.
  `= FS p d₀ _ (famF N)`, where `opDS e T` is `T` transported along `e` and `dsE`
  (Basic.lean).
* **(G3)** is `G3_operator`, the general statement `Gp_Q0_eq` of Basic.lean for
  `T = Fd 1` of `danceL p λ` and `fl = flL p λ`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DirectSum DPLattice

section general

variable {A : Type*} [CommRing A]

lemma dsE_embT {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ℕ) (j0 : Fin p)
    (y : ⨁ _ : κ, A) :
    dsE A (κ × Fin p) (embT A (fun _ : κ => A) p j0 y) =
      fun q => if q.2 = j0 then dsE A κ y q.1 else 0 := by
  induction y using DirectSum.induction_on with
  | zero => funext q; simp
  | of i a =>
    rw [← DirectSum.lof_eq_of A]
    simp only [embT, DirectSum.toModule_lof]
    rw [dsE_lof, dsE_lof]
    funext q
    by_cases h1 : q.1 = i <;> by_cases h2 : q.2 = j0 <;>
      simp [Pi.single_apply, Prod.ext_iff, h1, h2]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    funext q
    split_ifs <;> simp_all

lemma dsE_embS {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ℕ) (b0 : Bool) (j0 : Fin p)
    (y : ⨁ _ : κ, A) :
    dsE A (κ × Bool × Fin p) (embS A (fun _ : κ => A) p b0 j0 y) =
      fun q => if q.2.1 = b0 ∧ q.2.2 = j0 then dsE A κ y q.1 else 0 := by
  induction y using DirectSum.induction_on with
  | zero => funext q; simp
  | of i a =>
    rw [← DirectSum.lof_eq_of A]
    simp only [embS, DirectSum.toModule_lof]
    rw [dsE_lof, dsE_lof]
    funext q
    by_cases h1 : q.1 = i <;> by_cases h2 : q.2.1 = b0 <;> by_cases h3 : q.2.2 = j0 <;>
      simp [Pi.single_apply, Prod.ext_iff, h1, h2, h3]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    funext q
    by_cases hq : q.2.1 = b0 ∧ q.2.2 = j0
    · simp only [Pi.add_apply, if_pos hq, map_add]
    · simp only [Pi.add_apply, if_neg hq, add_zero]

end general

variable (p : ℕ)

/-- The reindexing `κ × Bool × Fin p ≃ Bool × Fin p × κ`, `(i, b, j) ↦ (b, j, i)`, between CSI8's
and CSI3's index orders (Part G (G2) of `CSI9_last_level_and_floors.md`). -/
def splitEqv (κ : Type*) : κ × Bool × Fin p ≃ Bool × Fin p × κ :=
  (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)

@[simp] lemma splitEqv_symm_apply (κ : Type*) (x : Bool × Fin p × κ) :
    (splitEqv p κ).symm x = (x.2.2, x.1, x.2.1) := rfl

@[simp] lemma splitEqv_apply (κ : Type*) (q : κ × Bool × Fin p) :
    splitEqv p κ q = (q.2.1, q.2.2, q.1) := rfl

variable [Fact p.Prime]

/-- **The twist as a moved graded family** (Part G (G2) of `CSI9_last_level_and_floors.md`, for an
arbitrary DP-lattice `N` over `ℤ_[p]`): after the reindexing `(i, j) ↦ (j, i)`, the operator
`Fd 1` of CSI1's `twist p N` (its (B1)) is CSI7's twist operator `FT p` of the graded family of
`N`. -/
theorem opDS_twist (N : DPLattice ℤ_[p]) :
    opDS (Equiv.prodComm N.ι (Fin p)) ((twist p N).Fd 1) = FT p (famF N) := by
  refine DirectSum.linearMap_ext _ fun q => LinearMap.ext_ring ?_
  obtain ⟨i, j⟩ := q
  apply (dsE ℤ_[p] _).injective
  simp only [LinearMap.comp_apply]
  rw [dsE_opDS, dsE_lof]
  have hs : (Pi.single (i, j) (1 : ℤ_[p]) : N.ι × Fin p → ℤ_[p]) ∘
      (Equiv.prodComm N.ι (Fin p)).symm = Pi.single (j, i) 1 := by
    funext ⟨j', i'⟩
    by_cases h1 : j' = j <;> by_cases h2 : i' = i <;> simp [Pi.single_apply, h1, h2]
  rw [hs, single_eq_bv]
  simp only [FT]
  erw [DirectSum.toModule_lof]
  by_cases hj : j.val + 1 < p
  · rw [dif_pos hj]
    change twFd p N 1 (bv p j (Pi.single i 1)) ∘ _ = _
    rw [F1_lt p N hj]
    erw [dsE_lof]
    funext ⟨i', j'⟩
    by_cases h1 : i' = i <;> by_cases h2 : (j' : ℕ) = j + 1 <;>
      simp [bv_apply, Pi.single_apply, Prod.ext_iff, Fin.ext_iff, h1, h2]
  · rw [dif_neg hj]
    have hj' : (j : ℕ) = p - 1 := by omega
    change twFd p N 1 (bv p j (Pi.single i 1)) ∘ _ = _
    rw [hj', F1_last p N]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    erw [dsE_embT, dsE_famF, dsE_lof]
    funext ⟨i', j'⟩
    simp only [Function.comp_apply, Pi.smul_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      bv_apply, smul_eq_mul]
    by_cases h2 : (j' : ℕ) = 0
    · rw [if_pos h2, if_pos (Fin.ext h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (congrArg Fin.val h))]

/-- **The split as a moved graded family** (Part G (G2) of `CSI9_last_level_and_floors.md`, for an
arbitrary DP-lattice `N` over `ℤ_[p]` and `1 ≤ r ≤ p − 1`): after the reindexing
`(i, b, j) ↦ (b, j, i)`, the operator `Fd 1` of CSI3's `psi p N r` (its `psiF`) is CSI8's split
operator `FS p r` of the graded family of `N`. -/
theorem opDS_psi (N : DPLattice ℤ_[p]) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    opDS (splitEqv p N.ι) ((psi p N r hr1 hr2).Fd 1) = FS p r hr1 (famF N) := by
  rw [psi_Fd1]
  refine DirectSum.linearMap_ext _ fun q => LinearMap.ext_ring ?_
  obtain ⟨i, c, j⟩ := q
  apply (dsE ℤ_[p] _).injective
  simp only [LinearMap.comp_apply]
  rw [dsE_opDS, dsE_lof]
  have hs : (Pi.single (i, c, j) (1 : ℤ_[p]) : N.ι × Bool × Fin p → ℤ_[p]) ∘
      (splitEqv p N.ι).symm = Pi.single (c, j, i) 1 := by
    funext ⟨c', j', i'⟩
    by_cases h1 : c' = c <;> by_cases h2 : j' = j <;> by_cases h3 : i' = i <;>
      simp [Pi.single_apply, h1, h2, h3]
  rw [hs]
  simp only [FS]
  erw [DirectSum.toModule_lof]
  have hp := two_le_p' (p := p)
  cases c
  · rw [single_false]
    by_cases hj : j.val + 1 < p
    · rw [dif_pos hj, psiF_A_lt r hj]
      erw [dsE_lof]
      funext ⟨i', c', j'⟩
      by_cases h1 : i' = i <;> by_cases h2 : (j' : ℕ) = j + 1 <;> cases c' <;>
        simp [aV_apply, Pi.single_apply, Prod.ext_iff, Fin.ext_iff, h1, h2]
    · rw [dif_neg hj]
      have hj' : (j : ℕ) = p - 1 := by omega
      rw [hj', psiF_A_last]
      simp only [cond_false, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        map_add, map_smul]
      erw [dsE_embS, dsE_famF, dsE_lof, dsE_lof]
      funext ⟨i', c', j'⟩
      simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, splitEqv_apply, aV_apply,
        cV_apply, smul_eq_mul]
      cases c'
      · by_cases h2 : (j' : ℕ) = 0
        · rw [if_pos (show false = false ∧ (j' : ℕ) = 0 from ⟨rfl, h2⟩),
            if_pos (show false = false ∧ j' = ⟨0, by omega⟩ from ⟨rfl, Fin.ext h2⟩)]
          simp
        · rw [if_neg (show ¬ (false = false ∧ (j' : ℕ) = 0) from fun h => h2 h.2),
            if_neg (show ¬ (false = false ∧ j' = ⟨0, by omega⟩) from
              fun h => h2 (congrArg Fin.val h.2))]
          simp
      · have e1 : (Pi.single (i, true, (⟨p - r, by omega⟩ : Fin p)) (1 : ℤ_[p]) :
            N.ι × Bool × Fin p → ℤ_[p]) (i', true, j') =
            if (j' : ℕ) = p - r then (Pi.single i (1 : ℤ_[p]) : N.ι → ℤ_[p]) i' else 0 := by
          by_cases h3 : (j' : ℕ) = p - r
          · rw [if_pos h3]
            have : j' = ⟨p - r, by omega⟩ := Fin.ext h3
            rw [this]
            by_cases h1 : i' = i
            · subst h1; simp
            · rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne]
              intro h; exact h1 (congrArg Prod.fst h)
          · rw [if_neg h3, Pi.single_eq_of_ne]
            intro h; apply h3; rw [show j' = _ from congrArg (fun x => x.2.2) h]
        rw [e1]
        simp
  · rw [single_true]
    by_cases hj : j.val + 1 < p
    · rw [dif_pos hj, psiF_C_lt r hj]
      erw [dsE_lof]
      funext ⟨i', c', j'⟩
      by_cases h1 : i' = i <;> by_cases h2 : (j' : ℕ) = j + 1 <;> cases c' <;>
        simp [cV_apply, Pi.single_apply, Prod.ext_iff, Fin.ext_iff, h1, h2]
    · rw [dif_neg hj]
      have hj' : (j : ℕ) = p - 1 := by omega
      rw [hj', psiF_C_last]
      simp only [cond_true, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
      erw [dsE_embS, dsE_famF, dsE_lof]
      funext ⟨i', c', j'⟩
      simp only [Function.comp_apply, Pi.smul_apply, splitEqv_apply, cV_apply, smul_eq_mul]
      cases c'
      · simp
      · by_cases h2 : (j' : ℕ) = 0
        · rw [if_pos (show true = true ∧ (j' : ℕ) = 0 from ⟨rfl, h2⟩),
            if_pos (show true = true ∧ j' = ⟨0, by omega⟩ from ⟨rfl, Fin.ext h2⟩)]
        · rw [if_neg (show ¬ (true = true ∧ (j' : ℕ) = 0) from fun h => h2 h.2),
            if_neg (show ¬ (true = true ∧ j' = ⟨0, by omega⟩) from
              fun h => h2 (congrArg Fin.val h.2))]

lemma opDS_cast_twist {M N : DPLattice ℤ_[p]} (h : M = twist p N) :
    opDS ((Equiv.prodComm N.ι (Fin p)).trans (Equiv.cast (congrArg DPLattice.ι h)).symm)
      (M.Fd 1) = FT p (famF N) := by
  subst h
  exact opDS_twist p N

lemma opDS_cast_psi {M N : DPLattice ℤ_[p]} {r : ℕ} {hr1 : 1 ≤ r} {hr2 : r ≤ p - 1}
    (h : M = psi p N r hr1 hr2) :
    opDS ((splitEqv p N.ι).trans (Equiv.cast (congrArg DPLattice.ι h)).symm) (M.Fd 1) =
      FS p r hr1 (famF N) := by
  subst h
  exact opDS_psi p N r hr1 hr2

/-! ### (G2) for `danceL` -/

/-- The reindexing of (G2), case `d₀ = 0` (Part G (G2) of `CSI9_last_level_and_floors.md`):
`(danceL p b).ι × Fin p ≃ (danceL p λ).ι`, `(i, j) ↦ (j, i)` followed by CSI6's identification. -/
def eTw (l : ℕ) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) :
    (danceL p ((l + 1) / p - 1)).ι × Fin p ≃ (danceL p l).ι :=
  (Equiv.prodComm _ _).trans (idxTw p l h hd).symm

/-- The reindexing of (G2), case `d₀ ≥ 1` (Part G (G2) of `CSI9_last_level_and_floors.md`):
`(danceL p b).ι × Bool × Fin p ≃ (danceL p λ).ι`, `(i, b, j) ↦ (b, j, i)` followed by CSI6's
identification. -/
def ePsi (l : ℕ) (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) :
    (danceL p ((l + 1) / p - 1)).ι × Bool × Fin p ≃ (danceL p l).ι :=
  (splitEqv p _).trans (idxPsi p l h hd).symm

/-- **(G2), twist** (Part G of `CSI9_last_level_and_floors.md`): for `λ ≥ p − 1` with `d₀ = 0`
and `b = (λ+1)/p − 1`, the pair `(flL, Fd 1)` of `danceL p λ` is, after the reindexing `eTw`, the
twist (CSI7 Part T) of the pair `(flL, Fd 1)` of `danceL p b`:
`flL p λ ∘ eTw = flT p (flL p b)` and `opDS eTw (Fd 1) = FT p (famF (danceL p b))`. -/
theorem G2_twist (l : ℕ) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) :
    (∀ q, flL p l (eTw p l h hd q) = flT p (flL p ((l + 1) / p - 1)) q) ∧
    opDS (eTw p l h hd) ((danceL p l).Fd 1) = FT p (famF (danceL p ((l + 1) / p - 1))) :=
  ⟨fun q => G1_twist p l h hd q.2 q.1, opDS_cast_twist p (danceL_d0_zero p h hd)⟩

/-- **(G2), split** (Part G of `CSI9_last_level_and_floors.md`): for `λ ≥ p − 1` with
`1 ≤ d₀ = (λ+1) % p` and `b = (λ+1)/p − 1`, the pair `(flL, Fd 1)` of `danceL p λ` is, after the
reindexing `ePsi`, the split with `r = d₀` (CSI8 Part S) of the pair `(flL, Fd 1)` of
`danceL p b`: `flL p λ ∘ ePsi = flS p d₀ (flL p b)` and
`opDS ePsi (Fd 1) = FS p d₀ _ (famF (danceL p b))`. -/
theorem G2_psi (l : ℕ) (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) :
    (∀ q, flL p l (ePsi p l h hd q) = flS p ((l + 1) % p) (flL p ((l + 1) / p - 1)) q) ∧
    opDS (ePsi p l h hd) ((danceL p l).Fd 1) =
      FS p ((l + 1) % p) hd (famF (danceL p ((l + 1) / p - 1))) := by
  refine ⟨fun q => ?_, opDS_cast_psi p (danceL_d0_pos p h hd (mod_le_pred p l))⟩
  obtain ⟨i, c, j⟩ := q
  have := G1_psi p l h hd j i
  cases c
  · simpa [flS, ePsi] using this.1
  · simpa [flS, ePsi, add_assoc] using this.2

/-! ### (G3) for `danceL` -/

/-- **(G3) The operator** (Part G of `CSI9_last_level_and_floors.md`): for `e ≥ 1` and `i : ℕ`, on
`danceL p λ` the operator `σ = Fd 1 + p^e • (D_fl + i)` (with `D_fl x = flL · x` coordinatewise)
is the one-slot system `Gp p flL (Fd 1) Q₀` with `Q₀ φ = p^{e−1} (φ + i)` (`1 × 1`), i.e.
`sysUnitE ∘ Gp p (flL p λ) (famF (danceL p λ)) Q₀ = σ ∘ sysUnitE`. -/
theorem G3_operator (l e i : ℕ) (he : 1 ≤ e) :
    (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap ∘ₗ
        Gp p (flL p l) (famF (danceL p l)) (Q0 ℤ_[p] p e i) =
      ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
          (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p])))) ∘ₗ
        (sysUnitE ℤ_[p] (danceL p l).ι).toLinearMap :=
  Gp_Q0_eq p e i he (flL p l) ((danceL p l).Fd 1)

end ColouredSand.OddTwist
