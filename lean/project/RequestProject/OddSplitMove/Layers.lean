module

public import RequestProject.OddSplitMove.Basic
public import RequestProject.OddSplitMove.Block
public import RequestProject.OddPayment.Layers

/-!
# The layers of the split and the `A`/`C` slots (*Proof* of (M1) of `CSI8_the_split_move.md`)

* `splitEquiv p : M_S^S ≃ (Fin p → M^S) × (Fin p → M^S)` (`M_S^S = Sys (NS p N) S`):
  `x at (s, (i, false, j)) ↦ x ι_{s,i}` in the `j`-th `A` layer (first factor) and
  `x at (s, (i, true, j)) ↦ x ι_{s,i}` in the `j`-th `C` layer (second factor).
* `layer_comp_GpS` (step 1 of the *Proof*): in the layers, the system of the split
  `Gp p (flS p r fl) (FS p r hr F) Q` is the coupled chain operator `coupledOp` of `Block.lean`, with
  CSI7's `layerD p fl Q` on the `A` chain, `layerD p fl (fun φ => Q (φ + r))` on the `C` chain,
  `E = −p • FSo F` on both, and the coupling `L = p • id` from `A_{p−1}` to `C_{p−r}`.
* `slotEquiv : Sys N (S × Bool) ≃ M^S × M^S`: `x ι_{(s, false), i} ↦ (x ι_{s,i}, 0)` (the `A`
  slots) and `x ι_{(s, true), i} ↦ (0, x ι_{s,i})` (the `C` slots).
* `slot_comp_Gp_blockS`: in these slots, `Gp p fl F (blockS a c k)` is the block operator
  `(u, v) ↦ (Gp p fl F a u, Gp p fl F c v + DSm (p • k) u)`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

section SplitLayers

variable (p : ℕ)

/-- Placing `y ∈ M^S` in the `j`-th `A` layer (`b = false`) or `C` layer (`b = true`) (*Proof*
of (M1) of `CSI8_the_split_move.md`). -/
def splitLay (b : Bool) (j : Fin p) :
    Payment.Sys N S →ₗ[A] (Fin p → Payment.Sys N S) × (Fin p → Payment.Sys N S) :=
  cond b (LinearMap.inr A _ _ ∘ₗ LinearMap.single A (fun _ => Payment.Sys N S) j)
    (LinearMap.inl A _ _ ∘ₗ LinearMap.single A (fun _ => Payment.Sys N S) j)

omit [DecidableEq ι] [DecidableEq S] [Fintype S] in
@[simp] lemma splitLay_false (j : Fin p) (y : Payment.Sys N S) :
    splitLay (A := A) p false j y = (Pi.single j y, 0) := rfl

omit [DecidableEq ι] [DecidableEq S] [Fintype S] in
@[simp] lemma splitLay_true (j : Fin p) (y : Payment.Sys N S) :
    splitLay (A := A) p true j y = (0, Pi.single j y) := rfl

/-- The decomposition into the `A` and `C` layers (*Proof* of (M1) of
`CSI8_the_split_move.md`). -/
def splitProj :
    Payment.Sys (NS p N) S →ₗ[A] (Fin p → Payment.Sys N S) × (Fin p → Payment.Sys N S) :=
  DirectSum.toModule A (S × (ι × Bool × Fin p)) _ (fun q =>
    splitLay p q.2.2.1 q.2.2.2 ∘ₗ oslot A N S q.1 q.2.1)

/-- `x ι_{s,i} ↦ x at (s, (i, b, j))` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
def embLS (b : Bool) (j : Fin p) : Payment.Sys N S →ₗ[A] Payment.Sys (NS p N) S :=
  DirectSum.toModule A (S × ι) _ (fun q => oslot A (NS p N) S q.1 (q.2, b, j))

omit [Fintype S] in
@[simp] lemma splitProj_oslot (s : S) (q : ι × Bool × Fin p) (x : N q.1) :
    splitProj (A := A) p (oslot A (NS p N) S s q x) = splitLay (A := A) p q.2.1 q.2.2 (oslot A N S s q.1 x) := by
  simp [splitProj, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
@[simp] lemma embLS_oslot (b : Bool) (j : Fin p) (s : S) (i : ι) (x : N i) :
    embLS (A := A) p b j (oslot A N S s i x) = oslot A (NS p N) S s (i, b, j) x := by
  simp [embLS, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
lemma lsum_embLS_single (b : Bool) (j : Fin p) (y : Payment.Sys N S) :
    LinearMap.lsum A (fun _ => Payment.Sys N S) A (embLS (A := A) p b) (Pi.single j y) =
      embLS (A := A) p b j y := by
  simp [Pi.single_apply, apply_ite]

/-- The inverse of `splitProj` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
def splitInv :
    (Fin p → Payment.Sys N S) × (Fin p → Payment.Sys N S) →ₗ[A] Payment.Sys (NS p N) S :=
  (LinearMap.lsum A (fun _ => Payment.Sys N S) A (embLS p false)).coprod
    (LinearMap.lsum A (fun _ => Payment.Sys N S) A (embLS p true))

omit [Fintype S] in
lemma splitInv_splitLay (b : Bool) (j : Fin p) (y : Payment.Sys N S) :
    splitInv (A := A) p (splitLay (A := A) p b j y) = embLS (A := A) p b j y := by
  cases b <;> simp [splitInv, Pi.single_apply, apply_ite]

omit [Fintype S] in
lemma splitProj_splitInv_splitLay (b : Bool) (j : Fin p) (s : S) (i : ι) (x : N i) :
    splitProj (A := A) p (splitInv (A := A) p (splitLay (A := A) p b j (oslot A N S s i x))) =
      splitLay (A := A) p b j (oslot A N S s i x) := by
  rw [splitInv_splitLay, embLS_oslot]
  exact splitProj_oslot (A := A) p s (i, b, j) x

/-- `M_S^S ≃ (Fin p → M^S) × (Fin p → M^S)`: the decomposition into the layers
`A_0, …, A_{p−1}` and `C_0, …, C_{p−1}` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
noncomputable def splitEquiv :
    Payment.Sys (NS p N) S ≃ₗ[A] (Fin p → Payment.Sys N S) × (Fin p → Payment.Sys N S) :=
  LinearEquiv.ofLinear (splitProj p) (splitInv p)
    (by
      apply LinearMap.prod_ext
      · refine LinearMap.pi_ext' fun j => ?_
        apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        exact splitProj_splitInv_splitLay p false j s i x
      · refine LinearMap.pi_ext' fun j => ?_
        apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        exact splitProj_splitInv_splitLay p true j s i x)
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨s, q⟩
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp]
      erw [splitProj_oslot]
      rw [splitInv_splitLay, embLS_oslot]
      rfl)

omit [Fintype S] in
lemma splitEquiv_toLinearMap :
    (splitEquiv (A := A) (N := N) (S := S) p :
      Payment.Sys (NS p N) S →ₗ[A] (Fin p → Payment.Sys N S) × (Fin p → Payment.Sys N S)) =
      splitProj p := rfl

omit [Fintype S] in
/-- `(b_j m) ι_s` in the layers (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma splitProj_oslotE_embS (s : S) (b : Bool) (j : Fin p) (m : ⨁ i, N i) :
    splitProj (A := A) p (oslotE A (NS p N) S s (embS A N p b j m)) =
      splitLay (A := A) p b j (oslotE A N S s m) := by
  have : (splitProj (A := A) p ∘ₗ oslotE A (NS p N) S s ∘ₗ embS A N p b j :
      (⨁ i, N i) →ₗ[A] _) = splitLay (A := A) p b j ∘ₗ oslotE A N S s := by
    apply DirectSum.linearMap_ext
    intro i
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embS, DirectSum.toModule_lof, oslotE_lof]
    exact splitProj_oslot (A := A) p s (i, b, j) x
  simpa using LinearMap.congr_fun this m

variable (r : ℕ) (hr : 0 < r)

/-- `FS (x at (i, b, j)) = x at (i, b, j+1)` for `j + 1 < p` (*Part S* of
`CSI8_the_split_move.md`). -/
lemma FS_lof_lt (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (b : Bool) (j : Fin p)
    (h : j.val + 1 < p) (x : N i) :
    FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, j) x) =
      DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, ⟨j.val + 1, h⟩) x := by
  simp [FS, DirectSum.toModule_lof, h]

/-- `FS (A_{p−1} x) = −p • A_0 (F x) + p • C_{p−r} x` (*Part S* of `CSI8_the_split_move.md`). -/
lemma FS_lof_lastA (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p)
    (h : ¬ j.val + 1 < p) (x : N i) :
    FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, false, j) x) =
      -(p : A) • embS A N p false ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x)) +
        (p : A) • DirectSum.lof A (ι × Bool × Fin p) (NS p N)
          (i, true, ⟨p - r, Nat.sub_lt j.pos hr⟩) x := by
  simp [FS, DirectSum.toModule_lof, h]

/-- `FS (C_{p−1} x) = −p • C_0 (F x)` (*Part S* of `CSI8_the_split_move.md`). -/
lemma FS_lof_lastC (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p)
    (h : ¬ j.val + 1 < p) (x : N i) :
    FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, true, j) x) =
      -(p : A) • embS A N p true ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x)) := by
  simp [FS, DirectSum.toModule_lof, h]

/-- **Step 1 of the *Proof* of (M1)** of `CSI8_the_split_move.md`: in the layers, the system of
the split `Gp p (flS p r fl) (FS p r hr F) Q` is the coupled chain operator, with CSI7's
`layerD p fl Q` on the `A` chain, `layerD p fl (fun φ => Q (φ + r))` on the `C` chain,
`E = −p • FSo F` on both chains and the coupling `p • id` from `A_{p−1}` to `C_{p−r}`. -/
lemma layer_comp_GpS (hrp : r < p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) :
    splitProj (A := A) (N := N) (S := S) p ∘ₗ Gp p (flS p r fl) (FS p r hr F) Q =
      coupledOp p (p - r) (by omega) (layerD p fl Q) (layerD p fl (fun φ => Q (φ + r)))
        (-(p : A) • FSo F) (-(p : A) • FSo F) ((p : A) • LinearMap.id) ∘ₗ splitProj p := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i, b, j⟩
  refine LinearMap.ext fun x => ?_
  change splitProj p (Gp p (flS p r fl) (FS p r hr F) Q (oslot A (NS p N) S s' (i, b, j) x)) =
    coupledOp p (p - r) (by omega) (layerD p fl Q) (layerD p fl (fun φ => Q (φ + r)))
        (-(p : A) • FSo F) (-(p : A) • FSo F) ((p : A) • LinearMap.id)
      (splitProj p (oslot A (NS p N) S s' (i, b, j) x))
  have hsum : splitProj (A := A) p (∑ s, ((p : A) * Q (flS p r fl (i, b, j)) s s') •
      oslot A (NS p N) S s (i, b, j) x) =
      splitLay (A := A) p b j (cond b (layerD p fl (fun φ => Q (φ + r))) (layerD p fl Q) j.val
        (oslot A N S s' i x)) := by
    have e : ∀ s, ((p : A) * Q (flS p r fl (i, b, j)) s s') =
        ((fun i => (p : A) • cond b (Q (p * fl i + j.val + r)) (Q (p * fl i + j.val))) i s s') := by
      intro s; cases b <;> simp [flS, add_right_comm]
    simp only [e]
    cases b <;> simp [layerD, map_sum, map_smul]
  rw [Gp_oslot, map_add, hsum, splitProj_oslot, coupledOp_apply]
  dsimp only
  by_cases hj : j.val + 1 < p
  · rw [FS_lof_lt p r hr F i b j hj, oslotE_lof, splitProj_oslot]
    have hne : (⟨p - 1, by omega⟩ : Fin p) ≠ j := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    cases b
    · simp only [splitLay_false, cond_false]
      rw [chainOp_single_lt _ _ _ _ hj, Pi.single_eq_of_ne hne]
      simp
    · simp only [splitLay_true, cond_true]
      rw [chainOp_single_lt _ _ _ _ hj]
      simp
  · cases b
    · rw [FS_lof_lastA p r hr F i j hj]
      simp only [map_add, map_smul]
      rw [splitProj_oslotE_embS, oslotE_lof, splitProj_oslot]
      have hl : (⟨p - 1, by omega⟩ : Fin p) = j := Fin.ext (by simp; omega)
      simp only [splitLay_false, splitLay_true, cond_false]
      rw [chainOp_single_last _ _ _ _ hj, hl]
      simp only [Pi.single_eq_same, map_zero, zero_add, LinearMap.smul_apply, FSo_oslot,
        LinearMap.id_apply, Prod.smul_mk, smul_zero, neg_smul, Pi.single_neg, Pi.single_smul]
      refine Prod.ext ?_ ?_ <;> simp
    · rw [FS_lof_lastC p r hr F i j hj]
      simp only [map_smul]
      rw [splitProj_oslotE_embS]
      simp only [splitLay_true, cond_true]
      rw [chainOp_single_last _ _ _ _ hj]
      simp only [map_zero, Pi.zero_apply, smul_zero, LinearMap.smul_apply, FSo_oslot,
        Prod.smul_mk, neg_smul, Pi.single_neg, Pi.single_smul]
      refine Prod.ext ?_ ?_ <;> simp

end SplitLayers

section Slots

/-- The `A` slots (`b = false`) and `C` slots (`b = true`) of `S × Bool`:
`x ι_{(s, b), i} ↦ x ι_{s,i}` in the first, resp. second, factor (*Part S* of
`CSI8_the_split_move.md`: block order, all `A` slots then all `C` slots). -/
def slotProj : Payment.Sys N (S × Bool) →ₗ[A] Payment.Sys N S × Payment.Sys N S :=
  DirectSum.toModule A ((S × Bool) × ι) _ (fun q =>
    cond q.1.2 (LinearMap.inr A _ _ ∘ₗ oslot A N S q.1.1 q.2)
      (LinearMap.inl A _ _ ∘ₗ oslot A N S q.1.1 q.2))

/-- `x ι_{s,i} ↦ x ι_{(s, b), i}` (*Part S* of `CSI8_the_split_move.md`). -/
def embB (b : Bool) : Payment.Sys N S →ₗ[A] Payment.Sys N (S × Bool) :=
  DirectSum.toModule A (S × ι) _ (fun q => oslot A N (S × Bool) (q.1, b) q.2)

omit [Fintype S] in
@[simp] lemma slotProj_oslot_false (s : S) (i : ι) (x : N i) :
    slotProj (A := A) (oslot A N (S × Bool) (s, false) i x) = (oslot A N S s i x, 0) := by
  simp [slotProj, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
@[simp] lemma slotProj_oslot_true (s : S) (i : ι) (x : N i) :
    slotProj (A := A) (oslot A N (S × Bool) (s, true) i x) = (0, oslot A N S s i x) := by
  simp [slotProj, oslot_eq_lof, DirectSum.toModule_lof]

omit [Fintype S] in
@[simp] lemma embB_oslot (b : Bool) (s : S) (i : ι) (x : N i) :
    embB (A := A) b (oslot A N S s i x) = oslot A N (S × Bool) (s, b) i x := by
  simp [embB, oslot_eq_lof, DirectSum.toModule_lof]

/-- `Sys N (S × Bool) ≃ M^S × M^S` (`A` slots, `C` slots) (*Part S* of
`CSI8_the_split_move.md`). -/
noncomputable def slotEquiv : Payment.Sys N (S × Bool) ≃ₗ[A] Payment.Sys N S × Payment.Sys N S :=
  LinearEquiv.ofLinear slotProj ((embB false).coprod (embB true))
    (by
      apply LinearMap.prod_ext
      · apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        simp only [LinearMap.comp_apply, LinearMap.id_comp, LinearMap.coe_inl,
          LinearMap.coprod_apply, map_zero, add_zero]
        rw [← oslot_eq_lof, embB_oslot, slotProj_oslot_false]
      · apply DirectSum.linearMap_ext
        rintro ⟨s, i⟩
        refine LinearMap.ext fun x => ?_
        simp only [LinearMap.comp_apply, LinearMap.id_comp, LinearMap.coe_inr,
          LinearMap.coprod_apply, map_zero, zero_add]
        rw [← oslot_eq_lof, embB_oslot, slotProj_oslot_true])
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨⟨s, b⟩, i⟩
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_comp]
      rw [← oslot_eq_lof]
      cases b <;> simp)

omit [Fintype S] in
lemma slotEquiv_toLinearMap :
    (slotEquiv (A := A) (N := N) (S := S) :
      Payment.Sys N (S × Bool) →ₗ[A] Payment.Sys N S × Payment.Sys N S) = slotProj := rfl

omit [Fintype S] in
lemma slotProj_oslotE (s : S) (b : Bool) (m : ⨁ i, N i) :
    slotProj (A := A) (oslotE A N (S × Bool) (s, b) m) =
      cond b (0, oslotE A N S s m) (oslotE A N S s m, 0) := by
  have : (slotProj (A := A) ∘ₗ oslotE A N (S × Bool) (s, b) : (⨁ i, N i) →ₗ[A] _) =
      cond b (LinearMap.inr A _ _ ∘ₗ oslotE A N S s) (LinearMap.inl A _ _ ∘ₗ oslotE A N S s) := by
    apply DirectSum.linearMap_ext
    intro i
    refine LinearMap.ext fun x => ?_
    cases b <;> simp
  have h := LinearMap.congr_fun this m
  cases b <;> simpa using h

/-- The block operator `(u, v) ↦ (Gp a u, Gp c v + DSm (p • k) u)` on `M^S × M^S` (*Part M* of
`CSI8_the_split_move.md`: the system with data `[[a, 0], [k, c]]` read in the `A`/`C` slots). -/
def blockGp (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (a c k : ℕ → Matrix S S A) :
    Payment.Sys N S × Payment.Sys N S →ₗ[A] Payment.Sys N S × Payment.Sys N S :=
  (Gp p fl F a).prodMap (Gp p fl F c) +
    LinearMap.inr A _ _ ∘ₗ DSm (fun i => (p : A) • k (fl i)) ∘ₗ LinearMap.fst A _ _

/-- In the `A`/`C` slots, `Gp p fl F (blockS a c k)` is the block operator `blockGp` (*Part M*
of `CSI8_the_split_move.md`). -/
lemma slot_comp_Gp_blockS (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (a c k : ℕ → Matrix S S A) :
    slotProj (A := A) (N := N) (S := S) ∘ₗ Gp p fl F (blockS a c k) =
      blockGp p fl F a c k ∘ₗ slotProj := by
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s', b'⟩, i⟩
  refine LinearMap.ext fun x => ?_
  change slotProj (Gp p fl F (blockS a c k) (oslot A N (S × Bool) (s', b') i x)) =
    blockGp p fl F a c k (slotProj (oslot A N (S × Bool) (s', b') i x))
  rw [Gp_oslot, map_add, slotProj_oslotE, map_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, map_smul, slotProj_oslot_true, slotProj_oslot_false]
  cases b' <;>
    simp [blockGp, blockS, Gp_oslot, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, mul_comm]

end Slots

end ColouredSand.OddTwist
