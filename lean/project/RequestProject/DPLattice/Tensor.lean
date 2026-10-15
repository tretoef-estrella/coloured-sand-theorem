module

public import RequestProject.DPLattice.Basic

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: the trivial lattice and `V ⊗ M` (Part T)

Encodings:
* `one A` is the trivial lattice `𝟙`: `ι = Unit`, weight `0`, `F^{(0)} = E^{(0)} = 1` and
  `F^{(r)} = E^{(r)} = 0` for `r ≥ 1` (`oneFd r = if r = 0 then 1 else 0`).
* `tensorV M` is `V ⊗ M`: basis `Fin 2 × M.ι`, weight `wt (e, i) = wtV e + M.wt i` with
  `wtV 0 = 1`, `wtV 1 = −1`. For `m : M.ι → A`, `bvec e m` is the vector `b_e m` "with `m` in the
  slot `e`" (`(bvec e m) (e', i) = if e' = e then m i else 0`), and `slice e f = f (e, ·)` reads
  the slot `e`. The divided powers are given by the coproduct formulas of the file
  (`Fd_bvec0`, `Fd_bvec1`, `Ed_bvec0`, `Ed_bvec1`), where `pred F r` stands for `F^{(r−1)}` when
  `r ≥ 1` and for `0` when `r = 0`.
-/

@[expose] public section

noncomputable section

namespace DPLattice

open Finset

variable {A : Type*} [CommRing A]

/-! ### Binomial coefficients -/

lemma choose_natAdd (a b : ℕ) : Ring.choose ((a : ℤ) + b) a = ((a + b).choose a : ℤ) := by
  rw [← Ring.choose_natCast]; push_cast; rfl

lemma choose_zero_succ' (k : ℕ) : Ring.choose (0 : ℤ) (k + 1) = 0 := by
  simp

/-! ### The trivial lattice `𝟙` -/

/-- (T1) the divided powers of `𝟙`: `F^{(0)} = 1`, `F^{(r)} = 0` for `r ≥ 1`. -/
def oneFd (A : Type*) [CommRing A] : ℕ → Module.End A (Unit → A) :=
  fun r => if r = 0 then 1 else 0

lemma one_isDP : IsDP (A := A) (fun _ : Unit => (0 : ℤ)) (oneFd A) (oneFd A) where
  W_F i r j h := by
    have : r ≠ 0 := by rintro rfl; simp at h
    simp [oneFd, this]
  W_E i r j h := by
    have : r ≠ 0 := by rintro rfl; simp at h
    simp [oneFd, this]
  P0_F := by simp [oneFd]
  P0_E := by simp [oneFd]
  P1_F a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [oneFd, if_true, Ring.choose_zero_right, Int.cast_one, one_smul, zero_add]
      exact LinearMap.id_comp _
    · simp [oneFd, ha.ne']
  P1_E a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [oneFd, if_true, Ring.choose_zero_right, Int.cast_one, one_smul, zero_add]
      exact LinearMap.id_comp _
    · simp [oneFd, ha.ne']
  K i r s := by
    by_cases h : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := h; simp [oneFd]
    · have lhs : oneFd A s (oneFd A r (Pi.single i 1)) = 0 := by
        unfold oneFd; split_ifs <;> simp_all
      rw [lhs]; symm
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [mem_range] at hj
      by_cases hj' : r - j = 0 ∧ s - j = 0
      · have hrs : r = s := by omega
        subst hrs
        obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have : j = k + 1 := by omega
        subst this
        simp
      · unfold oneFd; split_ifs <;> simp_all

/-- (T1) the trivial lattice `𝟙`: `ι = Unit`, weight `0`, `F^{(r)} = E^{(r)} = 0` for `r ≥ 1`. -/
def one (A : Type*) [CommRing A] : DPLattice A where
  ι := Unit
  wt _ := 0
  Fd := oneFd A
  Ed := oneFd A
  isDP := one_isDP

/-! ### Slots -/

/-- (T1) The weight of `V`: `wt b_0 = 1`, `wt b_1 = −1`. -/
def wtV (e : Fin 2) : ℤ := if e = 0 then 1 else -1

@[simp] lemma wtV_zero : wtV 0 = 1 := rfl
@[simp] lemma wtV_one : wtV 1 = -1 := rfl

section slots

variable {ι : Type*}

/-- (T2) `b_e m`: the vector of `V ⊗ M` with `m` in the slot `e`. -/
def bvec (e : Fin 2) : (ι → A) →ₗ[A] (Fin 2 × ι → A) where
  toFun m p := if p.1 = e then m p.2 else 0
  map_add' m m' := by funext p; by_cases h : p.1 = e <;> simp [h]
  map_smul' c m := by funext p; by_cases h : p.1 = e <;> simp [h]

/-- (T2) The slot `e` of a vector of `V ⊗ M`. -/
def slice (e : Fin 2) : (Fin 2 × ι → A) →ₗ[A] (ι → A) where
  toFun f i := f (e, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma bvec_apply (e : Fin 2) (m : ι → A) (p : Fin 2 × ι) :
    bvec e m p = if p.1 = e then m p.2 else 0 := rfl

@[simp] lemma slice_apply (e : Fin 2) (f : Fin 2 × ι → A) (i : ι) : slice e f i = f (e, i) := rfl

@[simp] lemma slice_bvec_self (e : Fin 2) (m : ι → A) : slice e (bvec e m) = m := by
  funext i; simp

@[simp] lemma slice0_bvec1 (m : ι → A) : slice 0 (bvec 1 m) = 0 := by
  funext i; simp

@[simp] lemma slice1_bvec0 (m : ι → A) : slice 1 (bvec 0 m) = 0 := by
  funext i; simp

lemma ext_slice {f g : Fin 2 × ι → A} (h0 : slice 0 f = slice 0 g) (h1 : slice 1 f = slice 1 g) :
    f = g := by
  funext ⟨e, i⟩
  fin_cases e
  · exact congr_fun h0 i
  · exact congr_fun h1 i

lemma eq_bvec_slice (f : Fin 2 × ι → A) : f = bvec 0 (slice 0 f) + bvec 1 (slice 1 f) := by
  apply ext_slice <;> simp

lemma single_eq_bvec [DecidableEq ι] (e : Fin 2) (i : ι) :
    (Pi.single (e, i) (1 : A) : Fin 2 × ι → A) = bvec e (Pi.single i 1) := by
  funext ⟨e', j⟩
  by_cases he : e' = e <;> by_cases hj : j = i <;> simp [Pi.single_apply, he, hj]

/-- (T2) `pred F r` is `F^{(r−1)}` for `r ≥ 1` and `0` for `r = 0`. -/
def pred (F : ℕ → Module.End A (ι → A)) (r : ℕ) : Module.End A (ι → A) :=
  if r = 0 then 0 else F (r - 1)

@[simp] lemma pred_zero (F : ℕ → Module.End A (ι → A)) : pred F 0 = 0 := rfl
@[simp] lemma pred_succ (F : ℕ → Module.End A (ι → A)) (r : ℕ) : pred F (r + 1) = F r := rfl

/-- (T2) the coproduct of `F^{(r)}` on `V ⊗ M`. -/
def tensorFd (F : ℕ → Module.End A (ι → A)) (r : ℕ) : Module.End A (Fin 2 × ι → A) :=
  bvec 0 ∘ₗ F r ∘ₗ slice 0 + bvec 1 ∘ₗ F r ∘ₗ slice 1 + bvec 1 ∘ₗ pred F r ∘ₗ slice 0

/-- (T2) the coproduct of `E^{(r)}` on `V ⊗ M`. -/
def tensorEd (E : ℕ → Module.End A (ι → A)) (r : ℕ) : Module.End A (Fin 2 × ι → A) :=
  bvec 0 ∘ₗ E r ∘ₗ slice 0 + bvec 1 ∘ₗ E r ∘ₗ slice 1 + bvec 0 ∘ₗ pred E r ∘ₗ slice 1

/-- (T2) the weight of `V ⊗ M`: `wt (e, i) = wt_V e + wt i`. -/
def tensorWt (wt : ι → ℤ) (p : Fin 2 × ι) : ℤ := wtV p.1 + wt p.2

variable (F : ℕ → Module.End A (ι → A))

lemma tensorFd_bvec0 (r : ℕ) (m : ι → A) :
    tensorFd F r (bvec 0 m) = bvec 0 (F r m) + bvec 1 (pred F r m) := by
  simp [tensorFd]

lemma tensorFd_bvec1 (r : ℕ) (m : ι → A) : tensorFd F r (bvec 1 m) = bvec 1 (F r m) := by
  simp [tensorFd]

lemma tensorEd_bvec0 (r : ℕ) (m : ι → A) : tensorEd F r (bvec 0 m) = bvec 0 (F r m) := by
  simp [tensorEd]

lemma tensorEd_bvec1 (r : ℕ) (m : ι → A) :
    tensorEd F r (bvec 1 m) = bvec 1 (F r m) + bvec 0 (pred F r m) := by
  simp [tensorEd]

end slots

end DPLattice

namespace DPLattice

open Finset

variable {A : Type*} [CommRing A]

section sums

variable {X : Type*} [AddCommGroup X] [Module A X]

/-- (T2, auxiliary) Pascal's rule, summed. -/
lemma pascal_sum (x : ℤ) (m : ℕ) (a : ℕ → X) :
    ∑ j ∈ range (m + 1), ((Ring.choose x j : ℤ) : A) • a j +
      ∑ j ∈ range m, ((Ring.choose x j : ℤ) : A) • a (j + 1) =
      ∑ j ∈ range (m + 1), ((Ring.choose (x + 1) j : ℤ) : A) • a j := by
  rw [sum_range_succ', sum_range_succ' (fun j => ((Ring.choose (x + 1) j : ℤ) : A) • a j)]
  simp only [Ring.choose_succ_succ, Ring.choose_zero_right, Int.cast_add, add_smul,
    sum_add_distrib]
  abel

lemma sum_trunc (r s : ℕ) (g h : ℕ → X) (hgh : ∀ j ≤ s, h j = g j) (hlast : h (s + 1) = 0) :
    ∑ j ∈ range (min r (s + 1) + 1), h j = ∑ j ∈ range (min r s + 1), g j := by
  rcases le_or_gt r s with hr | hr
  · rw [min_eq_left (by omega), min_eq_left hr]
    exact sum_congr rfl fun j hj => hgh j (by simp at hj; omega)
  · rw [min_eq_right (by omega : s + 1 ≤ r), min_eq_right hr.le, sum_range_succ, hlast, add_zero]
    exact sum_congr rfl fun j hj => hgh j (by simp at hj; omega)

lemma sum_trunc' (r s : ℕ) (g h : ℕ → X) (hgh : ∀ j ≤ r, h j = g j) (hlast : h (r + 1) = 0) :
    ∑ j ∈ range (min (r + 1) s + 1), h j = ∑ j ∈ range (min r s + 1), g j := by
  rw [min_comm, min_comm r]; exact sum_trunc s r g h hgh hlast

end sums

section tensor

variable {ι : Type*}

lemma ext_bvec {N : Type*} [AddCommGroup N] [Module A N] {T T' : (Fin 2 × ι → A) →ₗ[A] N}
    (h0 : ∀ m, T (bvec 0 m) = T' (bvec 0 m)) (h1 : ∀ m, T (bvec 1 m) = T' (bvec 1 m)) :
    T = T' := by
  refine LinearMap.ext fun f => ?_
  rw [eq_bvec_slice f, map_add, map_add, h0, h1]

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- The divided powers `pred F` satisfy the shifted (P1). -/
lemma pred_P1 (G : ℕ → Module.End A (ι → A)) (hP0 : G 0 = 1)
    (hP1 : ∀ a b : ℕ, G a ∘ₗ G b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b))
    (a b : ℕ) :
    pred G a ∘ₗ G b + G a ∘ₗ pred G b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • pred G (a + b) := by
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · simp [hP0]
    exact LinearMap.id_comp _
  · simp only [pred_succ, pred_zero, LinearMap.comp_zero, add_zero, hP0, add_zero]
    rw [choose_natAdd, Nat.add_zero, Nat.choose_self, Nat.cast_one, Int.cast_one, one_smul]
    exact LinearMap.comp_id _
  · simp only [pred_succ, hP1, choose_natAdd]
    rw [show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, pred_succ,
      show a + (b + 1) = a + b + 1 by omega, show a + 1 + b = a + b + 1 by omega, ← add_smul]
    congr 1
    rw [Nat.choose_succ_succ (a + b + 1) a]
    push_cast; ring

variable {wt : ι → ℤ} {F E : ℕ → Module.End A (ι → A)}

omit [DecidableEq ι] in
lemma tensor_P1_F (G : ℕ → Module.End A (ι → A)) (hP0 : G 0 = 1)
    (hP1 : ∀ a b : ℕ, G a ∘ₗ G b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b))
    (a b : ℕ) :
    tensorFd G a ∘ₗ tensorFd G b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • tensorFd G (a + b) := by
  have hP1' : ∀ m, G a (G b m) = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b) m :=
    fun m => LinearMap.congr_fun (hP1 a b) m
  have hpred : ∀ m, pred G a (G b m) + G a (pred G b m) =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • pred G (a + b) m :=
    fun m => LinearMap.congr_fun (pred_P1 G hP0 hP1 a b) m
  refine ext_bvec (fun m => ?_) (fun m => ?_)
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, tensorFd_bvec0, map_add,
      tensorFd_bvec1, smul_add, ← map_smul, ← hP1', ← hpred]
    abel
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, tensorFd_bvec1, ← map_smul, ← hP1']

omit [DecidableEq ι] in
lemma tensor_P1_E (G : ℕ → Module.End A (ι → A)) (hP0 : G 0 = 1)
    (hP1 : ∀ a b : ℕ, G a ∘ₗ G b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b))
    (a b : ℕ) :
    tensorEd G a ∘ₗ tensorEd G b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • tensorEd G (a + b) := by
  have hP1' : ∀ m, G a (G b m) = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b) m :=
    fun m => LinearMap.congr_fun (hP1 a b) m
  have hpred : ∀ m, pred G a (G b m) + G a (pred G b m) =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • pred G (a + b) m :=
    fun m => LinearMap.congr_fun (pred_P1 G hP0 hP1 a b) m
  refine ext_bvec (fun m => ?_) (fun m => ?_)
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, tensorEd_bvec0, ← map_smul, ← hP1']
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, tensorEd_bvec1, map_add,
      tensorEd_bvec0, smul_add, ← map_smul, ← hP1', ← hpred]
    abel

lemma tensor_W_F (hW : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i - 2 * r → F r (Pi.single i 1) j = 0) :
    ∀ (p : Fin 2 × ι) (r : ℕ) (q : Fin 2 × ι), tensorWt wt q ≠ tensorWt wt p - 2 * r →
      tensorFd F r (Pi.single p 1) q = 0 := by
  rintro ⟨e, i⟩ r ⟨e', j⟩ hq
  rw [single_eq_bvec]
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  all_goals obtain rfl | rfl : e' = 0 ∨ e' = 1 := by fin_cases e' <;> simp
  all_goals simp only [tensorWt, wtV_zero, wtV_one] at hq
  · simp [tensorFd_bvec0]; exact hW i r j (by omega)
  · rcases r with _ | r
    · simp [tensorFd_bvec0]
    · simp [tensorFd_bvec0]; exact hW i r j (by push_cast at hq; omega)
  · simp [tensorFd_bvec1]
  · simp [tensorFd_bvec1]; exact hW i r j (by omega)

lemma tensor_W_E (hW : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i + 2 * r → E r (Pi.single i 1) j = 0) :
    ∀ (p : Fin 2 × ι) (r : ℕ) (q : Fin 2 × ι), tensorWt wt q ≠ tensorWt wt p + 2 * r →
      tensorEd E r (Pi.single p 1) q = 0 := by
  rintro ⟨e, i⟩ r ⟨e', j⟩ hq
  rw [single_eq_bvec]
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  all_goals obtain rfl | rfl : e' = 0 ∨ e' = 1 := by fin_cases e' <;> simp
  all_goals simp only [tensorWt, wtV_zero, wtV_one] at hq
  · simp [tensorEd_bvec0]; exact hW i r j (by omega)
  · simp [tensorEd_bvec0]
  · rcases r with _ | r
    · simp [tensorEd_bvec1]
    · simp [tensorEd_bvec1]; exact hW i r j (by push_cast at hq; omega)
  · simp [tensorEd_bvec1]; exact hW i r j (by omega)

omit [DecidableEq ι] in
lemma tensorFd_zero (G : ℕ → Module.End A (ι → A)) (hP0 : G 0 = 1) : tensorFd G 0 = 1 := by
  refine ext_bvec (fun m => ?_) (fun m => ?_) <;> simp [tensorFd_bvec0, tensorFd_bvec1, hP0]

omit [DecidableEq ι] in
lemma tensorEd_zero (G : ℕ → Module.End A (ι → A)) (hP0 : G 0 = 1) : tensorEd G 0 = 1 := by
  refine ext_bvec (fun m => ?_) (fun m => ?_) <;> simp [tensorEd_bvec0, tensorEd_bvec1, hP0]

lemma tensor_K (h : IsDP wt F E) (p : Fin 2 × ι) (r s : ℕ) :
    tensorEd E s (tensorFd F r (Pi.single p 1)) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (tensorWt wt p + s - r) j : ℤ) : A) •
        tensorFd F (r - j) (tensorEd E (s - j) (Pi.single p 1)) := by
  obtain ⟨e, i⟩ := p
  rw [single_eq_bvec]
  -- the terms `F^{(r−j)} E^{(s−j)} δ_i` and the shifted sum `pred F ∘ pred E`
  set a : ℕ → (ι → A) := fun j => F (r - j) (E (s - j) (Pi.single i 1)) with ha
  have hshift : ∀ x : ℤ, ∑ j ∈ range (min r s + 1), ((Ring.choose x j : ℤ) : A) •
      pred F (r - j) (pred E (s - j) (Pi.single i 1)) =
      ∑ j ∈ range (min r s), ((Ring.choose x j : ℤ) : A) • a (j + 1) := by
    intro x
    rw [sum_range_succ]
    have hlast : pred F (r - min r s) (pred E (s - min r s) (Pi.single i 1)) = 0 := by
      rcases le_total r s with hrs | hrs
      · rw [min_eq_left hrs, Nat.sub_self]; simp
      · rw [min_eq_right hrs, Nat.sub_self]; simp
    rw [hlast, smul_zero, add_zero]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range, lt_min_iff] at hj
    rw [show r - j = (r - (j + 1)) + 1 by omega, show s - j = (s - (j + 1)) + 1 by omega,
      pred_succ, pred_succ]
  have hPP : pred E s (pred F r (Pi.single i 1)) =
      ∑ j ∈ range (min r s), ((Ring.choose (wt i + s - r) j : ℤ) : A) • a (j + 1) := by
    rcases r with _ | r'
    · simp
    rcases s with _ | s'
    · simp
    rw [pred_succ, pred_succ, h.K i r' s', Nat.add_min_add_right]
    refine sum_congr rfl fun j hj => ?_
    simp only [ha, Nat.add_sub_add_right]
    congr 3
    push_cast; ring
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  · simp only [tensorWt, wtV_zero, tensorFd_bvec0, tensorEd_bvec0, map_add, tensorEd_bvec1]
    apply ext_slice
    · simp only [map_add, map_sum, map_smul, slice_bvec_self, slice0_bvec1, add_zero]
      rw [zero_add, hPP, h.K i r s, pascal_sum]
      refine sum_congr rfl fun j _ => ?_
      congr 3; ring
    · simp only [map_add, map_sum, map_smul, slice_bvec_self, slice1_bvec0, zero_add]
      rw [add_zero]
      rcases r with _ | r'
      · simp
      rw [pred_succ, h.K i r' s]
      symm
      refine sum_trunc' r' s
        (fun j => ((Ring.choose (wt i + s - r') j : ℤ) : A) • F (r' - j) (E (s - j)
          (Pi.single i 1)))
        (fun j => ((Ring.choose (1 + wt i + s - ((r' + 1 : ℕ) : ℤ)) j : ℤ) : A) •
          pred F (r' + 1 - j) (E (s - j) (Pi.single i 1))) (fun j hj => ?_) ?_
      · simp only
        rw [show r' + 1 - j = (r' - j) + 1 by omega, pred_succ]
        congr 3; push_cast; ring
      · simp
  · simp only [tensorWt, wtV_one, tensorFd_bvec1, tensorEd_bvec1, map_add, tensorFd_bvec0]
    apply ext_slice
    · simp only [map_add, map_sum, map_smul, slice_bvec_self, slice0_bvec1, add_zero, zero_add]
      rcases s with _ | s'
      · simp
      rw [pred_succ, h.K i r s']
      symm
      refine sum_trunc r s'
        (fun j => ((Ring.choose (wt i + s' - r) j : ℤ) : A) • F (r - j) (E (s' - j)
          (Pi.single i 1)))
        (fun j => ((Ring.choose (-1 + wt i + ((s' + 1 : ℕ) : ℤ) - r) j : ℤ) : A) •
          F (r - j) (pred E (s' + 1 - j) (Pi.single i 1))) (fun j hj => ?_) ?_
      · simp only
        rw [show s' + 1 - j = (s' - j) + 1 by omega, pred_succ]
        congr 3; push_cast; ring
      · simp
    · simp only [map_add, map_sum, map_smul, slice_bvec_self, slice1_bvec0, zero_add, add_zero]
      rw [h.K i r s]
      simp only [smul_add, sum_add_distrib]
      rw [hshift, pascal_sum]
      refine sum_congr rfl fun j _ => ?_
      congr 3; ring

end tensor

/-- (T2) `V ⊗ M`: basis `Fin 2 × M.ι`, weight `wt (e, i) = wt_V e + wt i`, divided powers given by
the coproduct formulas (`tensorV_Fd_b0`, …). That it is a DP-lattice is (T2) (`T2`). -/
def tensorV (M : DPLattice A) : DPLattice A where
  ι := Fin 2 × M.ι
  wt := tensorWt M.wt
  Fd := tensorFd M.Fd
  Ed := tensorEd M.Ed
  isDP := ⟨tensor_W_F M.isDP.W_F, tensor_W_E M.isDP.W_E, tensorFd_zero _ M.isDP.P0_F,
    tensorEd_zero _ M.isDP.P0_E, tensor_P1_F _ M.isDP.P0_F M.isDP.P1_F,
    tensor_P1_E _ M.isDP.P0_E M.isDP.P1_E, tensor_K M.isDP⟩

/-- (T2) If `M` is a DP-lattice, then `V ⊗ M` (basis `Fin 2 × ι`, weight `wt_V e + wt i`, the
coproduct formulas of the file) satisfies (W), (P0), (P1) and (K), i.e. is a DP-lattice. -/
theorem T2 (M : DPLattice A) : IsDP (tensorWt M.wt) (tensorFd M.Fd) (tensorEd M.Ed) :=
  (tensorV M).isDP

section formulas

variable (M : DPLattice A)

/-- (T2) the weight of `V ⊗ M`: `wt (e, i) = wt_V(e) + wt(i)`. -/
theorem tensorV_wt (e : Fin 2) (i : M.ι) : (tensorV M).wt (e, i) = wtV e + M.wt i := rfl

/-- (T2) `F^{(r)}(b_0 m) = b_0 F^{(r)} m + b_1 F^{(r−1)} m` for `r ≥ 1`. -/
theorem tensorV_Fd_b0 (r : ℕ) (hr : 1 ≤ r) (m : M.ι → A) :
    (tensorV M).Fd r (bvec 0 m) = bvec 0 (M.Fd r m) + bvec 1 (M.Fd (r - 1) m) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact tensorFd_bvec0 _ _ _

/-- (T2) `F^{(0)}(b_0 m) = b_0 m` (from (P0)). -/
theorem tensorV_Fd_b0_zero (m : M.ι → A) : (tensorV M).Fd 0 (bvec 0 m) = bvec 0 m := by
  rw [show (tensorV M).Fd 0 = 1 from (tensorV M).isDP.P0_F]; rfl

/-- (T2) `F^{(r)}(b_1 m) = b_1 F^{(r)} m`. -/
theorem tensorV_Fd_b1 (r : ℕ) (m : M.ι → A) :
    (tensorV M).Fd r (bvec 1 m) = bvec 1 (M.Fd r m) := tensorFd_bvec1 _ _ _

/-- (T2) `E^{(r)}(b_1 m) = b_1 E^{(r)} m + b_0 E^{(r−1)} m` for `r ≥ 1`. -/
theorem tensorV_Ed_b1 (r : ℕ) (hr : 1 ≤ r) (m : M.ι → A) :
    (tensorV M).Ed r (bvec 1 m) = bvec 1 (M.Ed r m) + bvec 0 (M.Ed (r - 1) m) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact tensorEd_bvec1 _ _ _

/-- (T2) `E^{(0)}(b_1 m) = b_1 m` (from (P0)). -/
theorem tensorV_Ed_b1_zero (m : M.ι → A) : (tensorV M).Ed 0 (bvec 1 m) = bvec 1 m := by
  rw [show (tensorV M).Ed 0 = 1 from (tensorV M).isDP.P0_E]; rfl

/-- (T2) `E^{(r)}(b_0 m) = b_0 E^{(r)} m`. -/
theorem tensorV_Ed_b0 (r : ℕ) (m : M.ι → A) :
    (tensorV M).Ed r (bvec 0 m) = bvec 0 (M.Ed r m) := tensorEd_bvec0 _ _ _

end formulas

/-- (T3) `V^{⊗n}`: `V^{⊗0} := 𝟙`, `V^{⊗(n+1)} := V ⊗ V^{⊗n}`; its basis is
`Fin 2 × (Fin 2 × ⋯ × Unit)`. -/
def tensorPow (A : Type*) [CommRing A] : ℕ → DPLattice A
  | 0 => one A
  | n + 1 => tensorV (tensorPow A n)

/-- (T3) `V^{⊗n}` is a DP-lattice for every `n`: its data satisfy (W), (P0), (P1), (K). -/
theorem T3 (n : ℕ) : IsDP (tensorPow A n).wt (tensorPow A n).Fd (tensorPow A n).Ed :=
  (tensorPow A n).isDP

end DPLattice
