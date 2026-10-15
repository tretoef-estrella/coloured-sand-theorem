module

public import RequestProject.OddTheoremI.Basic
public import RequestProject.OddWindows.All
public import RequestProject.OddRulers.All
public import RequestProject.OddCeiling.All
public import RequestProject.OddHouses.All
public import RequestProject.OddCellFloor.All
public import RequestProject.DanceSmith.All

/-!
# `CSI18_theorem_4_4_smith_form_of_Mp.md`, *Setting* and *Part Z0* — `Mp` in o-order, integrality

Namespace `ColouredSand.OddTwist`; every new name carries the prefix `oddSmith`.

## Encodings

* `p` is a prime (`[Fact p.Prime]`); oddness, where needed, is the hypothesis `hodd : Odd p`.
  `λ` is `l`, `k = kTop p l`, `d_t = digitL p l t`, `I = Iset p l` (CSI10), `N = 2 ^ #I`, and
  `K = d_k p^k` is `oddSmithK p l = digitL p l (kTop p l) * p ^ kTop p l`.
* **Slots in o-order.** CSI12's `labL p l i e (kTop p l)` is a bijection from `slots p l i e` onto
  the subsets of `I` (`slots_as_subsets`). The position `q : Fin N` is the dancer
  `TheoremF.dancer I q` (base-`p` o-order = binary o-order, CSI14 (A1)), and
  `oddSmithSlot p l i e : Fin N ≃ slots p l i e` sends `q` to the slot with label `dancer I q`
  (`oddSmith_labL_slot`).
* **The matrix in o-order** `oddSmithMo p l i e q q' = Mp p l i e (slot q) (slot q')`, a matrix over
  `ℤ_[p]` on `Fin N`.
* **Part Z0.** `oddSmith_Mp_mem_bot`: every entry of `Mp` lies in the smallest subring `⊥` of
  `ℤ_[p]`, i.e. is the image of an integer (the data `Q_0`, the moves `QT`, `QS` and the products
  only multiply, add and scale by integers; this is proved by induction along CSI10's recursion
  `iterD`). `oddSmithMZ p l i e : Matrix (Fin N) (Fin N) ℤ` is the integer matrix with
  `oddSmithMo = (oddSmithMZ).map Int.cast` (`oddSmith_Z0`); it is unique (`oddSmith_Z0_unique`).
* Simultaneous permutations of rows and columns are `M.submatrix σ σ`; `ddP` is CSI14's `p`-adic
  determinantal divisor.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset Matrix TheoremF

/-! ### Integrality (Part Z0) -/

section integrality

variable {A : Type*} [CommRing A]

/-- All entries of `M` lie in the subring `T` (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithEntriesIn (T : Subring A) {S : Type*} (M : Matrix S S A) : Prop := ∀ x y, M x y ∈ T

variable {T : Subring A} {S : Type*}

lemma oddSmith_entriesIn_mul [Fintype S] {M M' : Matrix S S A} (hM : oddSmithEntriesIn T M)
    (hM' : oddSmithEntriesIn T M') : oddSmithEntriesIn T (M * M') := fun x y => by
  rw [Matrix.mul_apply]; exact T.sum_mem fun z _ => T.mul_mem (hM x z) (hM' z y)

lemma oddSmith_entriesIn_one [DecidableEq S] : oddSmithEntriesIn T (1 : Matrix S S A) :=
  fun x y => by
    rw [Matrix.one_apply]; split_ifs
    · exact T.one_mem
    · exact T.zero_mem

lemma oddSmith_entriesIn_smul {c : A} (hc : c ∈ T) {M : Matrix S S A}
    (hM : oddSmithEntriesIn T M) : oddSmithEntriesIn T (c • M) := fun x y => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact T.mul_mem hc (hM x y)

lemma oddSmith_entriesIn_list_prod [Fintype S] [DecidableEq S] (L : List (Matrix S S A))
    (h : ∀ M ∈ L, oddSmithEntriesIn T M) : oddSmithEntriesIn T L.prod := by
  induction L with
  | nil => exact oddSmith_entriesIn_one
  | cons M L ih =>
    rw [List.prod_cons]
    exact oddSmith_entriesIn_mul (h M (by simp)) (ih fun M' hM' => h M' (by simp [hM']))

lemma oddSmith_entriesIn_prodQ [Fintype S] [DecidableEq S] {Q : ℕ → Matrix S S A}
    (hQ : ∀ f, oddSmithEntriesIn T (Q f)) (a b : ℕ) : oddSmithEntriesIn T (prodQ Q a b) :=
  oddSmith_entriesIn_list_prod _ fun M hM => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hM; exact hQ _

lemma oddSmith_natCast_mem (n : ℕ) : (n : A) ∈ T := natCast_mem T n

lemma oddSmith_entriesIn_stepD (p d : ℕ) (D : SData A) (hD : ∀ f, oddSmithEntriesIn T (D.Q f)) :
    ∀ f, oddSmithEntriesIn T ((stepD p d D).Q f) := by
  have hp : -(p : A) ^ (p - 2) ∈ T := T.neg_mem (T.pow_mem (oddSmith_natCast_mem p) _)
  by_cases hd : d = 0
  · subst hd
    rw [stepD_zero]
    intro f
    exact oddSmith_entriesIn_smul hp (oddSmith_entriesIn_list_prod _ fun M hM => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hM; exact hD _)
  · rw [stepD_pos p d hd]
    intro f x y
    obtain ⟨x, bx⟩ := x
    obtain ⟨y, b⟩ := y
    cases bx <;> cases b
    · exact oddSmith_entriesIn_smul hp (oddSmith_entriesIn_prodQ hD _ _) x y
    · exact T.zero_mem
    · exact oddSmith_entriesIn_smul (T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _)
        (T.pow_mem (oddSmith_natCast_mem p) _)) (oddSmith_entriesIn_prodQ hD _ _) x y
    · exact oddSmith_entriesIn_smul hp (oddSmith_entriesIn_prodQ hD _ _) x y

lemma oddSmith_entriesIn_iterD (p : ℕ) (dg : ℕ → ℕ) (D : SData A)
    (hD : ∀ f, oddSmithEntriesIn T (D.Q f)) :
    ∀ t f, oddSmithEntriesIn T ((iterD p dg t D).Q f) := by
  intro t
  induction t with
  | zero => exact hD
  | succ t ih => exact oddSmith_entriesIn_stepD p (dg t) _ ih

end integrality

variable (p : ℕ) [hp : Fact p.Prime]

/-- **(Z0) integrality** (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`), slot form: every entry
of `Mp p λ i e` lies in the smallest subring `⊥` of `ℤ_[p]`, i.e. is the image of an integer.
(No hypothesis on `p`, `e`, `i` is needed.) -/
theorem oddSmith_Mp_mem_bot (l i e : ℕ) (x y : slots p l i e) :
    Mp p l i e x y ∈ (⊥ : Subring ℤ_[p]) := by
  have hQ0 : ∀ f, oddSmithEntriesIn (⊥ : Subring ℤ_[p]) ((⟨Unit, Q0 ℤ_[p] p e i⟩ : SData ℤ_[p]).Q f) :=
    fun f x y => by
      change (p : ℤ_[p]) ^ (e - 1) * ((f : ℤ_[p]) + i) ∈ _
      exact Subring.mul_mem _ (Subring.pow_mem _ (oddSmith_natCast_mem p) _)
        (Subring.add_mem _ (oddSmith_natCast_mem f) (oddSmith_natCast_mem i))
  have hQ := oddSmith_entriesIn_iterD p (digitL p l) _ hQ0 (kTop p l)
  exact oddSmith_entriesIn_smul (Subring.pow_mem _ (oddSmith_natCast_mem p) _)
    (oddSmith_entriesIn_prodQ hQ _ _) x y

/-! ### Slots in o-order -/

/-- `K = d_k p^k` (*Setting* of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithK (l : ℕ) : ℕ := digitL p l (kTop p l) * p ^ kTop p l

omit hp in
lemma oddSmith_dancer_sub (l q : ℕ) :
    dancer (Iset p l) q ⊆ (Iset p l).filter (· < kTop p l) := fun _ ht =>
  mem_filter.2 ⟨lemma_0a _ _ ht, by
    have := lemma_0a (Iset p l) q ht
    simp only [Iset, mem_filter, mem_range] at this
    exact this.1⟩

/-- The slot of the dancer at position `q` (*Setting* of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithSlotFun (l i e : ℕ) (q : Fin (2 ^ #(Iset p l))) : slots p l i e :=
  Classical.choose ((slots_as_subsets p l i e (kTop p l) le_rfl).surj _ (oddSmith_dancer_sub p l q))

lemma oddSmith_labL_slotFun (l i e : ℕ) (q : Fin (2 ^ #(Iset p l))) :
    labL p l i e (kTop p l) (oddSmithSlotFun p l i e q) = dancer (Iset p l) q :=
  Classical.choose_spec
    ((slots_as_subsets p l i e (kTop p l) le_rfl).surj _ (oddSmith_dancer_sub p l q))

lemma oddSmith_slotFun_injective (l i e : ℕ) : Function.Injective (oddSmithSlotFun p l i e) := by
  intro q q' h
  have h' := congrArg (labL p l i e (kTop p l)) h
  rw [oddSmith_labL_slotFun, oddSmith_labL_slotFun] at h'
  exact Fin.ext (CellFloor.dancer_inj q.2 q'.2 h')

/-- **Slots in o-order** (*Setting* of `CSI18_theorem_4_4_smith_form_of_Mp.md`): the bijection
`Fin N ≃ slots p λ i e` sending the position `q` to the slot labelled (CSI12) by `dancer_I q`. -/
def oddSmithSlot (l i e : ℕ) : Fin (2 ^ #(Iset p l)) ≃ slots p l i e :=
  Equiv.ofBijective (oddSmithSlotFun p l i e)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨oddSmith_slotFun_injective p l i e, by rw [card_slots, Fintype.card_fin]⟩)

/-- The slot of position `q` has label `dancer_I q` (*Setting* of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
theorem oddSmith_labL_slot (l i e : ℕ) (q : Fin (2 ^ #(Iset p l))) :
    labL p l i e (kTop p l) (oddSmithSlot p l i e q) = dancer (Iset p l) q :=
  oddSmith_labL_slotFun p l i e q

/-- **The matrix in o-order** (*Setting* of `CSI18_theorem_4_4_smith_form_of_Mp.md`):
`Mo q q' := Mp (dancer_I q) (dancer_I q')`, i.e. `Mp` read at the slots of the positions `q, q'`. -/
def oddSmithMo (l i e : ℕ) : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ_[p] :=
  (Mp p l i e).submatrix (oddSmithSlot p l i e) (oddSmithSlot p l i e)

/-- **The integer matrix** `MZ` (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`): the integer
whose image in `ℤ_[p]` is `Mo q q'` (it exists by `oddSmith_Mp_mem_bot`, and it is unique since
`ℤ → ℤ_[p]` is injective). -/
def oddSmithMZ (l i e : ℕ) : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ :=
  fun q q' => Classical.choose (Subring.mem_bot.1
    (oddSmith_Mp_mem_bot p l i e (oddSmithSlot p l i e q) (oddSmithSlot p l i e q')))

/-- **(Z0)** (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`): `Mo = MZ.map Int.cast`. -/
theorem oddSmith_Z0 (l i e : ℕ) : oddSmithMo p l i e = (oddSmithMZ p l i e).map (Int.cast) := by
  ext q q'
  exact (Classical.choose_spec (Subring.mem_bot.1
    (oddSmith_Mp_mem_bot p l i e (oddSmithSlot p l i e q) (oddSmithSlot p l i e q')))).symm

/-- **(Z0)**, existence form (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`): there is
`MZ : Matrix (Fin N) (Fin N) ℤ` with `Mo = MZ.map Int.cast`. -/
theorem oddSmith_Z0_exists (l i e : ℕ) :
    ∃ MZ : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      oddSmithMo p l i e = MZ.map (Int.cast) :=
  ⟨_, oddSmith_Z0 p l i e⟩

/-- The integer matrix of (Z0) is unique (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
theorem oddSmith_Z0_unique (l i e : ℕ)
    (MZ : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ)
    (h : oddSmithMo p l i e = MZ.map (Int.cast)) : MZ = oddSmithMZ p l i e := by
  ext q q'
  have h1 := congrFun (congrFun h q) q'
  rw [oddSmith_Z0] at h1
  simp only [Matrix.map_apply] at h1
  exact_mod_cast h1.symm

lemma oddSmith_MZ_cast (l i e : ℕ) (q q' : Fin (2 ^ #(Iset p l))) :
    ((oddSmithMZ p l i e q q' : ℤ) : ℤ_[p]) =
      Mp p l i e (oddSmithSlot p l i e q) (oddSmithSlot p l i e q') := by
  have h := congrFun (congrFun (oddSmith_Z0 p l i e) q) q'
  simp only [Matrix.map_apply] at h
  rw [← h]; rfl

/-- **(Z0)**, permutations (Part Z0 of `CSI18_theorem_4_4_smith_form_of_Mp.md`): a simultaneous
permutation of rows and columns does not change `ddP` (its matrices have determinant `±1`). -/
theorem oddSmith_ddP_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ)
    (r : ℕ) : ddP p (M.submatrix σ σ) r = ddP p M r := by
  rw [DanceSmith.submatrix_perm_eq]
  exact D1_invariance hp.out M _ _ (not_dvd_det_perm hp.out σ) (not_dvd_det_perm hp.out _) r

/-! ### Exact valuations of integers in `ℤ_[p]` -/

/-- For an integer `z` with `(z : ℤ_[p]) ≠ 0` of valuation `v`: `p^v ∣ z` and `p^{v+1} ∤ z`. -/
lemma oddSmith_exact_of_valuation {z : ℤ} (hz : (z : ℤ_[p]) ≠ 0) :
    (p : ℤ) ^ (z : ℤ_[p]).valuation ∣ z ∧ ¬ (p : ℤ) ^ ((z : ℤ_[p]).valuation + 1) ∣ z := by
  have key : ∀ n : ℕ, (p : ℤ) ^ n ∣ z ↔ n ≤ (z : ℤ_[p]).valuation := fun n => by
    rw [← PadicInt.mem_span_pow_iff_le_valuation _ hz, Ideal.mem_span_singleton,
      PadicInt.pow_p_dvd_int_iff]
  exact ⟨(key _).2 le_rfl, fun h => by have := (key _).1 h; omega⟩

lemma oddSmith_MZ_ne_zero {l i e : ℕ} {q q' : Fin (2 ^ #(Iset p l))}
    (h : Mp p l i e (oddSmithSlot p l i e q) (oddSmithSlot p l i e q') ≠ 0) :
    oddSmithMZ p l i e q q' ≠ 0 := by
  intro h0; apply h; rw [← oddSmith_MZ_cast, h0, Int.cast_zero]

end ColouredSand.OddTwist
