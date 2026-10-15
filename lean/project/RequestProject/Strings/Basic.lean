module

public import Mathlib

/-!
# Strings of the Boolean lattice: setting, (S1) and (S2)

This file corresponds to **§0 (Setting)**, **(S1) Commutator** and **(S2) The string relation**
of `CS1_strings_and_theorem_E.md`.

## Encoding

* `B m R := Finset (Fin m) → R`.  Since `Finset (Fin m)` is finite, this is the free `R`-module on
  the subsets of `{0, …, m-1}`; the basis vector `e_S` is `Pi.single S 1`, and a vector `f` is
  `∑ S, f S • e_S` (so `f S` is the coefficient of `e_S`).
* `H`, `U`, `D` are defined on coefficients:
  `(H f) T = |T| * f T`, `(U f) T = ∑_{x ∈ T} f (T \ {x})`, `(D f) T = ∑_{x ∉ T} f (T ∪ {x})`.
  The lemmas `H_single`, `U_single`, `D_single` show that these are exactly the maps
  `H e_S = |S| e_S`, `U e_S = ∑_{x ∉ S} e_{S ∪ {x}}`, `D e_S = ∑_{x ∈ S} e_{S \ {x}}` of the file.
* `level m R s` (the level `B_m(s)`) is the submodule of vectors supported on sets of size `s`;
  `level_eq_span` shows it is the span of the `e_S` with `|S| = s`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Strings

variable (m : ℕ) (R : Type*) [CommRing R]

/-- The Boolean lattice module `B_m(R) = Finset (Fin m) → R` (§0 of the file): the free
`R`-module with basis `e_S = Pi.single S 1`, `S ⊆ {0,…,m-1}`. -/
abbrev B := Finset (Fin m) → R

/-- The size operator `H` (§0): on coefficients `(H f) T = |T| * f T`, i.e. `H e_S = |S| e_S`
(see `H_single`). -/
def H : B m R →ₗ[R] B m R where
  toFun f T := (T.card : R) * f T
  map_add' f g := by ext T; simp [mul_add]
  map_smul' a f := by ext T; simp; ring

/-- The up operator `U` (§0): on coefficients `(U f) T = ∑_{x ∈ T} f (T \ {x})`, i.e.
`U e_S = ∑_{x ∉ S} e_{S ∪ {x}}` (see `U_single`). -/
def U : B m R →ₗ[R] B m R where
  toFun f T := ∑ x ∈ T, f (T.erase x)
  map_add' f g := by ext T; simp [sum_add_distrib]
  map_smul' a f := by ext T; simp [mul_sum]

/-- The down operator `D` (§0): on coefficients `(D f) T = ∑_{x ∉ T} f (T ∪ {x})`, i.e.
`D e_S = ∑_{x ∈ S} e_{S \ {x}}` (see `D_single`). -/
def D : B m R →ₗ[R] B m R where
  toFun f T := ∑ x ∈ Tᶜ, f (insert x T)
  map_add' f g := by ext T; simp [sum_add_distrib]
  map_smul' a f := by ext T; simp [mul_sum]

/-- The level `B_m(s)` (§0): vectors whose coefficients vanish off the sets of size `s`.
By `level_eq_span` this is the span of the `e_S` with `|S| = s`. -/
def level (s : ℕ) : Submodule R (B m R) where
  carrier := {f | ∀ S : Finset (Fin m), S.card ≠ s → f S = 0}
  add_mem' hf hg S hS := by simp [hf S hS, hg S hS]
  zero_mem' S _ := rfl
  smul_mem' a f hf S hS := by simp [hf S hS]

variable {m R}

@[simp] lemma H_apply (f : B m R) (T : Finset (Fin m)) : H m R f T = (T.card : R) * f T := rfl
@[simp] lemma U_apply (f : B m R) (T : Finset (Fin m)) :
    U m R f T = ∑ x ∈ T, f (T.erase x) := rfl
@[simp] lemma D_apply (f : B m R) (T : Finset (Fin m)) :
    D m R f T = ∑ x ∈ Tᶜ, f (insert x T) := rfl

lemma mem_level {s : ℕ} {f : B m R} : f ∈ level m R s ↔ ∀ S, S.card ≠ s → f S = 0 := Iff.rfl

/-! ### The operators on the basis vectors `e_S = Pi.single S 1` -/

/-- `H e_S = |S| e_S`. -/
lemma H_single (S : Finset (Fin m)) :
    H m R (Pi.single S 1) = (S.card : R) • (Pi.single S 1 : B m R) := by
  ext T
  by_cases h : T = S
  · subst h; simp
  · simp [h]

/-- `U e_S = ∑_{x ∉ S} e_{S ∪ {x}}`. -/
lemma U_single (S : Finset (Fin m)) :
    U m R (Pi.single S 1) = ∑ x ∈ Sᶜ, (Pi.single (insert x S) 1 : B m R) := by
  ext T
  simp only [U_apply, Pi.single_apply, Finset.sum_apply]
  rw [Finset.sum_boole, Finset.sum_boole]
  congr 1
  apply Finset.card_bij (fun x _ => x)
  · intro x hx
    simp only [mem_filter, mem_compl] at hx ⊢
    obtain ⟨hxT, rfl⟩ := hx
    simp [hxT]
  · intro _ _ _ _ h; exact h
  · intro x hx
    simp only [mem_filter, mem_compl] at hx
    obtain ⟨hxS, rfl⟩ := hx
    exact ⟨x, by simp [hxS], rfl⟩

/-- `D e_S = ∑_{x ∈ S} e_{S \ {x}}`. -/
lemma D_single (S : Finset (Fin m)) :
    D m R (Pi.single S 1) = ∑ x ∈ S, (Pi.single (S.erase x) 1 : B m R) := by
  ext T
  simp only [D_apply, Pi.single_apply, Finset.sum_apply]
  rw [Finset.sum_boole, Finset.sum_boole]
  congr 1
  apply Finset.card_bij (fun x _ => x)
  · intro x hx
    simp only [mem_filter, mem_compl] at hx ⊢
    obtain ⟨hxT, rfl⟩ := hx
    simp [hxT]
  · intro _ _ _ _ h; exact h
  · intro x hx
    simp only [mem_filter] at hx
    obtain ⟨hxS, rfl⟩ := hx
    exact ⟨x, by simp [hxS], rfl⟩

/-- The level `B_m(s)` is the span of the basis vectors `e_S` with `|S| = s`. -/
lemma level_eq_span (s : ℕ) :
    level m R s = Submodule.span R
      ((fun S => (Pi.single S (1 : R) : B m R)) '' {S | S.card = s}) := by
  apply le_antisymm
  · intro f hf
    have : f = ∑ S ∈ univ.filter (fun S : Finset (Fin m) => S.card = s), f S • (Pi.single S 1 : B m R) := by
      ext T
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      by_cases hT : T.card = s
      · simp [hT]
      · simp [hT, hf T hT]
    rw [this]
    refine Submodule.sum_mem _ (fun S hS => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact ⟨S, by simpa using hS, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨S, hS, rfl⟩ T hT
    have : T ≠ S := fun h => hT (h ▸ hS)
    simp [this]

/-! ### Basic level lemmas -/

lemma eq_zero_of_mem_level_of_lt {s : ℕ} {f : B m R} (hf : f ∈ level m R s) (hs : m < s) :
    f = 0 := by
  ext S
  apply hf
  have := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
  omega

lemma H_of_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    H m R f = (s : R) • f := by
  ext T
  by_cases hT : T.card = s
  · simp [hT]
  · simp [hf T hT]

lemma U_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    U m R f ∈ level m R (s + 1) := by
  intro T hT
  simp only [U_apply]
  refine Finset.sum_eq_zero (fun x hx => hf _ ?_)
  have := Finset.card_pos.mpr ⟨x, hx⟩
  rw [Finset.card_erase_of_mem hx]
  omega

lemma U_pow_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) (i : ℕ) :
    (U m R ^ i) f ∈ level m R (s + i) := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact U_mem_level ih

lemma D_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R (s + 1)) :
    D m R f ∈ level m R s := by
  intro T hT
  simp only [D_apply]
  refine Finset.sum_eq_zero (fun x hx => hf _ ?_)
  rw [Finset.card_insert_of_notMem (by simpa using hx)]
  omega

lemma D_of_mem_level_zero {f : B m R} (hf : f ∈ level m R 0) : D m R f = 0 := by
  ext T
  simp only [D_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero (fun x hx => hf _ ?_)
  simp

/-! ### (S1) The commutator -/

/-- **(S1) Commutator.**  `D ∘ U − U ∘ D = m · id − 2 H` on `B_m(R)`, for every commutative
ring `R` (composition of linear maps is `∘ₗ`). -/
theorem commutator_DU_UD :
    D m R ∘ₗ U m R - U m R ∘ₗ D m R = (m : R) • LinearMap.id - (2 : R) • H m R := by
  refine LinearMap.ext (fun f => funext (fun T => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, D_apply, U_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, H_apply, Pi.sub_apply]
  have h1 : ∀ x ∈ Tᶜ, ∑ y ∈ insert x T, f ((insert x T).erase y) =
      f T + ∑ y ∈ T, f (insert x (T.erase y)) := by
    intro x hx
    rw [mem_compl] at hx
    rw [Finset.sum_insert hx, Finset.erase_insert hx]
    congr 1
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.erase_insert_of_ne]
    rintro rfl; exact hx hy
  have h2 : ∀ y ∈ T, ∑ x ∈ (T.erase y)ᶜ, f (insert x (T.erase y)) =
      f T + ∑ x ∈ Tᶜ, f (insert x (T.erase y)) := by
    intro y hy
    rw [Finset.compl_erase, Finset.sum_insert (by simpa using hy), Finset.insert_erase hy]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_comm (s := Tᶜ) (t := T)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin]
  rw [Nat.cast_sub (by simpa using T.card_le_univ)]
  ring

/-- (S1) pointwise, in the form used later. -/
lemma DU_apply (f : B m R) :
    D m R (U m R f) = U m R (D m R f) + (m : R) • f - (2 : R) • H m R f := by
  have := congrArg (fun φ => φ f) (commutator_DU_UD (m := m) (R := R))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at this
  rw [sub_eq_iff_eq_add'] at this
  rw [this]; abel

/-- (S1) on a level: for `f ∈ B_m(s)`, `D U f = U D f + (m − 2s) f`. -/
lemma DU_apply_of_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    D m R (U m R f) = U m R (D m R f) + ((m : ℤ) - 2 * s) • f := by
  rw [DU_apply, H_of_mem_level hf, ← Int.cast_smul_eq_zsmul R, smul_smul]
  push_cast
  rw [sub_smul]
  abel

/-! ### (S2) The string relation -/

lemma string_relation_succ {k : ℕ} {v : B m R} (hv : v ∈ level m R k) (hD : D m R v = 0)
    (i : ℕ) :
    D m R ((U m R ^ (i + 1)) v) = (((i : ℤ) + 1) * ((m : ℤ) - 2 * k - i)) • (U m R ^ i) v := by
  induction i with
  | zero => simp [DU_apply_of_mem_level hv, hD]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply,
      DU_apply_of_mem_level (U_pow_mem_level hv (i + 1)), ih, map_zsmul]
    rw [show (U m R) ((U m R ^ i) v) = (U m R ^ (i + 1)) v by rw [pow_succ', Module.End.mul_apply],
      ← add_smul]
    congr 1
    push_cast
    ring

/-- **(S2) The string relation.**  If `v ∈ B_m(k)` and `D v = 0`, then for every `i ≥ 1`,
`D (U^i v) = i (m − 2k − i + 1) · U^{i−1} v` (the integer scalar acts by `ℤ`-multiplication;
`U ^ i` is the `i`-th power in `Module.End R (B m R)`). -/
theorem string_relation {k : ℕ} {v : B m R} (hv : v ∈ level m R k) (hD : D m R v = 0)
    {i : ℕ} (hi : 1 ≤ i) :
    D m R ((U m R ^ i) v) = ((i : ℤ) * ((m : ℤ) - 2 * k - i + 1)) • (U m R ^ (i - 1)) v := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [string_relation_succ hv hD j]
  simp only [Nat.add_sub_cancel]
  congr 1
  push_cast
  ring

end ColouredSand.Strings
