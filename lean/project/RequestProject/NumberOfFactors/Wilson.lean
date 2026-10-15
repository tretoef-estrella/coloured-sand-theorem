module

public import RequestProject.NumberOfFactors.Abstract
public import RequestProject.Strings.Global

/-!
# (D1) Wilson's diagonal form of `W_{t,t+1}`

This file corresponds to **(D1) Wilson's diagonal form, the case `k = t + 1`** of
`CS5_theorem_D_number_of_factors.md`.

## Encoding

* Subsets of `[m]` are `Finset (Fin m)`; the `t`-subsets are the subtype
  `{S : Finset (Fin m) // S.card = t}`.
* The inclusion matrix `W_{t,t+1}` is `inclMat m t`, an integer matrix with rows indexed by the
  `t`-subsets and columns indexed by the `(t+1)`-subsets, entry `1` if the row subset is contained
  in the column subset and `0` otherwise.
* "Equivalent over `ℤ` to a (rectangular) diagonal matrix" is: there are integer matrices `P`, `Q`
  with unit determinant (i.e. invertible over `ℤ`) and an injection `φ` from rows to columns such
  that `P * W * Q` has entry `t + 1 − lab a` at `(a, φ a)` and `0` elsewhere.  The function `lab`
  records the index `i` of each diagonal entry `t + 1 − i`; the multiplicity of `t + 1 − i` is the
  number of rows with `lab a = i`, which is `C(m,i) − C(m,i−1)` (`strMult m i`, with
  `C(m,−1) = 0`).  Since the number of rows is `C(m,t) = ∑_{i ≤ t} (C(m,i) − C(m,i−1))`, every
  row carries one diagonal entry and the remaining columns are zero.
* The hypothesis `t ≤ m − t − 1` (in the integers) is written `2 * t + 1 ≤ m`.

## Proof

Not through the integral strings (they do not split over `ℤ`), but through the filtrations
`F_j = span of the rows of W_{0,t}, …, W_{j−1,t}` and `F'_j` (the same for `t + 1`), which are
saturated (`gsub_sat`), with `U (row S of W_{i,t}) = (t + 1 − i) · (row S of W_{i,t+1})`; then the
abstract criterion `abstract_diag` applies.  The ranks of the filtration steps are computed with
the Gottlieb–Kantor injectivity `zeta_inj`.
-/

@[expose] public section

open Finset Module

namespace ColouredSand.NumberOfFactors

open ColouredSand.Strings

/-! ### The up operator on a level is a `zeta` -/

lemma sum_erase_eq_sum_powersetCard {m t : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin m) → M) {T : Finset (Fin m)}
    (hT : T.card = t + 1) : ∑ x ∈ T, f (T.erase x) = ∑ S ∈ T.powersetCard t, f S := by
  refine sum_bij (fun x _ => T.erase x) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    rw [mem_powersetCard]
    exact ⟨erase_subset x T, by rw [card_erase_of_mem hx, hT]; omega⟩
  · intro x hx y hy hxy
    have h1 : x ∉ T.erase x := notMem_erase x T
    by_contra hne
    have : x ∈ T.erase y := mem_erase.mpr ⟨hne, hx⟩
    have hxy' : T.erase x = T.erase y := hxy
    rw [← hxy'] at this
    exact h1 this
  · intro S hS
    rw [mem_powersetCard] at hS
    have hc : (T \ S).card = 1 := by rw [card_sdiff_of_subset hS.1, hS.2, hT]; omega
    obtain ⟨x, hx⟩ := card_eq_one.mp hc
    have hxT : x ∈ T := (mem_sdiff.mp (hx ▸ mem_singleton_self x)).1
    refine ⟨x, hxT, ?_⟩
    ext y
    simp only [mem_erase]
    constructor
    · rintro ⟨hyx, hyT⟩
      by_contra hyS
      have : y ∈ T \ S := mem_sdiff.mpr ⟨hyT, hyS⟩
      rw [hx, mem_singleton] at this
      exact hyx this
    · intro hyS
      refine ⟨?_, hS.1 hyS⟩
      rintro rfl
      have : y ∈ T \ S := hx ▸ mem_singleton_self y
      exact (mem_sdiff.mp this).2 hyS

/-- On the level `B_m(t)`, the up operator is `zeta univ (t+1)`:
`(U f) T = ∑_{S ⊆ T, |S| = t} f S` for `|T| = t + 1`. -/
lemma U_eq_zeta {m t : ℕ} {f : B m ℤ} (hf : f ∈ level m ℤ t) :
    U m ℤ f = zeta univ (t + 1) f := by
  ext T
  rw [U_apply, zeta_apply]
  by_cases hT : T.card = t + 1
  · rw [if_pos ⟨subset_univ T, hT⟩, sum_erase_eq_sum_powersetCard f hT]
    refine sum_subset (fun S hS => mem_powerset.mpr (mem_powersetCard.mp hS).1) fun S hS hS' => ?_
    apply hf
    intro h
    exact hS' (mem_powersetCard.mpr ⟨mem_powerset.mp hS, h⟩)
  · rw [if_neg (fun h => hT h.2)]
    refine sum_eq_zero fun x hx => hf _ ?_
    have := card_pos.mpr ⟨x, hx⟩
    rw [card_erase_of_mem hx]
    omega

lemma zeta_mem_level {m : ℕ} (s : ℕ) (c : B m ℤ) : zeta univ s c ∈ level m ℤ s := by
  intro T hT
  exact zeta_eq_zero_of_not c (fun h => hT h.2)

lemma level_support {m s : ℕ} {f : B m ℤ} (hf : f ∈ level m ℤ s) :
    ∀ S ⊆ (univ : Finset (Fin m)), S.card ≠ s → f S = 0 := fun S _ h => hf S h

lemma zeta_of_mem_level {m s : ℕ} {f : B m ℤ} (hf : f ∈ level m ℤ s) : zeta univ s f = f := by
  ext T
  by_cases hT : T.card = s
  · exact zeta_self (level_support hf) (subset_univ T) hT
  · rw [zeta_eq_zero_of_not f (fun h => hT h.2), hf T hT]

lemma level_le_lowSub {m j : ℕ} : level m ℤ j ≤ lowSub (j + 1) := by
  intro c hc S hS
  exact hc S (by omega)

lemma lowSub_succ {m j : ℕ} :
    (lowSub (j + 1) : Submodule ℤ (B m ℤ)) = lowSub j ⊔ level m ℤ j := by
  apply le_antisymm
  · intro c hc
    have h1 : c - projv j c ∈ lowSub j := by
      intro S hS
      simp only [projv, Pi.sub_apply]
      split_ifs with h
      · ring
      · rw [hc S (by omega)]; ring
    have h2 : projv j c ∈ level m ℤ j := fun S hS => by simp [projv, hS]
    have : c = (c - projv j c) + projv j c := by abel
    rw [this]
    exact Submodule.add_mem_sup h1 h2
  · refine sup_le (fun c hc S hS => hc S (by omega)) level_le_lowSub

lemma lowSub_zero {m : ℕ} : (lowSub 0 : Submodule ℤ (B m ℤ)) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Submodule.mem_bot]
  funext S
  exact hc S (Nat.zero_le _)

/-! ### Ranks of the filtration -/

/-- `rank (span of the rows of W_{0,s}, …, W_{j,s}) = C(m, j)` for `j ≤ s`, `j + s ≤ m`. -/
lemma finrank_gsub {m j s : ℕ} (hjs : j ≤ s) (hm : j + s ≤ m) :
    finrank ℤ (Gsub (univ : Finset (Fin m)) (j + 1) s) = m.choose j := by
  apply le_antisymm
  · obtain ⟨N, hN, hlift⟩ := lift_lower (univ : Finset (Fin m)) (j := j + 1) (k := j) (s := s)
      le_rfl hjs
    have hmaps : ∀ x ∈ Gsub (univ : Finset (Fin m)) (j + 1) s,
        (N • LinearMap.id : B m ℤ →ₗ[ℤ] B m ℤ) x ∈ (level m ℤ j).map (zeta univ s) := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hds, -⟩ := hlift c hc
      refine ⟨d, fun S hS => hd S (subset_univ S) hS, ?_⟩
      rw [hds]; rfl
    let f := (N • LinearMap.id : B m ℤ →ₗ[ℤ] B m ℤ).restrict hmaps
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      simp only [f, LinearMap.restrict_coe_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
      exact smul_right_injective _ hN this
    calc finrank ℤ (Gsub (univ : Finset (Fin m)) (j + 1) s)
        ≤ finrank ℤ ((level m ℤ j).map (zeta univ s)) :=
          LinearMap.finrank_le_finrank_of_injective hf
      _ ≤ finrank ℤ (level m ℤ j) := Submodule.finrank_map_le _ _
      _ = m.choose j := finrank_level j
  · have hinj : Function.Injective ((zeta univ s).comp (level m ℤ j).subtype) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at hx
      have := zeta_inj (univ : Finset (Fin m)) j s hjs (by simpa using hm) x.1
        (level_support x.2) hx
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext fun S => this S (subset_univ S))
    have h1 := LinearMap.finrank_range_of_inj hinj
    rw [finrank_level] at h1
    rw [← h1]
    apply Submodule.finrank_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, level_le_lowSub x.2, rfl⟩

/-! ### The statement -/

/-- The inclusion matrix `W_{t,t+1}` of `[m] = Fin m`: rows are the `t`-subsets, columns the
`(t+1)`-subsets, entry `1` if the row subset is contained in the column subset, else `0`. -/
def inclMat (m t : ℕ) :
    Matrix {S : Finset (Fin m) // S.card = t} {T : Finset (Fin m) // T.card = t + 1} ℤ :=
  Matrix.of fun S T => if (S : Finset (Fin m)) ⊆ T then 1 else 0


/-- `zeta univ s`, as a map into the level `B_m(s)`. -/
def zetaL (m s : ℕ) : B m ℤ →ₗ[ℤ] level m ℤ s :=
  (zeta univ s).codRestrict (level m ℤ s) (zeta_mem_level s)

lemma mem_map_zetaL_iff {m j s : ℕ} (x : level m ℤ s) :
    x ∈ (lowSub j).map (zetaL m s) ↔ (x : B m ℤ) ∈ Gsub (univ : Finset (Fin m)) j s := by
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, h⟩; exact ⟨c, hc, Subtype.ext h⟩

lemma isSat_map_zetaL {m j s : ℕ} : IsSat ((lowSub j).map (zetaL m s)) := by
  intro n x hn hx
  rw [mem_map_zetaL_iff] at hx ⊢
  exact gsub_sat _ j s n _ hn hx

lemma finrank_map_zetaL {m j s : ℕ} :
    finrank ℤ ((lowSub j).map (zetaL m s)) = finrank ℤ (Gsub (univ : Finset (Fin m)) j s) := by
  rw [(Submodule.equivMapOfInjective _ (level m ℤ s).injective_subtype _).finrank_eq,
    ← Submodule.map_comp]
  rfl

lemma choose_pred_eq {t j : ℕ} (hj : j ≤ t) :
    ((((t + 1 - j).choose (t - j) : ℕ)) : ℤ) = (t : ℤ) + 1 - j := by
  rw [show t - j = (t + 1 - j) - 1 by omega, Nat.choose_symm (by omega), Nat.choose_one_right,
    Nat.cast_sub (by omega)]
  push_cast; ring

/-- **(D1), basis form.**  For `2t + 1 ≤ m` there are `ℤ`-bases `b` of the level `B_m(t)` and
`b'` of the level `B_m(t+1)` (of `B_m(ℤ) = Finset (Fin m) → ℤ`) and an injection `φ` such that
`U (b a) = (t + 1 − lab a) • b' (φ a)`, where the label `i` occurs `C(m,i) − C(m,i−1)` times,
`0 ≤ i ≤ t`. -/
theorem wilson_bases (m t : ℕ) (ht : 2 * t + 1 ≤ m) :
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (b : Basis ι ℤ (level m ℤ t))
      (b' : Basis κ ℤ (level m ℤ (t + 1))) (φ : ι ↪ κ) (lab : ι → ℕ),
      (∀ a, lab a ≤ t) ∧
      (∀ a, U m ℤ (b a) = ((t : ℤ) + 1 - lab a) • (b' (φ a) : B m ℤ)) ∧
      ∀ i ≤ t, Fintype.card {a // lab a = i} = strMult m i := by
  let u : level m ℤ t →ₗ[ℤ] level m ℤ (t + 1) := (U m ℤ).restrict (fun f hf => U_mem_level hf)
  have hu : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : U m ℤ x.1 = 0 := congrArg Subtype.val hx
    rw [U_eq_zeta x.2] at h1
    have := zeta_inj (univ : Finset (Fin m)) t (t + 1) (by omega) (by simp; omega) x.1
      (level_support x.2) h1
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun S => this S (subset_univ S))
  obtain ⟨ι, κ, hι, hκ, b, b', φ, lab, hlab, hrel, hcard⟩ :=
    abstract_diag u hu (fun j => (lowSub j).map (zetaL m t))
      (fun j => (lowSub j).map (zetaL m (t + 1))) (fun j => level m ℤ j)
      (fun j => (zetaL m t).comp (level m ℤ j).subtype)
      (fun j => (zetaL m (t + 1)).comp (level m ℤ j).subtype)
      (fun j => (t : ℤ) + 1 - j) (t + 1)
      (by simp only [lowSub_zero, Submodule.map_bot])
      (by simp only [lowSub_zero, Submodule.map_bot])
      (fun j => by
        simp only [lowSub_succ, Submodule.map_sup, LinearMap.range_comp, Submodule.range_subtype])
      (fun j => by
        simp only [lowSub_succ, Submodule.map_sup, LinearMap.range_comp, Submodule.range_subtype])
      (fun j hj x => by
        apply Subtype.ext
        simp only [u, LinearMap.restrict_coe_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          zetaL, LinearMap.codRestrict_apply, SetLike.val_smul]
        rw [U_eq_zeta (zeta_mem_level t _), zeta_zeta (by omega) (level_support x.2),
          ← choose_pred_eq (by omega)])
      (fun j hj => by
        show (t : ℤ) + 1 - (j : ℤ) ≠ 0
        omega)
      (fun j _ => isSat_map_zetaL) (fun j _ => isSat_map_zetaL)
      (by
        rw [eq_top_iff]
        intro x _
        rw [mem_map_zetaL_iff]
        refine ⟨x.1, level_le_lowSub x.2, zeta_of_mem_level x.2⟩)
  refine ⟨ι, κ, hι, hκ, b, b', φ, lab, fun a => by have := hlab a; omega, fun a => ?_,
    fun i hi => ?_⟩
  · have := congrArg Subtype.val (hrel a)
    simpa [u] using this
  · rw [hcard i (by omega), finrank_map_zetaL, finrank_map_zetaL,
      finrank_gsub hi (by omega), strMult]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [gsub_zero, finrank_bot]; simp
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [finrank_gsub (by omega) (by omega)]
      simp

end ColouredSand.NumberOfFactors
