module

public import RequestProject.Windows.Moves
public import RequestProject.Windows.Hom

/-!
# Part W of `C14_windows_and_theorem_D.md`: the windows (W) and Theorem 4.4

* `windows_gen`: the induction of the proof of (W), for an arbitrary remaining digit list, starting
  from window data of any level `h`.
* **(W)** `W_windows`: the windows after `h` moves (over `ℚ`, for the prefix `ds.take h`).
* **Theorem 4.4** `theorem_4_4`: the final matrix over `ℚ` is `Deficit.Mc` on nested pairs and `0`
  otherwise.
-/

@[expose] public section

namespace Windows

open Finset Deficit Payment Split Dance

/-- The labels of the remaining digits after a digit `false` (used in the proof of (W) of
`C14_windows_and_theorem_D.md`). -/
lemma image_Ids_false (P : Finset ℕ) (h : ℕ) (rest : List Bool) :
    P ∪ (Ids (false :: rest)).image (· + h) = P ∪ (Ids rest).image (· + (h + 1)) := by
  rw [Ids_cons, if_neg (by simp), empty_union, image_image]
  congr 2
  funext t; simp only [Function.comp]; ring

/-- The labels of the remaining digits after a digit `true` (used in the proof of (W) of
`C14_windows_and_theorem_D.md`). -/
lemma image_Ids_true (P : Finset ℕ) (h : ℕ) (rest : List Bool) :
    P ∪ (Ids (true :: rest)).image (· + h) = insert h P ∪ (Ids rest).image (· + (h + 1)) := by
  rw [Ids_cons, if_pos rfl, image_union, image_image, image_singleton, zero_add]
  have : (fun x => x + h) ∘ (fun x => x + 1) = (fun x => x + (h + 1)) := by
    funext t; simp only [Function.comp]; ring
  rw [this]
  ext t; simp only [mem_union, mem_insert, mem_singleton]; tauto

/-- **The induction of the proof of (W)** (*Part W* of `C14_windows_and_theorem_D.md`): if the
data `(p, κ)` on `Fin r`, `r = 2^{|P|}`, are window data of level `h` labelled by `Dlab P`
(every element of `P` being `< h`), and every digit `true` of `rest` sits at a position
`h + t ∈ J`, then the dance data `danceAux rest r p κ` are window data of level
`h + length rest`, labelled by `Dlab (P ∪ (h + I(rest)))`. -/
theorem windows_gen (J : Finset ℕ) (α : ℤ) (i : ℕ) : ∀ (rest : List Bool) (r h : ℕ)
    (P : Finset ℕ) (p : Fin r → ℕ → ℚ) (κ : Fin r → Fin r → ℕ → ℚ), (∀ t ∈ P, t < h) →
    r = 2 ^ P.card → (∀ t, rest[t]? = some true → h + t ∈ J) → WinForm J α i h P p κ →
    WinForm J α i (h + rest.length) (P ∪ (Ids rest).image (· + h))
      (danceAux rest r p κ).1 (danceAux rest r p κ).2
  | [], r, h, P, p, κ, _, _, _, hW => by
    have : Ids ([] : List Bool) = ∅ := by simp [Ids]
    rw [this, image_empty, union_empty, List.length_nil, add_zero]
    exact hW
  | false :: rest, r, h, P, p, κ, hP, hr, hJ, hW => by
    have := windows_gen J α i rest r (h + 1) P (pT p) (κT p κ)
      (fun t ht => by have := hP t ht; omega) hr
      (fun t ht => by
        have := hJ (t + 1) (by simpa using ht)
        rwa [show h + (t + 1) = h + 1 + t by ring] at this)
      (twist_step hP hr hW)
    rw [image_Ids_false, show h + (false :: rest).length = h + 1 + rest.length by
      simp only [List.length_cons]; ring]
    exact this
  | true :: rest, r, h, P, p, κ, hP, hr, hJ, hW => by
    have hhP : h ∉ P := fun hh => lt_irrefl _ (hP h hh)
    have := windows_gen J α i rest (r * 2) (h + 1) (insert h P)
      (relabP (splitIso r).symm (pSp p)) (relabK (splitIso r).symm (κSp p κ))
      (fun t ht => by
        rcases mem_insert.1 ht with e | e
        · omega
        · have := hP t e; omega)
      (by rw [card_insert_of_notMem hhP, pow_succ, hr])
      (fun t ht => by
        have := hJ (t + 1) (by simpa using ht)
        rwa [show h + (t + 1) = h + 1 + t by ring] at this)
      (split_step hP hr (by simpa using hJ 0 rfl) hW)
    rw [image_Ids_true, show h + (true :: rest).length = h + 1 + rest.length by
      simp only [List.length_cons]; ring]
    exact this

/-- The halved data of `σ` are window data of level `0` (the case `h = 0` of the proof of (W) of
`C14_windows_and_theorem_D.md`): `pσ(f) = 2^{α−1}(i + f) = ½ c_0(∅) π_0(f)` for `α ≥ 1`. -/
lemma init_winForm (J : Finset ℕ) (α i : ℕ) (hα : 1 ≤ α) :
    WinForm J (α : ℤ) i 0 ∅ (pσ (A := ℚ) α i) κσ := by
  refine ⟨fun s f => ?_, fun s s' f hlt => ?_⟩
  · have hD : Dlab ∅ s = ∅ := by simp [Dlab]
    obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
    simp only [hD, Rulers.oE_empty, pow_zero, one_mul, add_zero, win, Nat.Ico_succ_singleton,
      prod_singleton, pi0, c, if_true, pσ, zpow_natCast, Nat.add_sub_cancel]
    ring
  · exact absurd hlt (by rw [Subsingleton.elim s s']; exact lt_irrefl _)

/-- **(W) The windows after `h` moves** (*Part W* of `C14_windows_and_theorem_D.md`).  Let
`ds : List Bool`, `α ≥ 1`, `i ∈ ℕ`, `h ≤ length ds`; over `ℚ`, let
`(p^{(h)}, κ^{(h)}) := dance (ds.take h) 1 (pσ α i) κσ` (data on `Fin (1 · 2^{m_h})`) and
`D_s := D(ds.take h, s)`.  Then for every floor `f` and all slots `s' < s`:
`p^{(h)}_s(f) = ½ c_h(∅) · ∏_{d ∈ [2^h f + o(D_s), 2^h f + o(D_s) + 2^h)} π_0(d)`,
`κ^{(h)}_{s s'}(f) = ½ c_h(D_s ∖ D_{s'}) · ∏_{d ∈ [2^h f + o(D_s), 2^h f + o(D_{s'}) + 2^h)} π_0(d)`
if `D_{s'} ⊆ D_s`, and `κ^{(h)}_{s s'}(f) = 0` if `D_{s'} ⊄ D_s`, where `c_h = Deficit.c (I(ds)) h`
and `π_0 = Deficit.pi0 α i`. -/
theorem W_windows (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (h : ℕ) (hh : h ≤ ds.length)
    (f : ℕ) (s s' : Fin (1 * 2 ^ mCount (ds.take h))) :
    (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).1 s f =
        1 / 2 * c (Ids ds) h ∅ *
          ∏ d ∈ Ico (2 ^ h * f + Rulers.oE (Dset (ds.take h) s))
            (2 ^ h * f + Rulers.oE (Dset (ds.take h) s) + 2 ^ h), pi0 α i d ∧
      (s' < s → Dset (ds.take h) s' ⊆ Dset (ds.take h) s →
        (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).2 s s' f =
          1 / 2 * c (Ids ds) h (Dset (ds.take h) s \ Dset (ds.take h) s') *
            ∏ d ∈ Ico (2 ^ h * f + Rulers.oE (Dset (ds.take h) s))
              (2 ^ h * f + Rulers.oE (Dset (ds.take h) s') + 2 ^ h), pi0 α i d) ∧
      (s' < s → ¬ Dset (ds.take h) s' ⊆ Dset (ds.take h) s →
        (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).2 s s' f = 0) := by
  have hG := windows_gen (Ids ds) (α : ℤ) i (ds.take h) 1 0 ∅ (pσ α i) κσ (by simp) (by simp)
    (fun t ht => by
      rw [List.getElem?_take] at ht
      split_ifs at ht
      rw [zero_add]; exact mem_Ids.2 ht)
    (init_winForm _ α i hα)
  have hI : (∅ : Finset ℕ) ∪ (Ids (ds.take h)).image (· + 0) = Ids (ds.take h) := by simp
  rw [hI, zero_add, List.length_take, min_eq_left hh] at hG
  have hc : ∀ x : Fin (1 * 2 ^ mCount (ds.take h)),
      Dset (ds.take h) x = Dlab (Ids (ds.take h)) (Fin.castOrderIso (slots_eq _ 1).symm x) :=
    fun x => Dset_eq_Dlab _ _
  have hlt : ∀ x y : Fin (1 * 2 ^ mCount (ds.take h)), y < x →
      Fin.castOrderIso (slots_eq (ds.take h) 1).symm y <
        Fin.castOrderIso (slots_eq (ds.take h) 1).symm x := fun x y hxy => by simpa using hxy
  refine ⟨?_, fun hss hD => ?_, fun hss hD => ?_⟩
  · rw [hc]; exact hG.1 _ f
  · rw [hc, hc] at hD ⊢
    have := hG.2 _ _ f (hlt s s' hss)
    rw [if_pos hD] at this
    exact this
  · rw [hc, hc] at hD
    have := hG.2 _ _ f (hlt s s' hss)
    rw [if_neg hD] at this
    exact this

/-- **Theorem 4.4 (the final matrix in closed form)** (*Part W* of
`C14_windows_and_theorem_D.md`).  Let `ds : List Bool`, `k := length ds`, `m := mCount ds`,
`I := I(ds)`, `α ≥ 1`, `i ∈ ℕ`.  Over `ℚ`, let `M := Mfin (dance ds 1 (pσ α i) κσ)`, read on
`Fin (2^m)` through the cast `Fin (2^m) ≃ Fin (1 · 2^m)` as in `Dance.proposition_4_3`.  Then for
all `s, s' < 2^m`: `M s s' = Deficit.Mc I k α i (D(ds, s)) (D(ds, s'))` if
`D(ds, s') ⊆ D(ds, s)`, and `M s s' = 0` otherwise. -/
theorem theorem_4_4 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ mCount ds)) :
    (Mfin (dance ds 1 (pσ (A := ℚ) α i) κσ).1 (dance ds 1 (pσ (A := ℚ) α i) κσ).2).submatrix
        (Fin.cast (one_mul (2 ^ mCount ds)).symm) (Fin.cast (one_mul (2 ^ mCount ds)).symm) s s' =
      if Dset ds s' ⊆ Dset ds s then Mc (Ids ds) ds.length (α : ℤ) i (Dset ds s) (Dset ds s')
      else 0 := by
  have hG := windows_gen (Ids ds) (α : ℤ) i ds 1 0 ∅ (pσ α i) κσ (by simp) (by simp)
    (fun t ht => by rw [zero_add]; exact mem_Ids.2 ht) (init_winForm _ α i hα)
  have hI : (∅ : Finset ℕ) ∪ (Ids ds).image (· + 0) = Ids ds := by simp
  rw [hI, zero_add] at hG
  set k := ds.length with hk
  set e : Fin (2 ^ mCount ds) → Fin (slots ds 1) := fun x =>
    Fin.castOrderIso (slots_eq ds 1).symm (Fin.cast (one_mul (2 ^ mCount ds)).symm x) with he
  have hc : ∀ x : Fin (2 ^ mCount ds), Dset ds x = Dlab (Ids ds) (e x) := by
    intro x; rw [Dset_eq_Dlab]; rfl
  have hlt : ∀ x y, e x < e y ↔ x < y := by
    intro x y; rw [Fin.lt_def, Fin.lt_def]; rfl
  have hentry : (Mfin (dance ds 1 (pσ (A := ℚ) α i) κσ).1
      (dance ds 1 (pσ (A := ℚ) α i) κσ).2).submatrix
        (Fin.cast (one_mul (2 ^ mCount ds)).symm) (Fin.cast (one_mul (2 ^ mCount ds)).symm) s s' =
      if s = s' then 2 * (danceAux ds 1 (pσ α i) κσ).1 (e s) 0
      else if s' < s then 2 * (danceAux ds 1 (pσ α i) κσ).2 (e s) (e s') 0 else 0 := by
    simp only [Matrix.submatrix_apply, Mfin, dance, relabP, relabK]
    congr 1
    simp [Fin.ext_iff]
  rw [hentry, hc, hc]
  have hB1 : ∀ Δ : Finset ℕ, c (Ids ds) k Δ =
      -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ k) * 2 ^ (Rulers.oE Δ) * (a (Ids ds) k Δ : ℚ) :=
    fun Δ => B1_rescaling _ _ _
  have hz : ∀ Δ : Finset ℕ, (2 : ℚ) ^ ((1 : ℤ) - 2 ^ k + (Rulers.oE Δ : ℕ)) =
      (2 : ℚ) ^ ((1 : ℤ) - 2 ^ k) * 2 ^ (Rulers.oE Δ) := by
    intro Δ; rw [zpow_add₀ (two_ne_zero), zpow_natCast]
  have hv : ∀ x, ((e x : Fin _) : ℕ) = x := fun x => by simp [he]
  have hb : ∀ x, ((e x : Fin _) : ℕ) < 2 ^ (Ids ds).card := fun x => by
    rw [hv, card_Ids]; exact x.isLt
  by_cases h1 : s = s'
  · subst h1
    rw [if_pos rfl, if_pos (subset_refl _), hG.1, Mc, sdiff_self, bot_eq_empty, hz, hB1]
    simp only [win, mul_zero, zero_add]
    ring
  rw [if_neg h1]
  by_cases h2 : s' < s
  · rw [if_pos h2, hG.2 _ _ 0 ((hlt s' s).2 h2)]
    by_cases h3 : Dlab (Ids ds) (e s') ⊆ Dlab (Ids ds) (e s)
    · rw [if_pos h3, if_pos h3, Mc, hz, hB1]
      simp only [win, mul_zero, zero_add]
      ring
    · rw [if_neg h3, if_neg h3]; ring
  · rw [if_neg h2, if_neg]
    intro h3
    have hle := Dlab_mono _ _ _ (hb s') (hb s) h3
    rw [hv, hv] at hle
    exact h2 (lt_of_le_of_ne (Fin.le_def.2 hle) (Ne.symm h1))

end Windows
