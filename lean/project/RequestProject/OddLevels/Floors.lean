module

public import RequestProject.OddLevels.Basic
public import RequestProject.OddDance.Lattice

/-!
# `CSI9_last_level_and_floors.md`, Part G (G1) — the floors of `danceL`

Namespace `ColouredSand.OddTwist`. Reuses CSI6's `danceL` and its defining equations
`danceL_lt`, `danceL_d0_zero`, `danceL_d0_pos` (`RequestProject/OddDance/`), CSI1's `twist`/`twWt`
and CSI3's `psi`/`psiWt`, and C18's condition (W) (`IsDP.W_F`).

## Encoding

* `λ` is written `l`; `d₀ = (l + 1) % p`, `b = (l + 1) / p − 1` (as in CSI6).
* `flL p l i := ((l − wt i) / 2).toNat` (integer division in `ℤ`, then `Int.toNat`); by
  `G1_parity` and `G1_nonneg` the division is exact and the argument of `toNat` is `≥ 0`, so this
  is the file's `(λ − wt i)/2`. The main identity is `wt_danceL`: `wt i = λ − 2 · flL i`.
* "`Fd 1` sends floor `φ` to floor `φ + 1`" (`G1_Fd`): every nonzero coordinate `j` of
  `Fd 1 (δ_i)` has `flL j = flL i + 1`; equivalently (`G1_Fd_floor`) `Fd 1` maps a vector supported
  on floor `φ` to a vector supported on floor `φ + 1`.
* The identification of index types of CSI6 (L1) is the cast along the defining equation of
  `danceL`: `idxTw p l h hd : (danceL p l).ι ≃ Fin p × (danceL p b).ι` (case `d₀ = 0`, from
  `danceL_d0_zero`) and `idxPsi p l h hd : (danceL p l).ι ≃ Bool × Fin p × (danceL p b).ι` (case
  `d₀ ≥ 1`, from `danceL_d0_pos`); the condition `λ ≥ p − 1` is written `¬ l + 1 < p`, as in CSI6.
  For `x = (j, i)` resp. `(b, j, i)` (`false` = A, `true` = C), the element of `(danceL p l).ι` is
  `(idxTw ..).symm x` resp. `(idxPsi ..).symm x`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

variable (p : ℕ) [Fact p.Prime]

/-- **The floor of `danceL p λ`** (Part G (G1) of `CSI9_last_level_and_floors.md`):
`flL p λ i = (λ − wt i)/2`. -/
def flL (l : ℕ) (i : (danceL p l).ι) : ℕ := (((l : ℤ) - (danceL p l).wt i) / 2).toNat

/-- Weights of the form `l − 2 f` (auxiliary predicate for (G1)). -/
def WtForm {A : Type*} [CommRing A] (M : DPLattice A) (l : ℕ) : Prop :=
  ∀ i, ∃ f : ℕ, M.wt i = (l : ℤ) - 2 * f

lemma wtForm_delta (l : ℕ) : WtForm (delta ℤ_[p] l) l :=
  fun r => ⟨r.val, rfl⟩

lemma wtForm_twist {N : DPLattice ℤ_[p]} {b : ℕ} (h : WtForm N b) :
    WtForm (twist p N) (p * b + p - 1) := by
  rintro ⟨j, i⟩
  obtain ⟨f, hf⟩ := h i
  refine ⟨p * f + j, ?_⟩
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  change twWt p N (j, i) = _
  simp only [twWt, hf]
  push_cast [Nat.sub_add_cancel (show 1 ≤ p * b + p by nlinarith), show 1 ≤ p * b + p by nlinarith]
  ring

lemma wtForm_psi {N : DPLattice ℤ_[p]} {b : ℕ} (h : WtForm N b) (d : ℕ) (hd1 : 1 ≤ d)
    (hd2 : d ≤ p - 1) : WtForm (psi p N d hd1 hd2) (d + p * (b + 1) - 1) := by
  rintro ⟨c, j, i⟩
  obtain ⟨f, hf⟩ := h i
  refine ⟨p * f + cond c d 0 + j, ?_⟩
  change psiWt p N d (c, j, i) = _
  simp only [psiWt, hf]
  have : 1 ≤ d + p * (b + 1) := by omega
  push_cast [this]
  cases c <;> simp <;> ring

lemma wtForm_floor {A : Type*} [CommRing A] {M : DPLattice A} {l : ℕ} {i : M.ι} {f : ℕ}
    (h : M.wt i = (l : ℤ) - 2 * f) : (((l : ℤ) - M.wt i) / 2).toNat = f := by
  rw [h, sub_sub_cancel, Int.mul_ediv_cancel_left _ (by norm_num), Int.toNat_natCast]

/-- The arithmetic of `λ ≥ p − 1`: `λ = d₀ + p (b + 1) − 1` with `d₀ = (λ+1) % p`,
`b = (λ+1)/p − 1`. -/
lemma l_eq_digits {l : ℕ} (h : ¬ l + 1 < p) :
    l = (l + 1) % p + p * ((l + 1) / p - 1 + 1) - 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : 1 ≤ (l + 1) / p := (Nat.one_le_div_iff hp).2 (by omega)
  rw [Nat.sub_add_cancel h1]
  have := Nat.mod_add_div (l + 1) p
  omega

lemma wtForm_danceL (l : ℕ) : WtForm (danceL p l) l := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    by_cases h : l + 1 < p
    · rw [danceL_lt p h]; exact wtForm_delta p l
    · have hb := ih _ (b_lt hp (by omega))
      have hl := l_eq_digits p h
      by_cases hd : (l + 1) % p = 0
      · rw [danceL_d0_zero p h hd]
        have := wtForm_twist p hb
        rw [hd, zero_add] at hl
        convert this using 1
      · have hm := Nat.mod_lt (l + 1) (show 0 < p by omega)
        rw [danceL_d0_pos p h (by omega) (by omega)]
        have := wtForm_psi p hb ((l + 1) % p) (by omega) (by omega)
        convert this using 1

/-- **(G1)**, the main identity (Part G (G1) of `CSI9_last_level_and_floors.md`):
`wt i = λ − 2 · flL p λ i` for every basis vector `i` of `danceL p λ`. -/
theorem wt_danceL (l : ℕ) (i : (danceL p l).ι) :
    (danceL p l).wt i = (l : ℤ) - 2 * flL p l i := by
  obtain ⟨f, hf⟩ := wtForm_danceL p l i
  rw [flL, wtForm_floor hf, hf]

/-- **(G1)** (Part G of `CSI9_last_level_and_floors.md`): `wt i ≡ λ (mod 2)`. -/
theorem G1_parity (l : ℕ) (i : (danceL p l).ι) : (danceL p l).wt i ≡ (l : ℤ) [ZMOD 2] := by
  rw [wt_danceL, Int.ModEq, Int.sub_emod, Int.mul_emod_right]
  simp

/-- **(G1)** (Part G of `CSI9_last_level_and_floors.md`): `0 ≤ (λ − wt i)/2`, and `2` divides
`λ − wt i` (so `flL p λ i` is exactly `(λ − wt i)/2`). -/
theorem G1_nonneg (l : ℕ) (i : (danceL p l).ι) :
    0 ≤ ((l : ℤ) - (danceL p l).wt i) / 2 ∧ (2 : ℤ) ∣ (l : ℤ) - (danceL p l).wt i ∧
      ((flL p l i : ℕ) : ℤ) = ((l : ℤ) - (danceL p l).wt i) / 2 := by
  rw [wt_danceL]
  simp

/-- **(G1)** (Part G of `CSI9_last_level_and_floors.md`): `Fd 1` of `danceL p λ` sends floor `φ`
to floor `φ + 1`: every nonzero coordinate `j` of `F δ_i` has `flL j = flL i + 1`. -/
theorem G1_Fd (l : ℕ) (i j : (danceL p l).ι) (h : (danceL p l).Fd 1 (Pi.single i 1) j ≠ 0) :
    flL p l j = flL p l i + 1 := by
  have hw : (danceL p l).wt j = (danceL p l).wt i - 2 * (1 : ℕ) := by
    by_contra hne
    exact h ((danceL p l).isDP.W_F i 1 j hne)
  rw [wt_danceL, wt_danceL] at hw
  push_cast at hw
  omega

/-- **(G1)**, vector form (Part G of `CSI9_last_level_and_floors.md`): if `v` is supported on
the floor `φ` (its coordinates off `{flL = φ}` vanish) then `Fd 1 v` is supported on the floor
`φ + 1`. -/
theorem G1_Fd_floor (l φ : ℕ) (v : (danceL p l).ι → ℤ_[p])
    (hv : ∀ i, flL p l i ≠ φ → v i = 0) (j : (danceL p l).ι) (hj : flL p l j ≠ φ + 1) :
    (danceL p l).Fd 1 v j = 0 := by
  have hv' : InWt (danceL p l).wt ((l : ℤ) - 2 * φ) v := by
    intro i hi
    refine hv i fun h => hi ?_
    rw [wt_danceL, h]
  have := (danceL p l).isDP.inWt_Fd 1 hv' j
  refine this fun h => hj ?_
  rw [wt_danceL] at h
  push_cast at h
  omega

/-! ### The recursive description -/

/-- The identification of index types of CSI6 (L1), case `λ + 1 < p` (Part G (G1) of
`CSI9_last_level_and_floors.md`): the cast along `danceL_lt`, `(danceL p λ).ι ≃ Fin (λ + 1)`. -/
def idxDelta (l : ℕ) (h : l + 1 < p) : (danceL p l).ι ≃ Fin (l + 1) :=
  Equiv.cast (congrArg DPLattice.ι (danceL_lt p h))

lemma wt_cast_delta {M : DPLattice ℤ_[p]} {l : ℕ} (h : M = delta ℤ_[p] l) (r : Fin (l + 1)) :
    M.wt ((Equiv.cast (congrArg DPLattice.ι h)).symm r) = weylWt l r := by
  subst h; rfl

/-- **(G1)**, base case (Part G of `CSI9_last_level_and_floors.md`, and the floor
`fl e_s = s` of Part L): for `λ + 1 < p`, `danceL p λ = Δ(λ)` and `flL e_r = r`. -/
theorem G1_delta (l : ℕ) (h : l + 1 < p) (r : Fin (l + 1)) :
    flL p l ((idxDelta p l h).symm r) = r.val := by
  apply wtForm_floor
  exact wt_cast_delta p (danceL_lt p h) r

/-- The identification of index types of CSI6 (L1), case `d₀ = 0` (Part G (G1) of
`CSI9_last_level_and_floors.md`): the cast along `danceL_d0_zero`. -/
def idxTw (l : ℕ) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) :
    (danceL p l).ι ≃ Fin p × (danceL p ((l + 1) / p - 1)).ι :=
  Equiv.cast (congrArg DPLattice.ι (danceL_d0_zero p h hd))

lemma mod_le_pred (l : ℕ) : (l + 1) % p ≤ p - 1 := by
  have := Nat.mod_lt (l + 1) (Fact.out : p.Prime).pos
  omega

/-- The identification of index types of CSI6 (L1), case `d₀ ≥ 1` (Part G (G1) of
`CSI9_last_level_and_floors.md`): the cast along `danceL_d0_pos`. -/
def idxPsi (l : ℕ) (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) :
    (danceL p l).ι ≃ Bool × Fin p × (danceL p ((l + 1) / p - 1)).ι :=
  Equiv.cast (congrArg DPLattice.ι (danceL_d0_pos p h hd (mod_le_pred p l)))

lemma wt_cast_twist {M N : DPLattice ℤ_[p]} (h : M = twist p N) (x : Fin p × N.ι) :
    M.wt ((Equiv.cast (congrArg DPLattice.ι h)).symm x) = twWt p N x := by
  subst h; rfl

lemma wt_cast_psi {M N : DPLattice ℤ_[p]} {d : ℕ} {hd1 : 1 ≤ d} {hd2 : d ≤ p - 1}
    (h : M = psi p N d hd1 hd2) (x : Bool × Fin p × N.ι) :
    M.wt ((Equiv.cast (congrArg DPLattice.ι h)).symm x) = psiWt p N d x := by
  subst h; rfl

lemma wt_idxTw (l : ℕ) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0)
    (x : Fin p × (danceL p ((l + 1) / p - 1)).ι) :
    (danceL p l).wt ((idxTw p l h hd).symm x) = twWt p (danceL p ((l + 1) / p - 1)) x :=
  wt_cast_twist p (danceL_d0_zero p h hd) x

lemma wt_idxPsi (l : ℕ) (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p)
    (x : Bool × Fin p × (danceL p ((l + 1) / p - 1)).ι) :
    (danceL p l).wt ((idxPsi p l h hd).symm x) =
      psiWt p (danceL p ((l + 1) / p - 1)) ((l + 1) % p) x :=
  wt_cast_psi p (danceL_d0_pos p h hd (mod_le_pred p l)) x

/-- **(G1)**, recursive description, twist (Part G of `CSI9_last_level_and_floors.md`): for
`λ ≥ p − 1` with `d₀ = 0`, `flL (j, i) = p · flL i + j` (with `flL i` the floor of
`danceL p b`, `b = (λ+1)/p − 1`). -/
theorem G1_twist (l : ℕ) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) (j : Fin p)
    (i : (danceL p ((l + 1) / p - 1)).ι) :
    flL p l ((idxTw p l h hd).symm (j, i)) = p * flL p ((l + 1) / p - 1) i + j := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  apply wtForm_floor
  rw [wt_idxTw, twWt, wt_danceL]
  have hl := l_eq_digits p h
  rw [hd, zero_add] at hl
  have hl' : (l : ℤ) = p * ((l + 1) / p - 1 : ℕ) + p - 1 := by
    have : 1 ≤ p * ((l + 1) / p - 1 + 1) := by nlinarith
    conv_lhs => rw [hl]
    push_cast [this]; ring
  rw [hl']
  push_cast
  ring

/-- **(G1)**, recursive description, split (Part G of `CSI9_last_level_and_floors.md`): for
`λ ≥ p − 1` with `d₀ ≥ 1`, `flL (A, j, i) = p · flL i + j` and `flL (C, j, i) = p · flL i + d₀ + j`
(`false` = A, `true` = C). -/
theorem G1_psi (l : ℕ) (h : ¬ l + 1 < p) (hd : 1 ≤ (l + 1) % p) (j : Fin p)
    (i : (danceL p ((l + 1) / p - 1)).ι) :
    flL p l ((idxPsi p l h hd).symm (false, j, i)) = p * flL p ((l + 1) / p - 1) i + j ∧
    flL p l ((idxPsi p l h hd).symm (true, j, i)) =
      p * flL p ((l + 1) / p - 1) i + (l + 1) % p + j := by
  have hl := l_eq_digits p h
  have hl' : (l : ℤ) = ((l + 1) % p : ℕ) + p * (((l + 1) / p - 1 : ℕ) + 1) - 1 := by
    conv_lhs => rw [hl]
    push_cast [show 1 ≤ (l + 1) % p + p * ((l + 1) / p - 1 + 1) by omega]; ring
  constructor
  · apply wtForm_floor
    rw [wt_idxPsi, psiWt, wt_danceL, hl']
    push_cast
    ring
  · apply wtForm_floor
    rw [wt_idxPsi, psiWt, wt_danceL, hl']
    push_cast
    rw [if_pos rfl]
    ring

end ColouredSand.OddTwist
