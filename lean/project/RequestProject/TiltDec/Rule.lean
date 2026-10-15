module

public import RequestProject.TiltP.Tilt
public import RequestProject.FamDec.Mult

/-!
# `CSG5_the_induction.md`, Part M — the rule as a list, and the formal sums

## Encoding (namespace `ColouredSand.TiltDec`)

* As in the cube's C31 (`FamDec`), a formal sum `Σ_λ c_λ [λ]` is a `List ℕ` containing `c_λ`
  copies of `λ`; the order of the list is irrelevant (lists are compared up to `List.Perm`).
  The paper's `λ` is written `lam` or `l`.
* `IsSimpleWt p l`, `rT p l = (l − p) % p + 1`, `aT p l = (l − p) / p` are those of CSG3
  (`RequestProject/TiltP/Tilt.lean`); all subtractions are natural-number subtractions.
* **(M1)** `VdotP p l` (the weights of `V ⊗ T(l)`) is defined by a chain of `if`s, in this
  order: `l = 0`; simple `l` (with `l ≤ p − 2` or not); non-simple `l` with `r = rT p l` equal to
  `1`, in `[2, p − 2]`, equal to `p − 1` (with `1 ≤ a ≤ p − 2` or not, `a = aT p l`); and `[]`
  otherwise (the case `r = p`, never used).  The cases of (M1) of the file are the theorems
  `VdotP_zero`, `VdotP_simple_small`, `VdotP_simple_large`, `VdotP_r_one`, `VdotP_r_mid`,
  `VdotP_r_top_pos`, `VdotP_r_top_ext`.  In the case `r = p − 1`, `1 ≤ a ≤ p − 2` the third
  weight `μ − 1` is written `l − 2 * rT p l − 1`.
* **(M2)** `LP p 0 = [0]`, `LP p (n + 1) = (LP p n).flatMap (VdotP p)`, and
  `mP p lam n = (LP p n).count lam`.
* **(M3)** `M3`: every `λ ∈ LP p n` has `λ ≤ n` and `λ % 2 = n % 2`.

The arithmetic facts used in Part D (the simplicity, `rT` and `aT` of `lam p r a` and of
`b p − 1`) are also proved here.  None of this file needs `p` prime: the hypotheses are only
`2 ≤ p` or `3 ≤ p` (`3 ≤ p` holds for every prime `p ≠ 2`).
-/

@[expose] public section

namespace ColouredSand.TiltDec

open ColouredSand.TiltP ColouredSand.Blocks

/-! ### Arithmetic of `rT`, `aT` and `IsSimpleWt` -/

/-- Division with remainder for `rT`, `aT`: `p * aT p l + (rT p l − 1) = l − p`. -/
lemma aT_rT_eq (p l : ℕ) : p * aT p l + (rT p l - 1) = l - p := by
  unfold aT rT; rw [Nat.add_sub_cancel]; exact Nat.div_add_mod _ _

/-- `1 ≤ rT p l ≤ p` for `p ≥ 1`. -/
lemma rT_bounds {p : ℕ} (hp : 1 ≤ p) (l : ℕ) : 1 ≤ rT p l ∧ rT p l ≤ p := by
  unfold rT; have := Nat.mod_lt (l - p) (show 0 < p by omega); omega

/-- `lam p r a − p = p a + (r − 1)` for `r ≥ 1`. -/
lemma lam_sub_p {p r : ℕ} (a : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) : lam p r a - p = p * a + (r - 1) := by
  unfold lam; omega

/-- `rT p (lam p r a) = r` for `1 ≤ r ≤ p`. -/
theorem rT_lam {p r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p) : rT p (lam p r a) = r := by
  unfold rT
  rw [lam_sub_p a hr1 (by omega), Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `aT p (lam p r a) = a` for `1 ≤ r ≤ p`. -/
theorem aT_lam {p r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p) : aT p (lam p r a) = a := by
  unfold aT
  rw [lam_sub_p a hr1 (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  simp

/-- `lam p r a` is not simple for `1 ≤ r ≤ p − 1`. -/
theorem not_simple_lam {p r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p - 1) :
    ¬ IsSimpleWt p (lam p r a) := by
  unfold IsSimpleWt
  rintro (h | ⟨hd, -⟩)
  · unfold lam at h; omega
  · have : lam p r a + 1 = p * (a + 1) + r := by unfold lam; rw [Nat.mul_add]; omega
    rw [this] at hd
    have := Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (dvd_mul_right _ _)).mp hd)
    omega

/-- `lam p p (p − 1) = p² + p − 1` is not simple (for `p ≥ 1`). -/
theorem not_simple_lam_top {p : ℕ} (hp : 1 ≤ p) : ¬ IsSimpleWt p (lam p p (p - 1)) := by
  unfold IsSimpleWt lam
  have h : p * (p - 1) + p = p ^ 2 := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]; ring
  rintro (h' | ⟨-, h'⟩) <;> omega

/-- `l ≤ p − 1` is simple. -/
theorem simple_of_le {p l : ℕ} (h : l ≤ p - 1) : IsSimpleWt p l := Or.inl h

/-- `b p − 1` is simple for `1 ≤ b ≤ p`. -/
theorem simple_mul_sub_one {p b : ℕ} (hb1 : 1 ≤ b) (hb : b ≤ p) : IsSimpleWt p (b * p - 1) := by
  right
  have hbp : 1 ≤ b * p := Nat.mul_pos (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.sub_add_cancel hbp]; exact dvd_mul_left _ _
  · have : b * p ≤ p * p := Nat.mul_le_mul_right _ hb
    rw [sq]; omega

/-- A simple `l ≥ p − 1` is `(b + 1) p − 1` for some `b ≤ p − 1` (for `p ≥ 2`). -/
theorem simple_large_form {p l : ℕ} (hp : 2 ≤ p) (hs : IsSimpleWt p l) (hl : p - 1 ≤ l) :
    ∃ b, b ≤ p - 1 ∧ l + 1 = (b + 1) * p := by
  rcases hs with h | ⟨⟨c, hc⟩, hle⟩
  · exact ⟨0, by omega, by omega⟩
  · have hc1 : 1 ≤ c := by rcases c with _ | c <;> simp_all
    have hcp : c ≤ p := by
      by_contra h
      have : p * (p + 1) ≤ p * c := Nat.mul_le_mul_left _ (by omega)
      have : p ^ 2 = p * p := sq p
      have : p * (p + 1) = p * p + p := by ring
      omega
    exact ⟨c - 1, by omega, by rw [hc, Nat.sub_add_cancel hc1, mul_comm]⟩

/-! ### (M1) -/

open Classical in
/-- **(M1)** (`CSG5_the_induction.md`, Part M, (M1)) the weights of `V ⊗ T(l)` as a list:
* `l = 0`: `[1]`;
* `l` simple, `l ≤ p − 2`: `[l + 1, l − 1]`; `l` simple, `l > p − 2`: `[l + 1]`;
* `l` not simple, `r = rT p l`, `a = aT p l`: `r = 1`: `[l + 1, l − 1, l − 1]`;
  `r ≤ p − 2`: `[l + 1, l − 1]`; `r = p − 1`, `1 ≤ a ≤ p − 2`: `[l + 1, l − 1, l − 2r − 1]`;
  `r = p − 1` otherwise: `[l + 1, l − 1]`; otherwise (`r = p`): `[]` (never used). -/
noncomputable def VdotP (p l : ℕ) : List ℕ :=
  if l = 0 then [1]
  else if IsSimpleWt p l then (if l ≤ p - 2 then [l + 1, l - 1] else [l + 1])
  else if rT p l = 1 then [l + 1, l - 1, l - 1]
  else if rT p l ≤ p - 2 then [l + 1, l - 1]
  else if rT p l = p - 1 then
    (if 1 ≤ aT p l ∧ aT p l ≤ p - 2 then [l + 1, l - 1, l - 2 * rT p l - 1] else [l + 1, l - 1])
  else []

/-- **(M1)** `VdotP p 0 = [1]`. -/
theorem VdotP_zero (p : ℕ) : VdotP p 0 = [1] := by
  unfold VdotP; simp

/-- **(M1)** for simple `l` with `1 ≤ l ≤ p − 2`: `VdotP p l = [l + 1, l − 1]`. -/
theorem VdotP_simple_small {p l : ℕ} (hs : IsSimpleWt p l) (hl1 : 1 ≤ l) (hl : l ≤ p - 2) :
    VdotP p l = [l + 1, l - 1] := by
  unfold VdotP; rw [if_neg (by omega), if_pos hs, if_pos hl]

/-- **(M1)** for simple `l` with `p ≤ l` (stated more generally for `p − 1 ≤ l`, `p ≥ 2`):
`VdotP p l = [l + 1]`. -/
theorem VdotP_simple_large {p l : ℕ} (hp : 2 ≤ p) (hs : IsSimpleWt p l) (hl : p - 1 ≤ l) :
    VdotP p l = [l + 1] := by
  unfold VdotP; rw [if_neg (by omega), if_pos hs, if_neg (by omega)]

/-- **(M1)** for non-simple `l` with `rT p l = 1`: `VdotP p l = [l + 1, l − 1, l − 1]`. -/
theorem VdotP_r_one {p l : ℕ} (hs : ¬ IsSimpleWt p l) (hr : rT p l = 1) :
    VdotP p l = [l + 1, l - 1, l - 1] := by
  have : l ≠ 0 := fun h => hs (by subst h; exact Or.inl (Nat.zero_le _))
  unfold VdotP; rw [if_neg this, if_neg hs, if_pos hr]

/-- **(M1)** for non-simple `l` with `2 ≤ rT p l ≤ p − 2`: `VdotP p l = [l + 1, l − 1]`. -/
theorem VdotP_r_mid {p l : ℕ} (hs : ¬ IsSimpleWt p l) (hr1 : 2 ≤ rT p l) (hr : rT p l ≤ p - 2) :
    VdotP p l = [l + 1, l - 1] := by
  have : l ≠ 0 := fun h => hs (by subst h; exact Or.inl (Nat.zero_le _))
  unfold VdotP; rw [if_neg this, if_neg hs, if_neg (by omega), if_pos hr]

/-- **(M1)** for non-simple `l` with `rT p l = p − 1` and `1 ≤ aT p l ≤ p − 2` (`p ≥ 3`):
`VdotP p l = [l + 1, l − 1, μ − 1]` with `μ = l − 2 rT p l`. -/
theorem VdotP_r_top_pos {p l : ℕ} (hp : 3 ≤ p) (hs : ¬ IsSimpleWt p l) (hr : rT p l = p - 1)
    (ha1 : 1 ≤ aT p l) (ha : aT p l ≤ p - 2) :
    VdotP p l = [l + 1, l - 1, l - 2 * rT p l - 1] := by
  have : l ≠ 0 := fun h => hs (by subst h; exact Or.inl (Nat.zero_le _))
  unfold VdotP
  rw [if_neg this, if_neg hs, if_neg (by omega), if_neg (by omega), if_pos hr, if_pos ⟨ha1, ha⟩]

/-- **(M1)** for non-simple `l` with `rT p l = p − 1` and (`aT p l = 0` or `aT p l = p − 1`)
(`p ≥ 3`): `VdotP p l = [l + 1, l − 1]`. -/
theorem VdotP_r_top_ext {p l : ℕ} (hp : 3 ≤ p) (hs : ¬ IsSimpleWt p l) (hr : rT p l = p - 1)
    (ha : aT p l = 0 ∨ aT p l = p - 1) : VdotP p l = [l + 1, l - 1] := by
  have : l ≠ 0 := fun h => hs (by subst h; exact Or.inl (Nat.zero_le _))
  unfold VdotP
  rw [if_neg this, if_neg hs, if_neg (by omega), if_neg (by omega), if_pos hr, if_neg (by omega)]

/-! ### (M2) -/

/-- **(M2)** (`CSG5_the_induction.md`, Part M, (M2)) the formal sums `LP p n = V^{⊗n} · [0]`:
`LP p 0 = [0]`, `LP p (n + 1) = (LP p n).flatMap (VdotP p)`. -/
noncomputable def LP (p : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (LP p n).flatMap (VdotP p)

/-- **(M2)** `LP p 0 = [0]`. -/
theorem LP_zero (p : ℕ) : LP p 0 = [0] := rfl

/-- **(M2)** `LP p (n + 1) = (LP p n).flatMap (VdotP p)`. -/
theorem LP_succ (p n : ℕ) : LP p (n + 1) = (LP p n).flatMap (VdotP p) := rfl

/-- **(M2)** the multiplicity `m_λ(n) = (LP p n).count λ`. -/
noncomputable def mP (p lam n : ℕ) : ℕ := (LP p n).count lam

/-! ### (M3) -/

/-- (M3), auxiliary: every `μ ∈ VdotP p l` has `μ ≤ l + 1` and `μ ≡ l + 1 (mod 2)`
(for every `l`, `p ≥ 2`). -/
theorem mem_VdotP {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    ∀ μ ∈ VdotP p l, μ ≤ l + 1 ∧ μ % 2 = (l + 1) % 2 := by
  intro μ hμ
  have hd := aT_rT_eq p l
  have hmul : p ≤ p * aT p l ∨ aT p l = 0 := by
    rcases Nat.eq_zero_or_pos (aT p l) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_right _ h)
  unfold VdotP at hμ
  split_ifs at hμ with h0 h1 <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ <;>
    omega

/-- **(M3)** (`CSG5_the_induction.md`, Part M, (M3)): every `λ ∈ LP p n` satisfies `λ ≤ n` and
`λ ≡ n (mod 2)` (for every `p ≥ 2`). -/
theorem M3 {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : ∀ lam ∈ LP p n, lam ≤ n ∧ lam % 2 = n % 2 := by
  induction n with
  | zero => intro lam h; simp [LP_zero] at h; omega
  | succ n ih =>
    intro μ hμ
    rw [LP_succ, List.mem_flatMap] at hμ
    obtain ⟨lam, hlam, hμ⟩ := hμ
    have h1 := mem_VdotP hp lam μ hμ
    have h2 := ih lam hlam
    omega

/-- (M4)-type statement (as `FamDec.M4`): `LP p n` is a permutation of
`(List.range (n + 1)).flatMap (fun λ => List.replicate (mP p λ n) λ)` (for `p ≥ 2`). -/
theorem LP_perm_replicate {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    (LP p n).Perm ((List.range (n + 1)).flatMap (fun lam => List.replicate (mP p lam n) lam)) :=
  FamDec.perm_flatMap_replicate (LP p n) (n + 1)
    (fun x hx => Nat.lt_succ_of_le (M3 hp n x hx).1)

/-! ### The cases of (M1) in the range `l ≤ p² + p − 2` -/

/-- `lam p r a = mu p r a + 2 r` and `mu p r a + r + 1 = p (a + 1)` for `r ≤ p − 1`. -/
lemma lam_mu_facts {p r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p - 1) :
    lam p r a = mu p r a + 2 * r ∧ mu p r a + r + 1 = p * (a + 1) := by
  unfold mu lam; constructor
  · omega
  · rw [Nat.mul_add, Nat.mul_one]; omega

/-- The case distinction of (M1)/(D1) for `l ≤ p² + p − 2` (`p ≥ 3`): either `l = 0`, or
`1 ≤ l ≤ p − 2`, or `l + 1 = (b + 1) p` with `b ≤ p − 1`, or `l = lam p r a` with
`1 ≤ r ≤ p − 1`, `a ≤ p − 1` (the non-simple case, with `r = rT p l`, `a = aT p l`). -/
theorem cases_weight {p l : ℕ} (hp : 3 ≤ p) (hl : l ≤ p ^ 2 + p - 2) :
    l = 0 ∨ (1 ≤ l ∧ l ≤ p - 2) ∨ (∃ b, b ≤ p - 1 ∧ l + 1 = (b + 1) * p) ∨
      ∃ r a, 1 ≤ r ∧ r ≤ p - 1 ∧ a ≤ p - 1 ∧ l = lam p r a := by
  by_cases hs : IsSimpleWt p l
  · by_cases h : l ≤ p - 2
    · rcases Nat.eq_zero_or_pos l with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h0, h⟩)
    · exact Or.inr (Or.inr (Or.inl (simple_large_form (by omega) hs (by omega))))
  · right; right; right
    obtain ⟨-, hr1, hrp, ha, htop, hlam⟩ := T3 (by omega) hs (by omega)
    refine ⟨rT p l, aT p l, hr1, ?_, ha, hlam.symm⟩
    by_contra h
    have hr : rT p l = p := by omega
    have := htop hr
    rw [hr, this] at hlam
    have h2 : p * (p - 1) + p = p ^ 2 := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]; ring
    unfold lam at hlam; omega

/-- **(M1)** at `l = lam p 1 a` (`p ≥ 3`): `[l + 1, l − 1, l − 1]`. -/
theorem VdotP_lam_one {p : ℕ} (hp : 3 ≤ p) (a : ℕ) :
    VdotP p (lam p 1 a) = [lam p 1 a + 1, lam p 1 a - 1, lam p 1 a - 1] :=
  VdotP_r_one (not_simple_lam a le_rfl (by omega)) (rT_lam a le_rfl (by omega))

/-- **(M1)** at `l = lam p r a`, `2 ≤ r ≤ p − 2`: `[l + 1, l − 1]`. -/
theorem VdotP_lam_mid {p r : ℕ} (a : ℕ) (hr1 : 2 ≤ r) (hr : r ≤ p - 2) :
    VdotP p (lam p r a) = [lam p r a + 1, lam p r a - 1] :=
  VdotP_r_mid (not_simple_lam a (by omega) (by omega)) (by rw [rT_lam a (by omega) (by omega)]; omega)
    (by rw [rT_lam a (by omega) (by omega)]; omega)

/-- **(M1)** at `l = lam p (p − 1) a`, `1 ≤ a ≤ p − 2` (`p ≥ 3`): `[l + 1, l − 1, μ − 1]` with
`μ = mu p (p − 1) a`. -/
theorem VdotP_lam_top_pos {p a : ℕ} (hp : 3 ≤ p) (ha1 : 1 ≤ a) (ha : a ≤ p - 2) :
    VdotP p (lam p (p - 1) a) =
      [lam p (p - 1) a + 1, lam p (p - 1) a - 1, mu p (p - 1) a - 1] := by
  have hr := rT_lam (p := p) a (by omega : 1 ≤ p - 1) (by omega)
  have haT := aT_lam (p := p) a (by omega : 1 ≤ p - 1) (by omega)
  rw [VdotP_r_top_pos hp (not_simple_lam a (by omega) le_rfl) hr (by omega) (by omega), hr]
  rfl

/-- **(M1)** at `l = lam p (p − 1) a`, `a = 0` or `a = p − 1` (`p ≥ 3`): `[l + 1, l − 1]`. -/
theorem VdotP_lam_top_ext {p a : ℕ} (hp : 3 ≤ p) (ha : a = 0 ∨ a = p - 1) :
    VdotP p (lam p (p - 1) a) = [lam p (p - 1) a + 1, lam p (p - 1) a - 1] := by
  have hr := rT_lam (p := p) a (by omega : 1 ≤ p - 1) (by omega)
  have haT := aT_lam (p := p) a (by omega : 1 ≤ p - 1) (by omega)
  exact VdotP_r_top_ext hp (not_simple_lam a (by omega) le_rfl) hr (by omega)

/-! ### The neighbours `l ± 1` and `μ − 1` of `l = lam p r a` (used in (D1) and (W2)) -/

/-- `lam p r a + 1 = lam p (r + 1) a`. -/
lemma lam_add_one_eq (p r a : ℕ) : lam p r a + 1 = lam p (r + 1) a := by unfold lam; omega

/-- `lam p r a − 1 = lam p (r − 1) a` for `r ≥ 2`. -/
lemma lam_sub_one_eq {p r : ℕ} (a : ℕ) (hr : 2 ≤ r) : lam p r a - 1 = lam p (r - 1) a := by
  unfold lam; omega

/-- `lam p 1 a − 1 = (a + 1) p − 1` is simple for `a ≤ p − 1`. -/
theorem simple_lam_one_pred {p a : ℕ} (ha : a ≤ p - 1) (hp : 1 ≤ p) :
    IsSimpleWt p (lam p 1 a - 1) := by
  have h := simple_mul_sub_one (p := p) (b := a + 1) (by omega) (by omega)
  have e : lam p 1 a - 1 = (a + 1) * p - 1 := by unfold lam; rw [Nat.add_mul]; rw [mul_comm]; omega
  rwa [e]

/-- `lam p (p − 1) a + 1 = (a + 2) p − 1` is simple for `a ≤ p − 2` (`p ≥ 2`). -/
theorem simple_lam_top_succ {p a : ℕ} (hp : 2 ≤ p) (ha : a ≤ p - 2) :
    IsSimpleWt p (lam p (p - 1) a + 1) := by
  have h := simple_mul_sub_one (p := p) (b := a + 2) (by omega) (by omega)
  have e : lam p (p - 1) a + 1 = (a + 2) * p - 1 := by
    unfold lam; rw [Nat.add_mul]; rw [mul_comm]; omega
  rwa [e]

/-- `mu p (p − 1) a − 1 = a p − 1` is simple for `1 ≤ a ≤ p − 1` (`p ≥ 2`). -/
theorem simple_mu_top_pred {p a : ℕ} (hp : 2 ≤ p) (ha1 : 1 ≤ a) (ha : a ≤ p - 1) :
    IsSimpleWt p (mu p (p - 1) a - 1) := by
  have h := simple_mul_sub_one (p := p) (b := a) ha1 (by omega)
  have e : mu p (p - 1) a - 1 = a * p - 1 := by unfold mu lam; rw [mul_comm]; omega
  rwa [e]

/-- `lam p (p − 1) (p − 1) + 1 = lam p p (p − 1)`. -/
lemma lam_top_add_one (p : ℕ) (hp : 1 ≤ p) : lam p (p - 1) (p - 1) + 1 = lam p p (p - 1) := by
  unfold lam; omega

/-- For `l + 1 = (b + 1) p`: `l + 1 = lam p 1 b` and `l − 1 = mu p 1 b`. -/
lemma lam_one_of_simple {p b l : ℕ} (hp : 2 ≤ p) (h : l + 1 = (b + 1) * p) :
    l + 1 = lam p 1 b ∧ l - 1 = mu p 1 b := by
  have e : l + 1 = lam p 1 b := by unfold lam; rw [h, Nat.add_mul, mul_comm]; omega
  refine ⟨e, ?_⟩
  unfold mu; rw [← e]; omega

end ColouredSand.TiltDec
