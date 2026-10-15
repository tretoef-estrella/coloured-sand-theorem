module

public import RequestProject.ThmG.TheoremG

/-!
# `CSG7_theorem_G.md`, Part F — the Glue Theorem (Theorem F), `m ≤ 2p − 2`

Namespace `ColouredSand.ThmG`.

## Encodings

* `betaN n l = (TiltDec.betaCG n l).toNat` is the Clebsch–Gordan count `β(n, l)` (CSG5 (W3)),
  as a natural number.
* `Ac p q c m l = chA p q c ((m − l)/2) l`, i.e.
  `A_c(m, λ) = Σ_{r=(m−λ)/2}^{(m+λ)/2} (e + v_p(c + r))` with Mathlib's `v_p(0) = 0`.
* `FPiece p q c m l` is the contribution of the weight `l` to the list of exponents of the Glue
  Theorem, by the case split of the file (`β' = betaN m (2p − 2 − l)` if `l ≤ p − 2` and `0` if
  `l = p − 1`; `δ = [c = 0 ∧ l = m]`), and `FList p q c m` is the flatMap of `FPiece p q c m` over
  the `l ∈ List.range (m + 1)` with `l % 2 = m % 2` (a `List.filter`).
* Lists of exponents are compared up to `List.Perm` (equality of multisets); the group
  `⊕_{e ∈ L} ℤ/p^e` is `(i : Fin L.length) → ZMod (p ^ L.get i)` (`= ExpGrp p L`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

open ColouredSand.Splitting
open ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks ColouredSand.BlockOp

/-- Part F of `CSG7_theorem_G.md`: `betaN n l = β(n, l)` as a natural number,
`(TiltDec.betaCG n l).toNat`. -/
def betaN (n l : ℕ) : ℕ := (betaCG n l).toNat

variable (p : ℕ) [Fact p.Prime]

/-- Part F of `CSG7_theorem_G.md`: `Ac p q c m l = A_c(m, λ) = chA p q c ((m − l)/2) l`. -/
def Ac (q c m l : ℕ) : ℕ := chA p q c ((m - l) / 2) l

/-- Part F of `CSG7_theorem_G.md`: the contribution of the weight `l` to `FList`:
* if `l ≤ p − 1`: `replicate (betaN m l − β' − δ) (Ac m l)`;
* if `p ≤ l` and `c = 0 ∧ l = m`: `replicate (betaN m l) (Ac m (2p−2−l) + 1) ++
  replicate (betaN m l − 1) (Ac m l − 1)`;
* if `p ≤ l` otherwise: `(replicate (betaN m l) [Ac m l − 1, Ac m (2p−2−l) + 1]).flatten`. -/
def FPiece (q c m l : ℕ) : List ℕ :=
  if l ≤ p - 1 then
    List.replicate (betaN m l - (if l ≤ p - 2 then betaN m (2 * p - 2 - l) else 0) -
      (if c = 0 ∧ l = m then 1 else 0)) (Ac p q c m l)
  else if c = 0 ∧ l = m then
    List.replicate (betaN m l) (Ac p q c m (2 * p - 2 - l) + 1) ++
      List.replicate (betaN m l - 1) (Ac p q c m l - 1)
  else
    (List.replicate (betaN m l) [Ac p q c m l - 1, Ac p q c m (2 * p - 2 - l) + 1]).flatten

/-- Part F of `CSG7_theorem_G.md`: `FList p q c m` is the flatMap of `FPiece p q c m` over the
`l ∈ List.range (m + 1)` with `l % 2 = m % 2`. -/
def FList (q c m : ℕ) : List ℕ :=
  ((List.range (m + 1)).filter (fun l => l % 2 = m % 2)).flatMap (FPiece p q c m)

variable {p}

/-! ### Auxiliary facts in the range `l ≤ 2p − 2` -/

/-- For `p ≤ l ≤ 2p − 2`, `l` is not simple (auxiliary for (F1)). -/
lemma not_simple_of_range {l : ℕ} (h1 : p ≤ l) (h2 : l ≤ 2 * p - 2) : ¬ IsSimpleWt p l := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rintro (h | ⟨⟨t, ht⟩, -⟩)
  · omega
  · rcases Nat.lt_or_ge t 2 with h | h
    · have : p * t ≤ p * 1 := Nat.mul_le_mul_left p (by omega)
      omega
    · have : p * 2 ≤ p * t := Nat.mul_le_mul_left p h
      omega

/-- For `p ≤ l ≤ 2p − 2`, `rT p l = l − p + 1` (auxiliary for (F1)). -/
lemma rT_of_range {l : ℕ} (h1 : p ≤ l) (h2 : l ≤ 2 * p - 2) : rT p l = l - p + 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  unfold rT; rw [Nat.mod_eq_of_lt (by omega)]

/-- For `p ≤ l ≤ 2p − 2`, `aT p l = 0` (auxiliary for (F1)). -/
lemma aT_of_range {l : ℕ} (h1 : p ≤ l) (h2 : l ≤ 2 * p - 2) : aT p l = 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  unfold aT; exact Nat.div_eq_of_lt (by omega)

omit [Fact p.Prime] in
/-- A non-simple `l` is `≥ p` (auxiliary for (F1)). -/
lemma le_of_not_simple {l : ℕ} (hs : ¬ IsSimpleWt p l) : p ≤ l := by
  by_contra h; exact hs (Or.inl (by omega))

/-- `betaN` vanishes beyond `n` (auxiliary for (F1)). -/
lemma betaN_of_lt {n l : ℕ} (h : n < l) : betaN n l = 0 := by
  unfold betaN betaCG; rw [if_neg (by omega)]; rfl

/-- `betaN n n = 1` (auxiliary for (F1)). -/
lemma betaN_self (n : ℕ) : betaN n n = 1 := by
  unfold betaN betaCG; simp

/-- **Multiplicities in the range `m ≤ 2p − 2`**, weights `l ≥ p − 1`: `mP p l m = β(m, l)`
(auxiliary for (F1), from CSG5 `W4_of_no_plus`). -/
lemma mP_of_ge (hp3 : 3 ≤ p) {m l : ℕ} (hm : m ≤ 2 * p - 2) (hl : p - 1 ≤ l) :
    mP p l m = betaN m l := by
  have hn : m ≤ p ^ 2 + p - 1 := by
    have : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p (by omega)
    omega
  have h := W4_of_no_plus hp3 hn (l := l) (fun m' hm' hs => by
    have h1 := le_of_not_simple hs
    rw [rT_of_range h1 (by omega)]
    omega)
  unfold betaN; rw [← h]; rfl

/-- **Multiplicities in the range `m ≤ 2p − 2`**, weights `l ≤ p − 2`:
`mP p l m = β(m, l) − β(m, 2p − 2 − l)` (auxiliary for (F1), from CSG5 `W4_of_plus` and
`W4_of_no_plus`; here `l⁺ = 2p − 2 − l`). -/
lemma mP_of_le (hp3 : 3 ≤ p) {m l : ℕ} (hm : m ≤ 2 * p - 2) (hl : l ≤ p - 2) :
    mP p l m = betaN m l - betaN m (2 * p - 2 - l) := by
  have hn : m ≤ p ^ 2 + p - 1 := by
    have : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p (by omega)
    omega
  by_cases hplus : 2 * p - 2 - l ≤ m
  · have hs := not_simple_of_range (p := p) (l := 2 * p - 2 - l) (by omega) (by omega)
    have h := W4_of_plus hp3 hn hs hplus (l := l) (by
      rw [rT_of_range (by omega) (by omega)]; omega)
    have h2 := mP_of_ge hp3 hm (l := 2 * p - 2 - l) (by omega)
    rw [h2] at h
    have h3 : betaN m l = mP p l m + betaN m (2 * p - 2 - l) := by
      unfold betaN; rw [← h]; exact_mod_cast rfl
    omega
  · have h := W4_of_no_plus hp3 hn (l := l) (fun m' hm' hs => by
      have h1 := le_of_not_simple hs
      rw [rT_of_range h1 (by omega)]
      omega)
    rw [betaN_of_lt (l := 2 * p - 2 - l) (by omega)]
    unfold betaN; rw [← h]; rfl

/-! ### The numbers of Lemma 8 for `a = 0` -/

/-- **Lemma 8's numbers when `a = 0`** (auxiliary for (F1); the paper: «When `a + 1 < p` one has
`x = E₁₂`»): for `1 ≤ v_p(q)` and `1 ≤ r ≤ p − 1`, `x = E₁₂ = A' + 1`, `min E₁₂ E₂₂ = A' + 1`
and `y = A − 1`. -/
lemma blk_a_zero {q : ℕ} (hq : 1 ≤ padicValNat p q) (c k : ℕ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ p - 1) :
    blkX p q c k r 0 = blkA' p q c k r 0 + 1 ∧
      min (E12 p q c k r 0) (E22 p q c k r 0) = blkA' p q c k r 0 + 1 ∧
      blkY p q c k r 0 = blkA p q c k r 0 - 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlam : lam p r 0 = p - 1 + r := by simp [lam]
  have hmu : r + mu p r 0 = p - 1 := by simp [mu, lam]; omega
  have hτ : blkTau p 0 = 1 := by unfold blkTau; rw [if_neg (by omega)]
  have hA' : blkA' p q c k r 0 = ∑ t ∈ Finset.Ico r p, vt p q c k t := by
    unfold blkA'; rw [hmu, Icc_eq_Ico_succ]; congr 2; omega
  have hα : blkAlpha p q c k r 0 = ∑ t ∈ Finset.Ico p (lam p r 0 + 1), vt p q c k t := by
    unfold blkAlpha; rw [Icc_eq_Ico_succ, zero_add, one_mul]
  have hsplit1 := Finset.sum_range_add_sum_Ico (vt p q c k) (show r ≤ p by omega)
  have hsplit2 := Finset.sum_range_add_sum_Ico (vt p q c k) (show p ≤ lam p r 0 + 1 by omega)
  have hA : blkA p q c k r 0 = ∑ t ∈ Finset.range r, vt p q c k t +
      ∑ t ∈ Finset.Ico r p, vt p q c k t +
      ∑ t ∈ Finset.Ico p (lam p r 0 + 1), vt p q c k t := by
    rw [hsplit1, hsplit2]; rfl
  have hS0 := card_le_sum_vt hq c k (Finset.range r)
  have hα1 := card_le_sum_vt hq c k (Finset.Ico p (lam p r 0 + 1))
  rw [Finset.card_range] at hS0
  rw [Nat.card_Ico] at hα1
  have hE11 : E11 p q c k r 0 = blkA p q c k r 0 - blkAlpha p q c k r 0 - 0 := rfl
  have hE12 : E12 p q c k r 0 = blkA' p q c k r 0 - 0 + blkTau p 0 := rfl
  have hE22 : E22 p q c k r 0 = blkA' p q c k r 0 - 0 + blkAlpha p q c k r 0 := rfl
  unfold blkY blkX
  rw [hE11, hE12, hE22, hA, hA', hα, hτ]
  generalize ∑ t ∈ Finset.range r, vt p q c k t = S0 at *
  generalize ∑ t ∈ Finset.Ico r p, vt p q c k t = S1 at *
  generalize ∑ t ∈ Finset.Ico p (lam p r 0 + 1), vt p q c k t = S2 at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

omit [Fact p.Prime] in
/-- `A = blkA p q c k r 0` is `chA p q c k l` for `l = lam p r 0` (auxiliary for (F1)). -/
lemma blkA_eq_chA (q c k r a : ℕ) : blkA p q c k r a = chA p q c k (lam p r a) := rfl

omit [Fact p.Prime] in
/-- `A' = blkA' p q c k r a` is `chA p q c (k + r) μ` for `μ = mu p r a` (auxiliary for (F1)). -/
lemma blkA'_eq_chA (q c k r a : ℕ) : blkA' p q c k r a = chA p q c (k + r) (mu p r a) := by
  unfold blkA' chA
  rw [Icc_eq_Ico_succ, Finset.sum_Ico_eq_sum_range, show r + mu p r a + 1 - r = mu p r a + 1 by omega]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold vt; congr 2; omega

/-! ### (F1) -/

/-- `(replicate n a).flatMap f = (replicate n (f a)).flatten` (auxiliary). -/
lemma flatMap_replicate' {α β : Type*} (f : α → List β) (a : α) :
    (n : ℕ) → (List.replicate n a).flatMap f = (List.replicate n (f a)).flatten
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.flatMap_cons, flatMap_replicate' f a n, List.replicate_succ,
        List.flatten_cons]

/-- `(replicate n [x]).flatten = replicate n x` (auxiliary). -/
lemma flatten_replicate_single {α : Type*} (x : α) :
    (n : ℕ) → (List.replicate n [x]).flatten = List.replicate n x
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.flatten_cons, flatten_replicate_single x n]; rfl

/-- `(replicate n []).flatten = []` (auxiliary). -/
lemma flatten_replicate_nil {α : Type*} : (n : ℕ) → (List.replicate n ([] : List α)).flatten = []
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, flatten_replicate_nil n]; rfl

/-- `(replicate n [x, y]).flatten ~ (replicate n [y, x]).flatten` (auxiliary). -/
lemma flatten_replicate_swap {α : Type*} (x y : α) :
    (n : ℕ) → (List.replicate n [x, y]).flatten.Perm (List.replicate n [y, x]).flatten
  | 0 => List.Perm.refl _
  | n + 1 => by
      rw [List.replicate_succ, List.flatten_cons, List.replicate_succ, List.flatten_cons]
      exact List.Perm.append (List.Perm.swap y x []) (flatten_replicate_swap x y n)

/-- Dropping the elements where `f` is empty from a flatMap (auxiliary). -/
lemma perm_flatMap_filter {α β : Type*} (P : α → Bool) (f g : α → List β) :
    (L : List α) → (∀ x ∈ L, P x → (f x).Perm (g x)) → (∀ x ∈ L, ¬ P x → f x = []) →
      (L.flatMap f).Perm ((L.filter P).flatMap g)
  | [], _, _ => List.Perm.refl _
  | a :: L, h1, h2 => by
      have ih := perm_flatMap_filter P f g L (fun x hx => h1 x (List.mem_cons_of_mem a hx))
        (fun x hx => h2 x (List.mem_cons_of_mem a hx))
      rw [List.flatMap_cons, List.filter_cons]
      by_cases hP : P a
      · rw [if_pos hP, List.flatMap_cons]
        exact List.Perm.append (h1 a (List.mem_cons_self) hP) ih
      · rw [if_neg hP, h2 a (List.mem_cons_self) hP, List.nil_append]
        exact ih

/-- **(F1)** of `CSG7_theorem_G.md`: for `p ≠ 2`, `1 ≤ v_p(q)` and `m ≤ 2p − 2`, the list of
exponents of Theorem G is a permutation of that of the Glue Theorem:
`(gTorList p q c m).Perm (FList p q c m)`.
In this range every non-simple `l ≤ m` has `aT p l = 0`, `rT p l = l − p + 1`,
`μ = 2p − 2 − l`; Lemma 8's `x = E₁₂ = A' + 1` and `y = A − 1` (`blk_a_zero`), with
`A' = Ac p q c m (2p − 2 − l)`; the multiplicities come from CSG5 `W4` (`mP_of_ge`, `mP_of_le`). -/
theorem F1 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q) (hm : m ≤ 2 * p - 2) :
    (gTorList p q c m).Perm (FList p q c m) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  set g := fun l => blkList p q c ((m - l) / 2) l with hg
  have h0 : (gTorList p q c m).Perm
      ((List.range (m + 1)).flatMap fun l => (List.replicate (mP p l m) l).flatMap g) := by
    unfold gTorList
    rw [← List.flatMap_assoc]
    exact (LP_perm_replicate hp m).flatMap_right g
  refine h0.trans (perm_flatMap_filter _ _ _ _ (fun l hl hP => ?_) (fun l hl hP => ?_))
  · -- `l` of the parity of `m`
    have hlm : l ≤ m := Nat.lt_succ_iff.1 (List.mem_range.1 hl)
    have hpar : l % 2 = m % 2 := by simpa using hP
    rw [flatMap_replicate']
    have hck : c + (m - l) / 2 = 0 ↔ c = 0 ∧ l = m := by omega
    unfold FPiece
    by_cases h1 : l ≤ p - 1
    · have hmult : mP p l m = betaN m l - (if l ≤ p - 2 then betaN m (2 * p - 2 - l) else 0) := by
        split_ifs with h2
        · exact mP_of_le hp3 hm h2
        · rw [Nat.sub_zero]; exact mP_of_ge hp3 hm (by omega)
      rw [if_pos h1, ← hmult]
      have hgl : g l = if c + (m - l) / 2 = 0 then [] else [chA p q c ((m - l) / 2) l] := by
        simp only [hg, blkList, if_pos h1]
      rw [hgl]
      by_cases hcl : c = 0 ∧ l = m
      · rw [if_pos (hck.2 hcl), if_pos hcl, flatten_replicate_nil]
        have : mP p l m ≤ 1 := by
          rw [hmult, hcl.2, betaN_self]; omega
        rw [show mP p l m - 1 = 0 by omega]
        exact List.Perm.refl _
      · rw [if_neg (fun h => hcl (hck.1 h)), if_neg hcl, flatten_replicate_single, Nat.sub_zero]
        exact List.Perm.refl _
    · have hpl : p ≤ l := by omega
      have hns := not_simple_of_range hpl (hlm.trans hm)
      have hr := rT_of_range hpl (hlm.trans hm)
      have ha := aT_of_range hpl (hlm.trans hm)
      have hmult := mP_of_ge hp3 hm (l := l) (by omega)
      obtain ⟨hX, hmin, hY⟩ := blk_a_zero hq c ((m - l) / 2) (r := l - p + 1) (by omega) (by omega)
      have hlam : lam p (l - p + 1) 0 = l := by simp [lam]; omega
      have hmu : mu p (l - p + 1) 0 = 2 * p - 2 - l := by simp [mu, lam]; omega
      have hA : blkA p q c ((m - l) / 2) (l - p + 1) 0 = Ac p q c m l := by
        rw [blkA_eq_chA, hlam]; rfl
      have hA' : blkA' p q c ((m - l) / 2) (l - p + 1) 0 = Ac p q c m (2 * p - 2 - l) := by
        rw [blkA'_eq_chA, hmu, Ac]; congr 1; omega
      rw [if_neg h1, hmult]
      have hgl : g l = List.replicate (2 * aT p l) 1 ++
          (if c + (m - l) / 2 = 0 then
            [min (E12 p q c ((m - l) / 2) (rT p l) (aT p l))
              (E22 p q c ((m - l) / 2) (rT p l) (aT p l))]
          else [blkX p q c ((m - l) / 2) (rT p l) (aT p l),
            blkY p q c ((m - l) / 2) (rT p l) (aT p l)]) := by
        simp only [hg, blkList, if_neg h1, if_neg hns]
        split_ifs <;> rfl
      rw [hgl, hr, ha]
      by_cases hcl : c = 0 ∧ l = m
      · rw [if_pos (hck.2 hcl), if_pos hcl, hmin, hA', hcl.2, betaN_self]
        exact List.Perm.refl _
      · rw [if_neg (fun h => hcl (hck.1 h)), if_neg hcl, hX, hY, hA, hA']
        simpa using flatten_replicate_swap _ _ _
  · -- `l` of the other parity: `mP p l m = 0`
    have hpar : ¬ l % 2 = m % 2 := by simpa using hP
    have : mP p l m = 0 := by
      unfold mP
      rw [List.count_eq_zero]
      intro hmem
      exact hpar (M3 hp m l hmem).2
    rw [this]; rfl

/-! ### (F2) -/

/-- **(F2) Theorem F (the Glue Theorem), as printed** (`CSG7_theorem_G.md`, Part F): for
`p ≠ 2`, `1 ≤ v_p(q)` and `m ≤ 2p − 2`,
`Syl_p (tors X_q(m,c)) ≅ ⊕_{e ∈ FList p q c m} ℤ/p^e`.
From (T2), (F1) and `expPerm` (a permutation of the exponents gives isomorphic groups). -/
theorem F2 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q) (hm : m ≤ 2 * p - 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (FList p q c m).length) → ZMod (p ^ (FList p q c m).get i))) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hm' : m ≤ p ^ 2 + p - 1 := by
    have : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p hp
    omega
  obtain ⟨e1⟩ := T2 hp2 c hq hm'
  obtain ⟨e2⟩ := expPerm p (F1 hp2 c hq hm)
  exact ⟨e1.trans e2⟩

end ColouredSand.ThmG
