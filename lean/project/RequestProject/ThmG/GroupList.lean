module

public import RequestProject.BlockOp.All
public import RequestProject.ThmG.ExpGroups

/-!
# `CSG7_theorem_G.md`, Part L — the group `G_c(m, λ)` as a list of exponents

Namespace `ColouredSand.ThmG`.

## Encodings

* `ℤ_[p]` is Mathlib's `PadicInt p`, `p` a prime (`[Fact p.Prime]`), `hp2 : p ≠ 2`;
  `v_p(q)` is `padicValNat p q`.
* The numbers `chA`, `vt`, `blkX`, `blkY`, `E12`, `E22` are those of Lemma 8
  (`RequestProject/Blocks/Defs.lean`); `IsSimpleWt`, `rT`, `aT` are those of CSG3
  (`RequestProject/TiltP`).  For the `if` on `IsSimpleWt p l` we use the decidability instance
  `decSimple` obtained by unfolding `IsSimpleWt` (a disjunction of decidable statements).
* (L0) `blkList p q c k l : List ℕ` is the list of the exponents of the finite cyclic factors of
  `G_c(l + 2k, l)`, exactly by the case split of the file (with `a = (l + 1)/p − 1` in the simple
  case `p ≤ l`, and `r = rT p l`, `a = aT p l` in the non-simple case).
* `freeBlk c k = if c = 0 ∧ k = 0 then 1 else 0` is the rank of the free part, and
  `GBlk p q c k l = (Fin (freeBlk c k) → ℤ_[p]) × ((i : Fin (blkList p q c k l).length) →
  ZMod (p ^ (blkList p q c k l).get i))`, i.e. `ℤ_p^{[c=k=0]} ⊕ ⊕_{e ∈ blkList} ℤ/p^e`
  (the second factor is `ExpGrp p (blkList p q c k l)`, an `abbrev` for the same type).
* `cokT p M m q c` is the cokernel of CSG6's operator `opT` on the DP-lattice `M`
  (`RequestProject/BlockOp`); "`≅`" of abelian groups is `≃+`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

open ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks ColouredSand.BlockOp

/-- Decidability of `IsSimpleWt p l` (by unfolding: it is a disjunction of decidable
statements); used for the case split of (L0) of `CSG7_theorem_G.md`. -/
instance decSimple (p : ℕ) : DecidablePred (IsSimpleWt p) := fun l =>
  inferInstanceAs (Decidable (l ≤ p - 1 ∨ (p ∣ l + 1 ∧ l ≤ p ^ 2 - 1)))

variable (p : ℕ) [Fact p.Prime]

/-- **(L0)** of `CSG7_theorem_G.md`: `blkList p q c k l` is the list of the exponents of the
finite cyclic factors of `G_c(l + 2k, l)`:
* if `l ≤ p − 1`: `[]` if `c + k = 0`, else `[chA p q c k l]`;
* if `IsSimpleWt p l` and `p ≤ l` (i.e. not `l ≤ p − 1`), with `a = (l + 1)/p − 1`:
  `replicate a 1` if `c + k = 0`, else `replicate a 1 ++ [chA p q c k l − a]`;
* if `¬ IsSimpleWt p l`, with `r = rT p l`, `a = aT p l`:
  `replicate (2a) 1 ++ [min E₁₂ E₂₂]` if `c + k = 0`, else `replicate (2a) 1 ++ [x, y]`. -/
def blkList (q c k l : ℕ) : List ℕ :=
  if l ≤ p - 1 then
    (if c + k = 0 then [] else [chA p q c k l])
  else if IsSimpleWt p l then
    (if c + k = 0 then List.replicate ((l + 1) / p - 1) 1
      else List.replicate ((l + 1) / p - 1) 1 ++ [chA p q c k l - ((l + 1) / p - 1)])
  else if c + k = 0 then
    List.replicate (2 * aT p l) 1 ++
      [min (E12 p q c k (rT p l) (aT p l)) (E22 p q c k (rT p l) (aT p l))]
  else
    List.replicate (2 * aT p l) 1 ++
      [blkX p q c k (rT p l) (aT p l), blkY p q c k (rT p l) (aT p l)]

/-- **(L0)** of `CSG7_theorem_G.md`: the rank of the free part of `G_c(l + 2k, l)`,
`freeBlk c k = if c = 0 ∧ k = 0 then 1 else 0`. -/
def freeBlk (c k : ℕ) : ℕ := if c = 0 ∧ k = 0 then 1 else 0

/-- **(L0)** of `CSG7_theorem_G.md`: the group
`G_c(l + 2k, l) = ℤ_p^{freeBlk c k} ⊕ ⊕_{e ∈ blkList p q c k l} ℤ/p^e`, encoded as
`(Fin (freeBlk c k) → ℤ_[p]) × ((i : Fin (blkList p q c k l).length) →
ZMod (p ^ (blkList p q c k l).get i))`. -/
abbrev GBlk (q c k l : ℕ) : Type :=
  (Fin (freeBlk c k) → ℤ_[p]) × ExpGrp p (blkList p q c k l)

variable {p}

/-! ### (L1) -/

/-- **(L1)** of `CSG7_theorem_G.md`: for `p ≠ 2`, `1 ≤ v_p(q)`, `l ≤ p² + p − 1`, `l ≤ m` and
`l ≡ m (mod 2)`, `coker (opT (Ttilt p l) m q c) ≅ G_c(m, l) = GBlk p q c ((m − l)/2) l`.
From CSG6 `G1a`, `G1b` (with `l + 1 = (a + 1) p`, `a ≤ p − 1`, CSG5 `simple_large_form`) and
`G1c`, together with `ℤ/p^1 ≅ ℤ/p` and `(ℤ/p)^a ≅ ⊕_{e ∈ replicate a 1} ℤ/p^e`. -/
theorem L1 (hp2 : p ≠ 2) {q c l m : ℕ} (hq : 1 ≤ padicValNat p q) (hl : l ≤ p ^ 2 + p - 1)
    (hle : l ≤ m) (hpar : l % 2 = m % 2) :
    Nonempty (cokT p (Ttilt p l) m q c ≃+ GBlk p q c ((m - l) / 2) l) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set k := (m - l) / 2 with hk
  let eF1 : ℤ_[p] ≃+ (Fin 1 → ℤ_[p]) := (AddEquiv.piUnique fun _ : Fin 1 => ℤ_[p]).symm
  by_cases h1 : l ≤ p - 1
  · obtain ⟨hA, hB⟩ := G1a hp2 hq h1 hle hpar (c := c)
    by_cases hck : c + k = 0
    · have hc : c = 0 := by omega
      have hk0 : k = 0 := by omega
      have hL : blkList p q c k l = [] := by simp only [blkList, if_pos h1, if_pos hck]
      unfold GBlk freeBlk
      rw [hL, if_pos ⟨hc, hk0⟩]
      obtain ⟨e⟩ := hB hc hk0
      exact ⟨e.trans (eF1.trans AddEquiv.prodUnique.symm)⟩
    · have hL : blkList p q c k l = [chA p q c k l] := by simp only [blkList, if_pos h1, if_neg hck]
      unfold GBlk freeBlk
      rw [hL, if_neg (by rintro ⟨h1, h2⟩; omega)]
      obtain ⟨e⟩ := hA (by omega)
      exact ⟨e.trans ((expSingle p _).symm.trans AddEquiv.uniqueProd.symm)⟩
  · by_cases hs : IsSimpleWt p l
    · obtain ⟨b, hb, hlb⟩ := simple_large_form hp hs (by omega)
      have hab : (l + 1) / p - 1 = b := by
        rw [hlb, Nat.mul_div_cancel _ (by omega)]; omega
      obtain ⟨hA, hB⟩ := G1b hp2 hq hlb hb hle hpar (c := c)
      by_cases hck : c + k = 0
      · have hc : c = 0 := by omega
        have hk0 : k = 0 := by omega
        have hL : blkList p q c k l = List.replicate b 1 := by
          simp only [blkList, if_neg h1, if_pos hs, if_pos hck, hab]
        unfold GBlk freeBlk
        rw [hL, if_pos ⟨hc, hk0⟩]
        obtain ⟨e⟩ := hB hc hk0
        exact ⟨e.trans (eF1.prodCongr (expOne p b).symm)⟩
      · have hL : blkList p q c k l = List.replicate b 1 ++ [chA p q c k l - b] := by
          simp only [blkList, if_neg h1, if_pos hs, if_neg hck, hab]
        unfold GBlk freeBlk
        rw [hL, if_neg (by rintro ⟨h1, h2⟩; omega)]
        obtain ⟨e⟩ := hA (by omega)
        exact ⟨e.trans ((((expOne p b).symm.prodCongr (expSingle p _).symm).trans
          (expAppend p _ _).symm).trans AddEquiv.uniqueProd.symm)⟩
    · obtain ⟨hA, hB⟩ := G1c hp2 hq hl hs hle hpar (c := c)
      by_cases hck : c + k = 0
      · have hc : c = 0 := by omega
        have hk0 : k = 0 := by omega
        have hL : blkList p q c k l = List.replicate (2 * aT p l) 1 ++
            [min (E12 p q c k (rT p l) (aT p l)) (E22 p q c k (rT p l) (aT p l))] := by
          simp only [blkList, if_neg h1, if_neg hs, if_pos hck]
        unfold GBlk freeBlk
        rw [hL, if_pos ⟨hc, hk0⟩]
        obtain ⟨e⟩ := hB hc hk0
        exact ⟨e.trans (eF1.prodCongr (((expOne p _).symm.prodCongr (expSingle p _).symm).trans
          (expAppend p _ _).symm))⟩
      · have hL : blkList p q c k l = List.replicate (2 * aT p l) 1 ++
            [blkX p q c k (rT p l) (aT p l), blkY p q c k (rT p l) (aT p l)] := by
          simp only [blkList, if_neg h1, if_neg hs, if_neg hck]
        unfold GBlk freeBlk
        rw [hL, if_neg (by rintro ⟨h1, h2⟩; omega)]
        obtain ⟨e⟩ := hA (by omega)
        let e2 : ZMod (p ^ blkX p q c k (rT p l) (aT p l)) ×
            ZMod (p ^ blkY p q c k (rT p l) (aT p l)) ≃+
            ExpGrp p [blkX p q c k (rT p l) (aT p l), blkY p q c k (rT p l) (aT p l)] :=
          (((AddEquiv.refl _).prodCongr (expSingle p _).symm).trans (expCons p _ _).symm)
        exact ⟨e.trans ((((expOne p _).symm.prodCongr e2).trans
          (expAppend p _ _).symm).trans AddEquiv.uniqueProd.symm)⟩

/-! ### (L2) -/

omit [Fact p.Prime] in
/-- **(L2)** of `CSG7_theorem_G.md`, first half: `blkList p q c k l` depends on `q` only through
`v_p(q)` (all its entries are built from `vt`). -/
theorem L2_val {q q' : ℕ} (h : padicValNat p q = padicValNat p q') (c k l : ℕ) :
    blkList p q c k l = blkList p q' c k l := by
  simp only [blkList, chA, E12, E22, blkX, blkY, E11, blkA, blkA', blkAlpha, vt, h]

omit [Fact p.Prime] in
/-- `v t ≥ 1` when `1 ≤ v_p(q)` (auxiliary for (L2)). -/
lemma one_le_vt {q : ℕ} (hq : 1 ≤ padicValNat p q) (c k t : ℕ) : 1 ≤ vt p q c k t := by
  unfold vt; omega

omit [Fact p.Prime] in
/-- A sum of terms `≥ 1` is at least the number of terms (auxiliary for (L2)). -/
lemma card_le_sum_vt {q : ℕ} (hq : 1 ≤ padicValNat p q) (c k : ℕ) (s : Finset ℕ) :
    s.card ≤ ∑ t ∈ s, vt p q c k t := by
  simpa using Finset.card_nsmul_le_sum s (vt p q c k) 1 (fun t _ => one_le_vt hq c k t)

/-- `Icc a b = Ico a (b + 1)` on `ℕ` (auxiliary). -/
lemma Icc_eq_Ico_succ (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- A non-simple `l` with `rT p l = p` has `aT p l ≥ 1` (auxiliary for (L2)). -/
lemma one_le_aT_of_rT_eq {l : ℕ} (hs : ¬ IsSimpleWt p l) (hr : rT p l = p) : 1 ≤ aT p l := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_contra h0
  have ha : aT p l = 0 := by omega
  have hpl : p ≤ l := by
    by_contra h; exact hs (Or.inl (by omega))
  have hd := aT_rT_eq p l
  rw [ha, hr, mul_zero, zero_add] at hd
  apply hs
  refine Or.inr ⟨⟨2, by omega⟩, ?_⟩
  have : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp
  rw [sq]; omega

/-- Lemma 8's numbers `E₁₁, E₁₂, E₂₂` are `≥ 1` for a non-simple `l` when `1 ≤ v_p(q)`
(auxiliary for (L2)). -/
lemma nonsimple_bounds {q : ℕ} (hq : 1 ≤ padicValNat p q) (c k : ℕ) {l : ℕ}
    (hs : ¬ IsSimpleWt p l) :
    1 ≤ E11 p q c k (rT p l) (aT p l) ∧ 1 ≤ E12 p q c k (rT p l) (aT p l) ∧
      1 ≤ E22 p q c k (rT p l) (aT p l) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hr := rT_bounds (p := p) (by omega) l
  have hra : rT p l = p → 1 ≤ aT p l := one_le_aT_of_rT_eq hs
  generalize rT p l = r at hr hra
  generalize aT p l = a at hra
  have hlam : lam p r a = p - 1 + r + p * a := rfl
  have hpa : a ≤ p * a := Nat.le_mul_of_pos_left _ (by omega)
  have hE11 : 1 ≤ E11 p q c k r a := by
    unfold E11 blkA blkAlpha
    have hsplit := Finset.sum_range_add_sum_Ico (vt p q c k)
      (show (a + 1) * p ≤ lam p r a + 1 by rw [hlam, Nat.add_mul, one_mul, Nat.mul_comm a p]; omega)
    rw [Icc_eq_Ico_succ, ← hsplit]
    have h1 := card_le_sum_vt hq c k (Finset.range ((a + 1) * p))
    rw [Finset.card_range] at h1
    have : a + 1 ≤ (a + 1) * p := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hA' : a + 1 ≤ blkA' p q c k r a := by
    unfold blkA'
    have h1 := card_le_sum_vt hq c k (Finset.Icc r (r + mu p r a))
    rw [Nat.card_Icc] at h1
    have hmu : mu p r a = p - 1 + r + p * a - 2 * r := rfl
    by_cases hrp : r = p
    · have ha1 : 1 ≤ a := hra hrp
      have h2a : 2 * a ≤ p * a := Nat.mul_le_mul_right a hp
      omega
    · omega
  have hE12 : 1 ≤ E12 p q c k r a := by unfold E12 blkTau; split_ifs <;> omega
  have hE22 : 1 ≤ E22 p q c k r a := by unfold E22; omega
  exact ⟨hE11, hE12, hE22⟩

/-- **(L2)** of `CSG7_theorem_G.md`, second half: every entry of `blkList p q c k l` is `≥ 1` when
`1 ≤ v_p(q)` (for every `l`). -/
theorem L2_pos {q : ℕ} (hq : 1 ≤ padicValNat p q) (c k l : ℕ) :
    ∀ x ∈ blkList p q c k l, 1 ≤ x := by
  have hchA : l + 1 ≤ chA p q c k l := by
    have := card_le_sum_vt hq c k (Finset.range (l + 1)); simpa [chA] using this
  intro x hx
  unfold blkList at hx
  split_ifs at hx with h1 h2 h3 h4 h5
  · simp at hx
  · simp at hx; omega
  · simp at hx; omega
  · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    have : (l + 1) / p - 1 ≤ l := by
      have := Nat.div_le_self (l + 1) p; omega
    omega
  · obtain ⟨hE11, hE12, hE22⟩ := nonsimple_bounds hq c k h3
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with hx | hx
    · omega
    · rw [hx]; exact le_min hE12 hE22
  · obtain ⟨hE11, hE12, hE22⟩ := nonsimple_bounds hq c k h3
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx | hx
    · omega
    · rw [hx]; unfold blkX; exact le_min hE11 (le_min hE12 hE22)
    · rw [hx]; unfold blkY blkX
      have : min (E11 p q c k (rT p l) (aT p l))
          (min (E12 p q c k (rT p l) (aT p l)) (E22 p q c k (rT p l) (aT p l))) ≤
          E22 p q c k (rT p l) (aT p l) :=
        (min_le_right _ _).trans (min_le_right _ _)
      omega

end ColouredSand.ThmG
