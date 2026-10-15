module

public import RequestProject.ThmG.All
public import RequestProject.FamilyGroup.All
public import RequestProject.DanceSmith.All
public import RequestProject.TwoTheoremI.All

/-!
# `CSX3_theorems_F_G_prime_two.md`, Part B — tools: `2 × 2` Smith forms and the groups

Namespace `ColouredSand.ThmGTwo`; every new name starts with `two`.  These are the tools for the
proof of (B1) (`RequestProject/ThmGTwo/Blocks.lean`).

## Encodings

* `ℤ_[2]` is Mathlib's `PadicInt 2`; `v_2` of an integer is `padicValInt 2`.
* A Smith form over `ℤ` "with odd determinants" is `P * M * Q = diagonal d` with integer
  matrices `P`, `Q` of odd determinant (these are invertible over `ℤ_[2]`).
* `FamilyGroup.X ds α i` is the group of the tower (C16); `DanceSmith.Mo ds α i` is its final
  matrix in o-order (C15); `FamilyGroup.SC ds` are the small clocks and `FamilyGroup.Q e` is
  `ℤ_[2] ⧸ (2^e)`.
* `ThmG.ExpGrp 2 L` (CSG7) is `⊕_{e ∈ L} ℤ/2^e`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmGTwo

open Matrix FamilyGroup ColouredSand.ThmG
open scoped Pointwise

/-! ### Integer `2 × 2` Smith forms -/

/-- Every non-zero integer is `2^{v_2(a)}` times an odd integer (auxiliary for Part B of
`CSX3_theorems_F_G_prime_two.md`). -/
lemma twoOddDecomp {a : ℤ} (ha : a ≠ 0) : ∃ a' : ℤ, Odd a' ∧ a = 2 ^ padicValInt 2 a * a' := by
  obtain ⟨a', h⟩ := padicValInt_dvd (p := 2) a
  refine ⟨a', ?_, by exact_mod_cast h⟩
  by_contra hne
  rw [Int.not_odd_iff_even] at hne
  obtain ⟨b, rfl⟩ := hne
  generalize hv : padicValInt 2 a = v at h
  have h2 : ((2 : ℕ) : ℤ) ^ (v + 1) ∣ a := ⟨b, by rw [h]; push_cast; ring⟩
  rcases (padicValInt_dvd_iff (p := 2) _ a).1 h2 with h3 | h3
  · exact ha h3
  · omega

/-- Smith form, over `ℤ` with odd determinants, of a lower triangular `2 × 2` integer matrix
`[[a, 0], [b, d]]` with `a, b, d ≠ 0`: the diagonal is `(u₀ 2^x, u₁ 2^{v(a) + v(d) − x})` with
`x = min (v a) (min (v b) (v d))` and `u₀, u₁` odd (tool for Part B of
`CSX3_theorems_F_G_prime_two.md`). -/
lemma twoSmith2_pos (M : Matrix (Fin 2) (Fin 2) ℤ) (h01 : M 0 1 = 0) (h00 : M 0 0 ≠ 0)
    (h10 : M 1 0 ≠ 0) (h11 : M 1 1 ≠ 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ u₀ u₁ : ℤ, Odd u₀ ∧ Odd u₁ ∧
      P * M * Q = diagonal ![u₀ * 2 ^ (min (padicValInt 2 (M 0 0))
          (min (padicValInt 2 (M 1 0)) (padicValInt 2 (M 1 1)))),
        u₁ * 2 ^ (padicValInt 2 (M 0 0) + padicValInt 2 (M 1 1) - min (padicValInt 2 (M 0 0))
          (min (padicValInt 2 (M 1 0)) (padicValInt 2 (M 1 1))))] := by
  obtain ⟨a', ha', ha⟩ := twoOddDecomp h00
  obtain ⟨b', hb', hb⟩ := twoOddDecomp h10
  obtain ⟨d', hd', hd⟩ := twoOddDecomp h11
  have hM : M = !![2 ^ padicValInt 2 (M 0 0) * a', 0; 2 ^ padicValInt 2 (M 1 0) * b',
      2 ^ padicValInt 2 (M 1 1) * d'] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01]
    exacts [ha, hb, hd]
  generalize padicValInt 2 (M 0 0) = va at hM ⊢
  generalize padicValInt 2 (M 1 0) = vb at hM ⊢
  generalize padicValInt 2 (M 1 1) = vd at hM ⊢
  subst hM
  by_cases c1 : va ≤ vb ∧ va ≤ vd
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le c1.1
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le c1.2
    refine ⟨!![1, 0; -(2 ^ s * b'), a'], 1, by simpa [det_fin_two_of] using ha', by simp,
      a', a' * d', ha', ha'.mul hd', ?_⟩
    rw [show min va (min (va + s) (va + t)) = va by omega, show va + (va + t) - va = va + t by omega]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases c2 : vd ≤ vb ∧ vd < va
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le c2.1
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le c2.2.le
    refine ⟨!![0, 1; 1, 0], !![d', 0; -(2 ^ s * b'), 1] * !![0, 1; 1, 0], by simp [det_fin_two_of],
      by simpa [det_fin_two_of] using hd', d', a' * d', hd', ha'.mul hd', ?_⟩
    rw [show min (vd + t) (min (vd + s) vd) = vd by omega,
      show vd + t + vd - vd = vd + t by omega]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · have hba : vb < va := by omega
    have hbd : vb < vd := by omega
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hba.le
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hbd.le
    refine ⟨!![1, 0; -(2 ^ s * a'), b'] * !![0, 1; 1, 0], !![1, -(2 ^ t * d'); 0, b'],
      by simpa [det_fin_two_of] using hb', by simpa [det_fin_two_of] using hb',
      b', -(b' * a' * d'), hb', (hb'.mul ha').mul hd' |>.neg, ?_⟩
    rw [show min (vb + s) (min vb (vb + t)) = vb by omega,
      show vb + s + (vb + t) - vb = vb + s + t by omega]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Smith form, over `ℤ` with odd determinants, of `[[0, 0], [b, d]]` with `b, d ≠ 0`: the
diagonal is `(0, u 2^{min (v b) (v d)})` with `u` odd (tool for Part B of
`CSX3_theorems_F_G_prime_two.md`). -/
lemma twoSmith2_zero (M : Matrix (Fin 2) (Fin 2) ℤ) (h01 : M 0 1 = 0) (h00 : M 0 0 = 0)
    (h10 : M 1 0 ≠ 0) (h11 : M 1 1 ≠ 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ u : ℤ, Odd u ∧
      P * M * Q = diagonal ![0, u * 2 ^ (min (padicValInt 2 (M 1 0)) (padicValInt 2 (M 1 1)))] := by
  obtain ⟨b', hb', hb⟩ := twoOddDecomp h10
  obtain ⟨d', hd', hd⟩ := twoOddDecomp h11
  have hM : M = !![0, 0; 2 ^ padicValInt 2 (M 1 0) * b', 2 ^ padicValInt 2 (M 1 1) * d'] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01]
    exacts [hb, hd]
  generalize padicValInt 2 (M 1 0) = vb at hM ⊢
  generalize padicValInt 2 (M 1 1) = vd at hM ⊢
  subst hM
  by_cases c1 : vb ≤ vd
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le c1
    refine ⟨1, !![1, -(2 ^ t * d'); 0, b'] * !![0, 1; 1, 0], by simp,
      by simpa [det_fin_two_of] using hb', b', hb', ?_⟩
    rw [show min vb (vb + t) = vb by omega]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (not_le.1 c1).le
    refine ⟨1, !![d', 0; -(2 ^ s * b'), 1], by simp,
      by simpa [det_fin_two_of] using hd', d', hd', ?_⟩
    rw [show min (vd + s) vd = vd by omega]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ### The group of a tower from a Smith form of `Mo` -/

/-- From a Smith form `P Mo Q = diagonal d` (odd determinants) of the final matrix in o-order,
`X^{(α)}(ds, i) ≅ SC(ds) × Π_j ℤ_[2] ⧸ (2^k d_j)` (C16 `X_equiv_diag` with C15
`smith_transfer`; tool for Part B of `CSX3_theorems_F_G_prime_two.md`). -/
theorem twoX_smith (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α)
    {P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ}
    (hP : Odd P.det) (hQ : Odd Q.det) (d : Fin (2 ^ Dance.mCount ds) → ℤ)
    (h : P * DanceSmith.Mo ds α i * Q = diagonal d) :
    Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((j : Fin (2 ^ Dance.mCount ds)) →
      ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ ds.length * ((d j : ℤ) : ℤ_[2])})) :=
  X_equiv_diag ds α i hα _ _
    (by rw [det_mul]; exact hP.mul (DanceSmith.odd_det_permMatrix _))
    (by rw [det_mul]; exact (DanceSmith.odd_det_permMatrix _).mul hQ) d
    (DanceSmith.smith_transfer ds α i h)

/-! ### Quotients of `ℤ_[2]` -/

/-- `ℤ_[2] ⧸ (2^k u 2^e) ≅ Q(k + e)` for `u` odd (tool for Part B). -/
def twoQuotUnit (k e : ℕ) {u : ℤ} (hu : Odd u) :
    (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k * (((u * 2 ^ e : ℤ)) : ℤ_[2])}) ≃ₗ[ℤ_[2]] Q (k + e) :=
  Submodule.quotEquivOfEq _ _ (span_two_pow_unit hu)

/-- `ℤ_[2] ⧸ (2^k · 0) ≅ ℤ_[2]` (tool for Part B). -/
def twoQuotZero (k : ℕ) :
    (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k * (((0 : ℤ)) : ℤ_[2])}) ≃ₗ[ℤ_[2]] ℤ_[2] :=
  Submodule.quotEquivOfEqBot _ (by simp)

/-- `Q(n) = ℤ_[2] ⧸ (2^n) ≅ ℤ/2^n` (CSG7's `Blocks.padicQuotEquiv`; tool for Part B). -/
def twoQZMod (n : ℕ) : Q n ≃+ ZMod (2 ^ n) :=
  (Submodule.quotEquivOfEq _ _ (by norm_num)).toAddEquiv.trans
    (ColouredSand.Blocks.padicQuotEquiv (p := 2) n)

/-- `Q(n) ≅ ⊕_{e ∈ [n]} ℤ/2^e` (tool for Part B). -/
def twoQExp (n : ℕ) : Q n ≃+ ExpGrp 2 [n] := (twoQZMod n).trans (expSingle 2 n).symm

/-- `Q(a) × Q(b) ≅ ⊕_{e ∈ [a, b]} ℤ/2^e` (tool for Part B). -/
def twoQExp2 (a b : ℕ) : Q a × Q b ≃+ ExpGrp 2 [a, b] :=
  ((twoQZMod a).prodCongr (twoQExp b)).trans (expCons 2 a [b]).symm

/-! ### The small clocks -/

/-- A quotient by `⊤` is a subsingleton (auxiliary). -/
lemma twoQuotTop_subsingleton {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] :
    Subsingleton (M ⧸ (1 : ℤ_[2]) • (⊤ : Submodule ℤ_[2] M)) := by
  rw [one_smul]
  exact Submodule.Quotient.subsingleton_iff.2 rfl

/-- For a digit list of length one, `SC(ds) = 0`, i.e. `SC(ds) ≅ ⊕_{e ∈ []} ℤ/2^e` (tool for
Part B of `CSX3_theorems_F_G_prime_two.md`). -/
def twoSC_one (b : Bool) : SC [b] ≃+ ExpGrp 2 [] where
  toFun := fun _ => 0
  invFun := fun _ => 0
  left_inv := fun x => by
    funext a
    have : Subsingleton ((Fin (2 ^ ([b].length + Dance.mCount [b] - 1 - a)) → ℤ_[2]) ⧸
        (2 : ℤ_[2]) ^ (a : ℕ) • (⊤ : Submodule ℤ_[2]
          (Fin (2 ^ ([b].length + Dance.mCount [b] - 1 - a)) → ℤ_[2]))) := by
      have ha : (a : ℕ) = 0 := by have := a.isLt; change (a : ℕ) < 1 at this; omega
      rw [ha, pow_zero]; exact twoQuotTop_subsingleton
    exact Subsingleton.elim _ _
  right_inv := fun y => funext fun j => Fin.elim0 j
  map_add' := fun _ _ => by simp

/-- For a digit list of length two, `SC(ds) ≅ (ℤ/2)^{2^{m}} = ⊕_{e ∈ replicate (2^m) 1} ℤ/2^e`,
`m = mCount ds` (written `2 + m − 1 − 1`, as in `SC`) (tool for Part B of
`CSX3_theorems_F_G_prime_two.md`). -/
def twoSC_two (b₁ b₂ : Bool) :
    SC [b₁, b₂] ≃+ ExpGrp 2 (List.replicate (2 ^ (2 + Dance.mCount [b₁, b₂] - 1 - 1)) 1) := by
  set n := 2 ^ (2 + Dance.mCount [b₁, b₂] - 1 - 1)
  let F : Fin 2 → Type := fun a => (Fin (2 ^ (2 + Dance.mCount [b₁, b₂] - 1 - a)) → ℤ_[2]) ⧸
    (2 : ℤ_[2]) ^ (a : ℕ) • (⊤ : Submodule ℤ_[2] (Fin (2 ^ (2 + Dance.mCount [b₁, b₂] - 1 - a)) →
      ℤ_[2]))
  have h0 : Subsingleton (F 0) := by
    change Subsingleton (_ ⧸ (2 : ℤ_[2]) ^ 0 • _)
    rw [pow_zero]; exact twoQuotTop_subsingleton
  let e1 : SC [b₁, b₂] ≃+ F 0 × F 1 := { piFinTwoEquiv F with map_add' := fun _ _ => rfl }
  let e2 : F 0 × F 1 ≃+ F 1 :=
    { toFun := Prod.snd
      invFun := fun y => (0, y)
      left_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let e3 : F 1 ≃+ (Fin n → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ 1}) :=
    (TwoI.twoI_finQuotEquiv n ((2 : ℤ_[2]) ^ 1)).toAddEquiv
  let e4 : (Fin n → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ 1}) ≃+ (Fin n → ZMod (2 ^ 1)) :=
    AddEquiv.piCongrRight fun _ => twoQZMod 1
  exact ((e1.trans e2).trans (e3.trans e4)).trans (expReplicate 2 1 n).symm


/-! ### The cokernels for `N = 1` and `N = 2` -/

/-- `N = 2`, all three entries non-zero: from a Smith form of a lower triangular `2 × 2` matrix
(written on `Fin n` with `n = 2`), `Π_j ℤ_[2] ⧸ (2^k d_j) ≅ ⊕_{e ∈ [k + x, k + y]} ℤ/2^e` with
`x = min (v a) (min (v b) (v d))`, `y = v a + v d − x` (tool for Part B). -/
lemma twoFin2_pos (n : ℕ) (hn : n = 2) (M : Matrix (Fin n) (Fin n) ℤ)
    (h01 : M ⟨0, by omega⟩ ⟨1, by omega⟩ = 0) (h00 : M ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0)
    (h10 : M ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0) (h11 : M ⟨1, by omega⟩ ⟨1, by omega⟩ ≠ 0) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ d : Fin n → ℤ,
      P * M * Q = diagonal d ∧ ∀ k : ℕ,
        Nonempty (((j : Fin n) → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k * ((d j : ℤ) : ℤ_[2])}) ≃+
          ExpGrp 2 [k + min (padicValInt 2 (M ⟨0, by omega⟩ ⟨0, by omega⟩))
              (min (padicValInt 2 (M ⟨1, by omega⟩ ⟨0, by omega⟩))
                (padicValInt 2 (M ⟨1, by omega⟩ ⟨1, by omega⟩))),
            k + (padicValInt 2 (M ⟨0, by omega⟩ ⟨0, by omega⟩) +
              padicValInt 2 (M ⟨1, by omega⟩ ⟨1, by omega⟩) -
              min (padicValInt 2 (M ⟨0, by omega⟩ ⟨0, by omega⟩))
                (min (padicValInt 2 (M ⟨1, by omega⟩ ⟨0, by omega⟩))
                  (padicValInt 2 (M ⟨1, by omega⟩ ⟨1, by omega⟩))))]) := by
  subst hn
  obtain ⟨P, Q, hP, hQ, u₀, u₁, hu₀, hu₁, h⟩ := twoSmith2_pos M h01 h00 h10 h11
  refine ⟨P, Q, hP, hQ, _, h, fun k => ?_⟩
  let G : Fin 2 → Type := fun j => ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k *
    (((![u₀ * 2 ^ (min (padicValInt 2 (M 0 0)) (min (padicValInt 2 (M 1 0))
          (padicValInt 2 (M 1 1)))),
        u₁ * 2 ^ (padicValInt 2 (M 0 0) + padicValInt 2 (M 1 1) - min (padicValInt 2 (M 0 0))
          (min (padicValInt 2 (M 1 0)) (padicValInt 2 (M 1 1))))] j : ℤ)) : ℤ_[2])}
  let e1 : ((j : Fin 2) → G j) ≃+ G 0 × G 1 := { piFinTwoEquiv G with map_add' := fun _ _ => rfl }
  exact ⟨e1.trans (((twoQuotUnit k _ hu₀).toAddEquiv.prodCongr
    (twoQuotUnit k _ hu₁).toAddEquiv).trans (twoQExp2 _ _))⟩

/-- `N = 2`, `a = 0`: `Π_j ℤ_[2] ⧸ (2^k d_j) ≅ ℤ_[2] × ⊕_{e ∈ [k + min (v b) (v d)]} ℤ/2^e`
(tool for Part B). -/
lemma twoFin2_zero (n : ℕ) (hn : n = 2) (M : Matrix (Fin n) (Fin n) ℤ)
    (h01 : M ⟨0, by omega⟩ ⟨1, by omega⟩ = 0) (h00 : M ⟨0, by omega⟩ ⟨0, by omega⟩ = 0)
    (h10 : M ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0) (h11 : M ⟨1, by omega⟩ ⟨1, by omega⟩ ≠ 0) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ d : Fin n → ℤ,
      P * M * Q = diagonal d ∧ ∀ k : ℕ,
        Nonempty (((j : Fin n) → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k * ((d j : ℤ) : ℤ_[2])}) ≃+
          (Fin 1 → ℤ_[2]) × ExpGrp 2 [k + min (padicValInt 2 (M ⟨1, by omega⟩ ⟨0, by omega⟩))
                (padicValInt 2 (M ⟨1, by omega⟩ ⟨1, by omega⟩))]) := by
  subst hn
  obtain ⟨P, Q, hP, hQ, u, hu, h⟩ := twoSmith2_zero M h01 h00 h10 h11
  refine ⟨P, Q, hP, hQ, _, h, fun k => ?_⟩
  let G : Fin 2 → Type := fun j => ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k *
    (((![0, u * 2 ^ (min (padicValInt 2 (M 1 0)) (padicValInt 2 (M 1 1)))] j : ℤ)) : ℤ_[2])}
  let e1 : ((j : Fin 2) → G j) ≃+ G 0 × G 1 := { piFinTwoEquiv G with map_add' := fun _ _ => rfl }
  let eF1 : ℤ_[2] ≃+ (Fin 1 → ℤ_[2]) := (AddEquiv.piUnique fun _ : Fin 1 => ℤ_[2]).symm
  exact ⟨e1.trans ((((twoQuotZero k).toAddEquiv.trans eF1).prodCongr
    ((twoQuotUnit k _ hu).toAddEquiv.trans (twoQExp _))))⟩

/-- `N = 1`, `a ≠ 0`: `Π_j ℤ_[2] ⧸ (2^k d_j) ≅ ⊕_{e ∈ [k + v a]} ℤ/2^e` (tool for Part B). -/
lemma twoFin1_pos (n : ℕ) (hn : n = 1) (M : Matrix (Fin n) (Fin n) ℤ)
    (h00 : M ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧ ∃ d : Fin n → ℤ,
      P * M * Q = diagonal d ∧ ∀ k : ℕ,
        Nonempty (((j : Fin n) → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k * ((d j : ℤ) : ℤ_[2])}) ≃+
          ExpGrp 2 [k + padicValInt 2 (M ⟨0, by omega⟩ ⟨0, by omega⟩)]) := by
  subst hn
  obtain ⟨a', ha', ha⟩ := twoOddDecomp h00
  refine ⟨1, 1, by simp, by simp, fun _ => a' * 2 ^ padicValInt 2 (M 0 0), ?_, fun k => ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.one_mul, Matrix.mul_one, diagonal_apply_eq]
    rw [mul_comm]; exact ha
  · let G : Fin 1 → Type := fun _ => ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ k *
      (((a' * 2 ^ padicValInt 2 (M 0 0) : ℤ)) : ℤ_[2])}
    let e1 : ((j : Fin 1) → G j) ≃+ G 0 := AddEquiv.piUnique G
    exact ⟨e1.trans ((twoQuotUnit k _ ha').toAddEquiv.trans (twoQExp _))⟩

/-! ### The group of a tower with `N ≤ 2` -/

/-- `N = 2`, `a, b, d ≠ 0`: `X^{(α)}(ds, i) ≅ SC(ds) × ⊕_{e ∈ [k + x, k + y]} ℤ/2^e` with
`x = min va (min vb vd)`, `y = va + vd − x`, where `va, vb, vd` are the `2`-adic valuations of the
entries `(0,0)`, `(1,0)`, `(1,1)` of the final matrix in o-order and `k = ds.length` (tool for
Part B of `CSX3_theorems_F_G_prime_two.md`). -/
lemma twoX_N2_pos (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (hN : 2 ^ Dance.mCount ds = 2)
    (h01 : DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨1, by omega⟩ = 0)
    (h00 : DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0)
    (h10 : DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0)
    (h11 : DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨1, by omega⟩ ≠ 0) {va vb vd : ℕ}
    (hva : padicValInt 2 (DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨0, by omega⟩) = va)
    (hvb : padicValInt 2 (DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨0, by omega⟩) = vb)
    (hvd : padicValInt 2 (DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨1, by omega⟩) = vd) :
    Nonempty (X ds α i ≃+ SC ds × ExpGrp 2 [ds.length + min va (min vb vd),
      ds.length + (va + vd - min va (min vb vd))]) := by
  obtain ⟨P, Q, hP, hQ, d, hd, hiso⟩ := twoFin2_pos _ hN (DanceSmith.Mo ds α i) h01 h00 h10 h11
  rw [hva, hvb, hvd] at hiso
  obtain ⟨eX⟩ := twoX_smith ds α i hα hP hQ d hd
  obtain ⟨eQ⟩ := hiso ds.length
  exact ⟨eX.toAddEquiv.trans ((AddEquiv.refl _).prodCongr eQ)⟩

/-- `N = 2`, `a = 0`, `b, d ≠ 0`: `X^{(α)}(ds, i) ≅ SC(ds) × (ℤ_[2] × ⊕_{e ∈ [k + min vb vd]}
ℤ/2^e)` (tool for Part B of `CSX3_theorems_F_G_prime_two.md`). -/
lemma twoX_N2_zero (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (hN : 2 ^ Dance.mCount ds = 2)
    (h01 : DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨1, by omega⟩ = 0)
    (h00 : DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨0, by omega⟩ = 0)
    (h10 : DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨0, by omega⟩ ≠ 0)
    (h11 : DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨1, by omega⟩ ≠ 0) {vb vd : ℕ}
    (hvb : padicValInt 2 (DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨0, by omega⟩) = vb)
    (hvd : padicValInt 2 (DanceSmith.Mo ds α i ⟨1, by omega⟩ ⟨1, by omega⟩) = vd) :
    Nonempty (X ds α i ≃+ SC ds × ((Fin 1 → ℤ_[2]) × ExpGrp 2 [ds.length + min vb vd])) := by
  obtain ⟨P, Q, hP, hQ, d, hd, hiso⟩ := twoFin2_zero _ hN (DanceSmith.Mo ds α i) h01 h00 h10 h11
  rw [hvb, hvd] at hiso
  obtain ⟨eX⟩ := twoX_smith ds α i hα hP hQ d hd
  obtain ⟨eQ⟩ := hiso ds.length
  exact ⟨eX.toAddEquiv.trans ((AddEquiv.refl _).prodCongr eQ)⟩

/-- `N = 1`, `a ≠ 0`: `X^{(α)}(ds, i) ≅ SC(ds) × ⊕_{e ∈ [k + va]} ℤ/2^e` (tool for Part B of
`CSX3_theorems_F_G_prime_two.md`). -/
lemma twoX_N1_pos (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (hN : 2 ^ Dance.mCount ds = 1)
    (h00 : DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0) {va : ℕ}
    (hva : padicValInt 2 (DanceSmith.Mo ds α i ⟨0, by omega⟩ ⟨0, by omega⟩) = va) :
    Nonempty (X ds α i ≃+ SC ds × ExpGrp 2 [ds.length + va]) := by
  obtain ⟨P, Q, hP, hQ, d, hd, hiso⟩ := twoFin1_pos _ hN (DanceSmith.Mo ds α i) h00
  rw [hva] at hiso
  obtain ⟨eX⟩ := twoX_smith ds α i hα hP hQ d hd
  obtain ⟨eQ⟩ := hiso ds.length
  exact ⟨eX.toAddEquiv.trans ((AddEquiv.refl _).prodCongr eQ)⟩

end ColouredSand.ThmGTwo
