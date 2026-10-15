module

public import RequestProject.Exponent.Pieces
public import RequestProject.TheoremB.TheoremB

/-!
# (C4) Theorem C: the exponent of `Syl_p K(H(d,q))`

This file corresponds to **(C4) Theorem C** of `CS4_theorem_C_exponent.md`.

## Encoding

* The sandpile group `K(H(d,q))` is `ColouredSand.TheoremB.sandpile d q`, the torsion subgroup
  of `coker L = ((Fin d → Fin q) → ℤ) ⧸ range L` for the Laplacian `L` of the Hamming graph
  (`RequestProject/TheoremB/Basic.lean`, `RequestProject/Splitting/Basic.lean`).
* **The `p`-primary component** `Syl_p K` is Mathlib's `AddCommGroup.primaryComponent K p`, the
  subgroup of elements of `p`-power order (`mem_primaryComponent_iff`: those `x` with
  `p^n • x = 0` for some `n`).
* **The exponent** is Mathlib's `AddMonoid.exponent`: the least positive `n` with `n • x = 0`
  for all `x` (and `0` if there is none).
* `e = v_p(q)` is `padicValNat p q`, `⌊log_p d⌋` is `Nat.log p d`, and
  `max_{1 ≤ s ≤ d}` is `Finset.sup` over `Finset.Icc 1 d` (equal to `0` for `d = 0`).
  `expE p q d` is the exponent `E` of the file.

## Proof

As in the file.  By Theorem A (`ColouredSand.Splitting.theorem_A`) and (B1)
(`torsion_tensor_equiv_syl`, `pieceBaseChange` from `RequestProject/TheoremB/`),
`Syl_p K ≅ ∏_σ torsion (coker_{ℤ_[p]} (q (j + H) + U on B_{d−j}))`, so `p^n` kills `Syl_p K` iff
it kills each factor.  By (C1) + (C2) (`piece_kills_iff`, `piece_zero_kills_torsion`), this
happens iff `e L + v_p(L) + v_p C(b, L) ≤ n` for all `1 ≤ L ≤ b ≤ d` (the piece `j = 1`, which
occurs because `q ≥ 3`, gives the full range; the others give sub-ranges).  Lemma 5 (C3)
identifies the maximum with `E`.
-/

@[expose] public section

open Finset TensorProduct ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB

namespace ColouredSand.Exponent

/-- The exponent `E` of Theorem C: `E = max_{1 ≤ s ≤ d} (e s + v_p(s))` if `e = v_p(q) ≥ 1`, and
`E = ⌊log_p d⌋` if `e = 0`. -/
def expE (p q d : ℕ) : ℕ :=
  if 1 ≤ padicValNat p q then (Icc 1 d).sup (fun s => padicValNat p q * s + padicValNat p s)
  else Nat.log p d

variable {p : ℕ} [hp : Fact p.Prime]

/-- `E` is the maximum of `e L + v_p(L) + v_p C(b, L)` over `1 ≤ L ≤ b ≤ d` (Lemma 5). -/
lemma expE_eq_sup (q d : ℕ) :
    expE p q d = (carryPairs d).sup (fun x => carryTerm p (padicValNat p q) x.1 x.2) := by
  unfold expE carryTerm
  split_ifs with he
  · rw [lemma5]
  · rw [show padicValNat p q = 0 by omega, lemma5_zero]

/-! ### Transport of "`k` kills everything" -/

lemma kills_congr {M N : Type*} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (k : ℕ) :
    (∀ x : M, k • x = 0) ↔ ∀ y : N, k • y = 0 := by
  constructor
  · intro h y
    rw [← e.apply_symm_apply y, ← map_nsmul, h, map_zero]
  · intro h x
    rw [← e.symm_apply_apply x, ← map_nsmul, h, map_zero]

lemma kills_pi {ι : Type*} [DecidableEq ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] (k : ℕ) :
    (∀ x : ∀ i, G i, k • x = 0) ↔ ∀ i, ∀ y : G i, k • y = 0 := by
  constructor
  · intro h i y
    have := congrFun (h (Pi.single i y)) i
    simpa using this
  · intro h x
    funext i
    simpa using h i (x i)

lemma kills_torsion_iff {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (n : ℕ) :
    (∀ y : Submodule.torsion ℤ_[p] M, (p ^ n) • y = 0) ↔
      ∀ x ∈ Submodule.torsion ℤ_[p] M, ((p : ℤ_[p]) ^ n) • x = 0 := by
  constructor
  · intro h x hx
    have := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p]] at this
    simpa using this
  · intro h y
    apply Subtype.ext
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p]]
    simpa using h y.1 y.2

/-! ### The pieces -/

/-- For `c ≥ 1`, `p^n` kills the torsion of the piece iff the bound holds. -/
lemma piece_torsion_kills_iff (m q c n : ℕ) (hq : q ≠ 0) (hc : 1 ≤ c) :
    (∀ x ∈ Submodule.torsion ℤ_[p]
        (B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) (c : ℤ_[p]))),
        ((p : ℤ_[p]) ^ n) • x = 0) ↔
      ∀ s k : ℕ, s + k ≤ m → carryTerm p (padicValNat p q) (k + 1) (c + s + k) ≤ n := by
  rw [← piece_kills_iff m q c n hq hc]
  refine ⟨fun h x => h x ?_, fun h x _ => h x⟩
  -- every element is torsion
  set n0 := ((range (m + 1)) ×ˢ (range (m + 1))).sup
    (fun y => carryTerm p (padicValNat p q) (y.2 + 1) (c + y.1 + y.2))
  have hkill := (piece_kills_iff (p := p) m q c n0 hq hc).mpr fun s k hsk =>
    le_sup (f := fun y : ℕ × ℕ => carryTerm p (padicValNat p q) (y.2 + 1) (c + y.1 + y.2))
      (b := (s, k)) (mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩)
  refine (Submodule.mem_torsion_iff _).mpr ⟨⟨(p : ℤ_[p]) ^ n0, ?_⟩, hkill x⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))

/-- **`p^n` kills `Syl_p K(H(d,q))` iff `e L + v_p(L) + v_p C(b, L) ≤ n` for `1 ≤ L ≤ b ≤ d`.** -/
theorem sylow_kills_iff (d q : ℕ) (hq : 3 ≤ q) (n : ℕ) :
    (∀ x : AddCommGroup.primaryComponent (sandpile d q) p, (p ^ n) • x = 0) ↔
      ∀ L b : ℕ, 1 ≤ L → L ≤ b → b ≤ d → carryTerm p (padicValNat p q) L b ≤ n := by
  classical
  have hq0 : q ≠ 0 := by omega
  -- Step 1: `Syl_p K ≅ torsion (ℤ_[p] ⊗ coker L)`
  let E1 : sylSub p (sandpile d q) ≃+ Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] cokerL d q) :=
    (sylTorsion (p := p) (cokerL d q)).toAddEquiv.trans
      (torsion_tensor_equiv_syl (p := p) (cokerL d q)).some.symm
  -- Step 2: Theorem A and base change
  obtain ⟨EA⟩ := theorem_A d q (by omega)
  let X : PieceIdx d q → Type := fun σ => Xq q (d - σ.1) σ.1
  let E2 : Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] cokerL d q) ≃ₗ[ℤ_[p]]
      ∀ σ : PieceIdx d q, Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X σ) :=
    (torsionEquiv ((LinearEquiv.baseChange ℤ ℤ_[p] _ _ EA).trans
      (TensorProduct.piRight ℤ ℤ_[p] ℤ_[p] X))).trans (torsionPi _)
  let E3 : (∀ σ : PieceIdx d q, Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X σ)) ≃ₗ[ℤ_[p]]
      ∀ σ : PieceIdx d q, Submodule.torsion ℤ_[p] (B (d - σ.1) ℤ_[p] ⧸ LinearMap.range
        (opM (d - σ.1) ℤ_[p] ((q : ℤ) : ℤ_[p]) ((σ.1 : ℕ) : ℤ_[p]))) :=
    LinearEquiv.piCongrRight fun σ => torsionEquiv (pieceBaseChange (p := p) q (d - σ.1) σ.1)
  let Φ := E1.trans (E2.trans E3).toAddEquiv
  have h1 : (∀ x : AddCommGroup.primaryComponent (sandpile d q) p, (p ^ n) • x = 0) ↔
      ∀ x : sylSub p (sandpile d q), (p ^ n) • x = 0 :=
    ⟨fun h x => Subtype.ext (congrArg Subtype.val (h ⟨x.1, x.2⟩)),
      fun h x => Subtype.ext (congrArg Subtype.val (h ⟨x.1, x.2⟩))⟩
  rw [h1, kills_congr Φ, kills_pi]
  simp_rw [kills_torsion_iff]
  constructor
  · -- the piece `j = 1` gives the full range
    intro h L b hL hLb hbd
    have hd : 1 ≤ d := by omega
    have hmult : 0 < d.choose ((⟨1, by omega⟩ : Fin (d + 1)) : ℕ) * (q - 2) ^
        ((⟨1, by omega⟩ : Fin (d + 1)) : ℕ) := by
      simp only [Nat.choose_one_right, pow_one]
      exact Nat.mul_pos (by omega) (by omega)
    have := (piece_torsion_kills_iff (p := p) (d - 1) q 1 n hq0 le_rfl).mp
      (h ⟨⟨1, by omega⟩, ⟨0, hmult⟩⟩) (b - L) (L - 1) (by omega)
    rwa [show L - 1 + 1 = L by omega, show 1 + (b - L) + (L - 1) = b by omega] at this
  · intro h σ
    by_cases hc : (σ.1 : ℕ) = 0
    · exact piece_zero_kills_torsion (d - σ.1) q σ.1 n hq0 hc fun s k hs hsk =>
        h _ _ (by omega) (by omega) (by omega)
    · exact (piece_torsion_kills_iff (d - σ.1) q σ.1 n hq0 (by omega)).mpr fun s k hsk =>
        h _ _ (by omega) (by omega) (by omega)

/-- **(C4) Theorem C.**  Let `q ≥ 3`, `p` a prime and `e = v_p(q)`.  The exponent of
`Syl_p K(H(d,q))` is `p^E`, with `E = max_{1 ≤ s ≤ d} (e s + v_p(s))` if `e ≥ 1` and
`E = ⌊log_p d⌋` if `e = 0`.

Encoding: `K(H(d,q)) = sandpile d q` (torsion subgroup of `coker L`); `Syl_p` is
`AddCommGroup.primaryComponent` (elements of `p`-power order); the exponent is
`AddMonoid.exponent`; the maximum is `Finset.sup` over `Icc 1 d` (so `d = 0` is allowed, with
`E = 0`). -/
theorem theorem_C (d q p : ℕ) [Fact p.Prime] (hq : 3 ≤ q) :
    AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile d q) p) =
      p ^ (if 1 ≤ padicValNat p q then
          (Icc 1 d).sup (fun s => padicValNat p q * s + padicValNat p s)
        else Nat.log p d) := by
  change _ = p ^ expE p q d
  refine exponent_eq_pow_of_kills_iff (Fact.out : p.Prime) fun n => ?_
  rw [sylow_kills_iff d q hq n, expE_eq_sup, Finset.sup_le_iff]
  constructor
  · intro h x hx
    rw [mem_carryPairs] at hx
    exact h x.1 x.2 hx.1 hx.2.1 hx.2.2
  · intro h L b hL hLb hbd
    exact h (L, b) (mem_carryPairs.mpr ⟨hL, hLb, hbd⟩)

/-- Theorem C, stated with `expE`. -/
theorem theorem_C' (d q p : ℕ) [Fact p.Prime] (hq : 3 ≤ q) :
    AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile d q) p) = p ^ expE p q d :=
  theorem_C d q p hq

end ColouredSand.Exponent
