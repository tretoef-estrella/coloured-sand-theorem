module

public import RequestProject.BlockOp.Matrices
public import RequestProject.Blocks.All

/-!
# `CSG6_operator_on_the_blocks.md`, Part G — the group of each block (Lemma 8 on the summand)

Namespace `ColouredSand.BlockOp`.

## Encodings

* `cokT p M m q c := (M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m q c)` is the cokernel of the
  operator of (K1) on a DP-lattice `M`.
* `v_p(q)` is `padicValNat p q`; `ZMod n`, `ℤ_[p]`, `Fin a → ZMod p` (for `(ℤ/p)^a`) and `×` (for
  `⊕`) are as in Lemma 8 (`RequestProject/Blocks`); "`≅`" of abelian groups is `≃+`.
* The level offset is `k = (m − λ)/2` (natural-number division), written out in each statement.
* The numbers `chA`, `blkX`, `blkY`, `E12`, `E22` are those of Lemma 8 (`Blocks/Defs.lean`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.BlockOp

open ColouredSand.Strings ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The cokernel `coker (opT p M m q c) = (M.ι → ℤ_[p]) ⧸ range (opT p M m q c)`
(notation for Part G of `CSG6_operator_on_the_blocks.md`). -/
abbrev cokT (M : DPLattice ℤ_[p]) (m q c : ℕ) : Type :=
  (M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m q c)

/-! ### (G1) -/

/-- **(G1)(a)** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, `1 ≤ v_p(q)`, `λ ≤ p − 1`,
`λ ≤ m`, `λ ≡ m (mod 2)` and `k = (m − λ)/2`, the cokernel `C = coker (opT (Ttilt p λ) m q c)`
satisfies: if `1 ≤ c + k`, `C ≃+ ℤ/p^{A}` (`A = chA p q c k λ`); if `c = 0` and `k = 0`,
`C ≃+ ℤ_[p]`.  From (E3)(a) and Lemma 8 (S1). -/
theorem G1a (hp2 : p ≠ 2) {q c l m : ℕ} (hq : 1 ≤ padicValNat p q) (hl : l ≤ p - 1)
    (hle : l ≤ m) (hpar : l % 2 = m % 2) :
    (1 ≤ c + (m - l) / 2 →
      Nonempty (cokT p (Ttilt p l) m q c ≃+ ZMod (p ^ chA p q c ((m - l) / 2) l))) ∧
    (c = 0 → (m - l) / 2 = 0 → Nonempty (cokT p (Ttilt p l) m q c ≃+ ℤ_[p])) := by
  obtain ⟨e⟩ := E3a hp2 (Or.inl hl : IsSimpleWt p l) hle hpar q c
  obtain ⟨h1, h2⟩ := S1 (c := c) (k := (m - l) / 2) hq hl
  exact ⟨fun hck => ⟨e.toAddEquiv.trans (h1 hck).some⟩,
    fun hc hk => ⟨e.toAddEquiv.trans (h2 hc hk).some⟩⟩

/-- `λ + 1 = (a + 1) p` with `a ≤ p − 1` is simple (auxiliary for (G1)(b)). -/
lemma simple_of_mul {l a : ℕ} (hl : l + 1 = (a + 1) * p) (ha : a ≤ p - 1) : IsSimpleWt p l := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  refine Or.inr ⟨⟨a + 1, by rw [hl, mul_comm]⟩, ?_⟩
  have h1 : (a + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  have h2 : p ^ 2 = p * p := by ring
  rw [h2]
  generalize (a + 1) * p = X at *
  generalize p * p = P at *
  omega

/-- **(G1)(b)** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, `1 ≤ v_p(q)`,
`λ + 1 = (a + 1) p` with `a ≤ p − 1`, `λ ≤ m`, `λ ≡ m (mod 2)`, `k = (m − λ)/2`:
if `1 ≤ c + k`, `C ≃+ (ℤ/p)^a ⊕ ℤ/p^{A − a}` (`A = chA p q c k λ`); if `c = k = 0`,
`C ≃+ ℤ_[p] ⊕ (ℤ/p)^a`.  From (E3)(a) and Lemma 8 (S2). -/
theorem G1b (hp2 : p ≠ 2) {q c l m a : ℕ} (hq : 1 ≤ padicValNat p q)
    (hl : l + 1 = (a + 1) * p) (ha : a ≤ p - 1) (hle : l ≤ m) (hpar : l % 2 = m % 2) :
    (1 ≤ c + (m - l) / 2 → Nonempty (cokT p (Ttilt p l) m q c ≃+
      (Fin a → ZMod p) × ZMod (p ^ (chA p q c ((m - l) / 2) l - a)))) ∧
    (c = 0 → (m - l) / 2 = 0 →
      Nonempty (cokT p (Ttilt p l) m q c ≃+ ℤ_[p] × (Fin a → ZMod p))) := by
  obtain ⟨e⟩ := E3a hp2 (simple_of_mul hl ha) hle hpar q c
  obtain ⟨h1, h2⟩ := S2 (c := c) (k := (m - l) / 2) hq hl ha
  exact ⟨fun hck => ⟨e.toAddEquiv.trans (h1 hck).2.some⟩,
    fun hc hk => ⟨e.toAddEquiv.trans (h2 hc hk).some⟩⟩

/-- **(G1)(c)** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`, `1 ≤ v_p(q)`,
`λ ≤ p² + p − 1` not simple, `r = rT p λ`, `a = aT p λ`, `λ ≤ m`, `λ ≡ m (mod 2)`,
`k = (m − λ)/2`: if `1 ≤ c + k`, `C ≃+ (ℤ/p)^{2a} ⊕ ℤ/p^x ⊕ ℤ/p^y`; if `c = k = 0`,
`C ≃+ ℤ_[p] ⊕ (ℤ/p)^{2a} ⊕ ℤ/p^{min E₁₂ E₂₂}`.  From (E3)(b), CSG3 `T3` and Lemma 8 (B1), (B2). -/
theorem G1c (hp2 : p ≠ 2) {q c l m : ℕ} (hq : 1 ≤ padicValNat p q)
    (hl : l ≤ p ^ 2 + p - 1) (hns : ¬ IsSimpleWt p l) (hle : l ≤ m) (hpar : l % 2 = m % 2) :
    (1 ≤ c + (m - l) / 2 → Nonempty (cokT p (Ttilt p l) m q c ≃+
      (Fin (2 * aT p l) → ZMod p) × ZMod (p ^ blkX p q c ((m - l) / 2) (rT p l) (aT p l)) ×
        ZMod (p ^ blkY p q c ((m - l) / 2) (rT p l) (aT p l)))) ∧
    (c = 0 → (m - l) / 2 = 0 → Nonempty (cokT p (Ttilt p l) m q c ≃+
      ℤ_[p] × (Fin (2 * aT p l) → ZMod p) ×
        ZMod (p ^ min (E12 p q c ((m - l) / 2) (rT p l) (aT p l))
          (E22 p q c ((m - l) / 2) (rT p l) (aT p l))))) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨-, hr1, hrp, ha, hra, -⟩ := TiltP.T3 hp hns hl
  obtain ⟨e⟩ := E3b hp2 hl hns hle hpar q c
  refine ⟨fun hck => ?_, fun hc hk => ?_⟩
  · obtain ⟨E⟩ := B1 (c := c) (k := (m - l) / 2) hq hck hr1 hrp ha hra
    exact ⟨e.toAddEquiv.trans E⟩
  · obtain ⟨E⟩ := B2 (q := q) hq hc hk hr1 hrp ha hra
    exact ⟨e.toAddEquiv.trans E⟩

/-! ### (G2) -/

/-- **(G2) the whole cokernel** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`,
`m ≤ p² + p − 1` and every `q c`,
`coker (opM m ℤ_[p] q c) ≃ₗ[ℤ_[p]] Π_{j : Fin (LP p m).length} coker (opT (Ttilt p λ_j) m q c)`
with `λ_j = (LP p m).get j` (this is (K4)), and every `λ_j` satisfies the hypotheses of (G1):
`λ_j ≤ m`, `λ_j ≡ m (mod 2)` and `λ_j ≤ p² + p − 1` (so each factor is described by `G1a`,
`G1b` or `G1c` with `k = (m − λ_j)/2` when `1 ≤ v_p(q)`).  The hypothesis `1 ≤ v_p(q)` of the
file is only needed for (G1), so it is omitted here (more general). -/
theorem G2 (hp2 : p ≠ 2) {m : ℕ} (hm : m ≤ p ^ 2 + p - 1) (q c : ℕ) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((j : Fin (LP p m).length) → cokT p (Ttilt p ((LP p m).get j)) m q c)) ∧
    ∀ j : Fin (LP p m).length, (LP p m).get j ≤ m ∧ (LP p m).get j % 2 = m % 2 ∧
      (LP p m).get j ≤ p ^ 2 + p - 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  refine ⟨K4 hp2 hm q c, fun j => ?_⟩
  obtain ⟨h1, h2⟩ := M3 hp m _ (List.get_mem _ _)
  exact ⟨h1, h2, h1.trans hm⟩

end ColouredSand.BlockOp
