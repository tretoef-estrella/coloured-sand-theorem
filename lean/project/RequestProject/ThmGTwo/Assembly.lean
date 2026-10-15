module

public import RequestProject.ThmGTwo.Theorems

/-!
# `CSX3_theorems_F_G_prime_two.md`, Part T, (A) — Theorems F and G for every prime

Namespace `ColouredSand.ThmGTwo`; every new name starts with `two`.

* `twoThmG` is the conjunction of (T1), (T2), (F1), (F2), (S1), (S2) at `p = 2`.
* The `…_allPrimes` theorems are the statements of CSG7's `ThmG.T1`, `T2`, `F1`, `F2`, `S1`,
  `S2` **without** the hypothesis `hp2 : p ≠ 2`, for every prime `p`: for `p ≠ 2` they are CSG7's
  theorems, for `p = 2` they are the theorems of this folder (at `p = 2` the bounds of CSG7 read
  `p² + p − 1 = 5` and `2p − 2 = 2`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmGTwo

open ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.TiltDec ColouredSand.ThmG

/-- **(A) assembled** (`CSX3_theorems_F_G_prime_two.md`, Part T): Theorems G and F at `p = 2`,
i.e. the conjunction of (T1) `twoT1`, (T2) `twoT2`, (F1) `twoF1`, (F2) `twoF2`, (S1) `twoS1` and
(S2) `twoS2`. -/
theorem twoThmG :
    (∀ (q m c : ℕ), 1 ≤ padicValNat 2 q → m ≤ 5 →
      Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
          AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2) ≃+
        ((j : Fin (LP 2 m).length) →
          GBlk 2 q c ((m - (LP 2 m).get j) / 2) ((LP 2 m).get j)))) ∧
    (∀ (q m c : ℕ), 1 ≤ padicValNat 2 q → m ≤ 5 →
      Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
        ((i : Fin (gTorList 2 q c m).length) → ZMod (2 ^ (gTorList 2 q c m).get i)))) ∧
    (∀ (q m c : ℕ), 1 ≤ padicValNat 2 q → m ≤ 2 →
      (gTorList 2 q c m).Perm (FList 2 q c m)) ∧
    (∀ (q m c : ℕ), 1 ≤ padicValNat 2 q → m ≤ 2 →
      Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
        ((i : Fin (FList 2 q c m).length) → ZMod (2 ^ (FList 2 q c m).get i)))) ∧
    (∀ (d q : ℕ), 2 ≤ q → 1 ≤ padicValNat 2 q → d ≤ 5 →
      Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent (sandpile d q) 2) ≃+
        ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
          (t : Fin (LP 2 (d - σ.1)).length) →
            GBlk 2 q σ.1 ((d - σ.1 - (LP 2 (d - σ.1)).get t) / 2) ((LP 2 (d - σ.1)).get t)))) ∧
    (∀ (d q : ℕ), 2 ≤ q → 1 ≤ padicValNat 2 q → d ≤ 5 →
      Nonempty (AddCommGroup.primaryComponent (sandpile d q) 2 ≃+
        ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
          (i : Fin (gTorList 2 q σ.1 (d - σ.1)).length) →
            ZMod (2 ^ (gTorList 2 q σ.1 (d - σ.1)).get i)))) :=
  ⟨fun _ _ c hq hm => twoT1 c hq hm, fun _ _ c hq hm => twoT2 c hq hm,
    fun _ _ c hq hm => twoF1 c hq hm, fun _ _ c hq hm => twoF2 c hq hm,
    fun _ _ hq2 hq hd => twoS1 hq2 hq hd, fun _ _ hq2 hq hd => twoS2 hq2 hq hd⟩

variable {p : ℕ} [Fact p.Prime]

/-- **Theorem G (T1) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the
statement of `ThmG.T1` without `p ≠ 2`. -/
theorem twoT1_allPrimes {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      ((j : Fin (LP p m).length) →
        GBlk p q c ((m - (LP p m).get j) / 2) ((LP p m).get j))) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoT1 c hq (by norm_num at hm; omega)
  · exact T1 hp2 c hq hm

/-- **Theorem G (T2) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the
statement of `ThmG.T2` without `p ≠ 2`. -/
theorem twoT2_allPrimes {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (gTorList p q c m).length) → ZMod (p ^ (gTorList p q c m).get i))) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoT2 c hq (by norm_num at hm; omega)
  · exact T2 hp2 c hq hm

/-- **Theorem F (F1) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the
statement of `ThmG.F1` without `p ≠ 2`. -/
theorem twoF1_allPrimes {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q) (hm : m ≤ 2 * p - 2) :
    (gTorList p q c m).Perm (FList p q c m) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoF1 c hq (by omega)
  · exact F1 hp2 c hq hm

/-- **Theorem F (F2) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the
statement of `ThmG.F2` without `p ≠ 2`. -/
theorem twoF2_allPrimes {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q) (hm : m ≤ 2 * p - 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (FList p q c m).length) → ZMod (p ^ (FList p q c m).get i))) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoF2 c hq (by omega)
  · exact F2 hp2 c hq hm

/-- **(S1) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the statement of
`ThmG.S1` without `p ≠ 2`. -/
theorem twoS1_allPrimes {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LP p (d - σ.1)).length) →
          GBlk p q σ.1 ((d - σ.1 - (LP p (d - σ.1)).get t) / 2) ((LP p (d - σ.1)).get t))) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoS1 hq2 hq (by norm_num at hd; omega)
  · exact S1 hp2 hq2 hq hd

/-- **(S2) for every prime** (Part T (A) of `CSX3_theorems_F_G_prime_two.md`): the statement of
`ThmG.S2` without `p ≠ 2`. -/
theorem twoS2_allPrimes {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (gTorList p q σ.1 (d - σ.1)).get i))) := by
  by_cases hp2 : p = 2
  · subst hp2; exact twoS2 hq2 hq (by norm_num at hd; omega)
  · exact S2 hp2 hq2 hq hd

end ColouredSand.ThmGTwo
