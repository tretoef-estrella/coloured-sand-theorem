import RequestProject.Blocks.All

/-!
# CheckCSG1 (Grepy Sand, 13 Oct 2026)

Hand restatement of Lemma 8 (CSG1, `CSG1_lemma_8_the_blocks.md`): the block matrix, the chain
matrix and every number are written out again here from the document, without the project's
definitions, and the four statements (B1), (B2), (S1), (S2) plus (L), (P), (N) are checked against
the certified theorems. Then `#print axioms`.
-/

open Finset

namespace CheckCSG1

open ColouredSand.Blocks

/-- `v t = v_p(q) + v_p(c + k + t)`, by hand. -/
def hv (p q c k t : ℕ) : ℕ := padicValNat p q + padicValNat p (c + k + t)

/-- `N t = q (c + k + t)` in `ℤ_[p]`, by hand. -/
noncomputable def hN (p : ℕ) [Fact p.Prime] (q c k t : ℕ) : ℤ_[p] := ((q * (c + k + t) : ℕ) : ℤ_[p])

/-- The glue entry `u = C(μ+r, μ)(a+1)p / p^ν`, `μ = p − 1 − r + pa` written as `λ − 2r`. -/
def hu (p r a : ℕ) : ℕ :=
  (Nat.choose (p - 1 + r + p * a - 2 * r + r) (p - 1 + r + p * a - 2 * r) * (a + 1) * p) /
    p ^ (if r ≤ p - 1 ∧ a = p - 1 then 2 else 1)

/-- The block matrix of §1, entry by entry, by hand. -/
noncomputable def hM (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) :
    Matrix (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1))
      (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1)) ℤ_[p] :=
  Matrix.of fun x y => match x, y with
    | .inl i', .inl i =>
        if i' = i then hN p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0
    | .inr j', .inr j =>
        if j' = j then hN p q c k (j + r) else if (j' : ℕ) = j + 1 then ((j : ℕ) + 1 : ℤ_[p])
        else 0
    | .inl i', .inr j =>
        if (j : ℕ) = p - 1 + r + p * a - 2 * r ∧ (i' : ℕ) = p - 1 + r + p * a - 2 * r + r + 1
        then (hu p r a : ℤ_[p]) else 0
    | .inr _, .inl _ => 0

/-- `A`, `A'`, `α`, `τ`, `E₁₁`, `E₁₂`, `E₂₂`, `x`, `y`, by hand. -/
def hA (p q c k r a : ℕ) : ℕ := ∑ t ∈ range (p - 1 + r + p * a + 1), hv p q c k t
def hA' (p q c k r a : ℕ) : ℕ := ∑ t ∈ Icc r (r + (p - 1 + r + p * a - 2 * r)), hv p q c k t
def hal (p q c k r a : ℕ) : ℕ := ∑ t ∈ Icc ((a + 1) * p) (p - 1 + r + p * a), hv p q c k t
def htau (p a : ℕ) : ℕ := if a = p - 1 then 2 else 1
def hE11 (p q c k r a : ℕ) : ℕ := hA p q c k r a - hal p q c k r a - a
def hE12 (p q c k r a : ℕ) : ℕ := hA' p q c k r a - a + htau p a
def hE22 (p q c k r a : ℕ) : ℕ := hA' p q c k r a - a + hal p q c k r a
def hx (p q c k r a : ℕ) : ℕ := min (hE11 p q c k r a) (min (hE12 p q c k r a) (hE22 p q c k r a))
def hy (p q c k r a : ℕ) : ℕ := hE11 p q c k r a + hE22 p q c k r a - hx p q c k r a

/-- The chain matrix of §2, by hand. -/
noncomputable def hCh (p : ℕ) [Fact p.Prime] (q c k l : ℕ) :
    Matrix (Fin (l + 1)) (Fin (l + 1)) ℤ_[p] :=
  Matrix.of fun i' i =>
    if i' = i then hN p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0

def hChA (p q c k l : ℕ) : ℕ := ∑ t ∈ range (l + 1), hv p q c k t

/-- (B1) by hand. -/
theorem hB1 (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hck : 1 ≤ c + k) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hM p q c k r a))) ≃+
      (Fin (2 * a) → ZMod p) × ZMod (p ^ hx p q c k r a) × ZMod (p ^ hy p q c k r a)) :=
  B1 hq hck hr1 hrp ha hra

/-- (B2) by hand. -/
theorem hB2 (p : ℕ) [Fact p.Prime] (q r a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hM p q 0 0 r a))) ≃+
      ℤ_[p] × (Fin (2 * a) → ZMod p) × ZMod (p ^ min (hE12 p q 0 0 r a) (hE22 p q 0 0 r a))) :=
  B2 (c := 0) (k := 0) hq rfl rfl hr1 hrp ha hra

/-- (S1) by hand, both cases. -/
theorem hS1 (p : ℕ) [Fact p.Prime] (q c k l : ℕ) (hq : 1 ≤ padicValNat p q) (hl : l ≤ p - 1) :
    (1 ≤ c + k → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ZMod (p ^ hChA p q c k l))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ℤ_[p])) :=
  S1 hq hl

/-- (S2) by hand, both cases. -/
theorem hS2 (p : ℕ) [Fact p.Prime] (q c k l a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hl : l + 1 = (a + 1) * p) (ha : a ≤ p - 1) :
    (1 ≤ c + k → a + 1 ≤ hChA p q c k l ∧ Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+
          (Fin a → ZMod p) × ZMod (p ^ (hChA p q c k l - a)))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ℤ_[p] × (Fin a → ZMod p))) :=
  S2 hq hl ha

/-- (L) by hand. -/
theorem hL (p : ℕ) [Fact p.Prime] (e₁ e₂ e₃ : ℕ) (w : ℤ_[p]) (hw : IsUnit w) :
    Nonempty (((Fin 2 → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin
        !![(p : ℤ_[p]) ^ e₁, w * (p : ℤ_[p]) ^ e₂; 0, (p : ℤ_[p]) ^ e₃])) ≃+
      ZMod (p ^ min e₁ (min e₂ e₃)) × ZMod (p ^ (e₁ + e₃ - min e₁ (min e₂ e₃)))) :=
  lemma_L e₁ e₂ e₃ w hw

/-- (P) by hand. -/
theorem hP (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r)
    (hrp : r ≤ p) (hra : r = p → a = p - 1) :
    a + 1 ≤ hA' p q c k r a ∧ a + 1 ≤ hA p q c k r a - hal p q c k r a :=
  positivity_P (p := p) hq hr1 hrp hra

/-- (N) by hand (the last two clauses: the valuation of the glue entry). -/
theorem hN2 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) :
    (r ≤ p - 1 → padicValNat p (hu p r a) = 0) ∧ (r = p → padicValNat p (hu p r a) = 1) :=
  ⟨(glue_exponent_N (p := p) hr1 hrp ha hra).2.2.2.1, (glue_exponent_N (p := p) hr1 hrp ha hra).2.2.2.2⟩

end CheckCSG1

#print axioms CheckCSG1.hB1
#print axioms CheckCSG1.hB2
#print axioms CheckCSG1.hS1
#print axioms CheckCSG1.hS2
#print axioms CheckCSG1.hL
#print axioms CheckCSG1.hP
#print axioms CheckCSG1.hN2
#print axioms ColouredSand.Blocks.B1
#print axioms ColouredSand.Blocks.B2
#print axioms ColouredSand.Blocks.S1
#print axioms ColouredSand.Blocks.S2
#print axioms ColouredSand.Blocks.S1_pos
#print axioms ColouredSand.Blocks.S1_zero
#print axioms ColouredSand.Blocks.S2_pos
#print axioms ColouredSand.Blocks.S2_zero
#print axioms ColouredSand.Blocks.lemma_L
#print axioms ColouredSand.Blocks.twoByTwo_nonempty
#print axioms ColouredSand.Blocks.positivity_P
#print axioms ColouredSand.Blocks.glue_exponent_N
