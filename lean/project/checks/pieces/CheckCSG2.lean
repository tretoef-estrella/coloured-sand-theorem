import RequestProject.Glue.All

/-!
# CheckCSG2 (Grepy Sand, 13 Oct 2026)

Hand restatement of Lemma 7 (CSG2, `CSG2_lemma_7_the_glue.md`): the space, the divided powers,
the weight projections, the glued lattice and the operator `q(c+H)+U` are written out again here
from the document (with `λ = p − 1 + r + p a`, `μ = λ − 2r`, `ν` and `x₀ = p^{−ν}` written
explicitly, no project definition), and (G1), (G2), (G3), (G4), (G5), (G6) are checked against the
certified theorems. Then `#print axioms`.
-/

open Finset
open scoped Pointwise

namespace CheckCSG2

open ColouredSand.Blocks ColouredSand.Glue

/-- `F t` by hand: `F t ℓ_i = C(i+t, t) ℓ_{i+t}`, `F t s_j = C(j+t, t) s_{j+t}`. -/
noncomputable def hF (p : ℕ) [Fact p.Prime] (Λ Μ t : ℕ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) = i + t then (((i : ℕ) + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) = j + t then (((j : ℕ) + t).choose t : ℚ_[p]) else 0
    | _, _ => 0)

/-- `E t` by hand: `E t ℓ_i = C(λ−i+t, t) ℓ_{i−t}`, `E t s_j = C(μ−j+t, t) s_{j−t}`. -/
noncomputable def hE (p : ℕ) [Fact p.Prime] (Λ Μ t : ℕ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) + t = i then ((Λ - i + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) + t = j then ((Μ - j + t).choose t : ℚ_[p]) else 0
    | _, _ => 0)

/-- Weight of a basis vector, by hand. -/
def hwt (Λ Μ : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℤ
  | .inl i => (Λ : ℤ) - 2 * (i : ℤ)
  | .inr j => (Μ : ℤ) - 2 * (j : ℤ)

/-- The weight projection `P w`, by hand. -/
noncomputable def hP (p : ℕ) [Fact p.Prime] (Λ Μ : ℕ) (w : ℤ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => if y = z ∧ hwt Λ Μ z = w then 1 else 0)

/-- `ℓ_i` and `s_j`, by hand. -/
noncomputable def hl (p : ℕ) [Fact p.Prime] (Λ Μ i : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if h : i ≤ Λ then Pi.single (Sum.inl ⟨i, Nat.lt_succ_of_le h⟩) 1 else 0
noncomputable def hs (p : ℕ) [Fact p.Prime] (Λ Μ j : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if h : j ≤ Μ then Pi.single (Sum.inr ⟨j, Nat.lt_succ_of_le h⟩) 1 else 0

/-- `s̃ x j = s_j + x C(j+r, j) ℓ_{j+r}`, by hand. -/
noncomputable def hst (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (x : ℚ_[p]) (j : ℕ) :
    Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if j ≤ Μ then hs p Λ Μ j + (x * ((j + r).choose j : ℚ_[p])) • hl p Λ Μ (j + r) else 0

/-- The glued lattice, by hand. -/
noncomputable def hLx (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (x : ℚ_[p]) :
    Submodule ℤ_[p] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Submodule.span ℤ_[p] (Set.range (fun i : Fin (Λ + 1) => hl p Λ Μ i) ∪
    Set.range (fun j : Fin (Μ + 1) => hst p Λ Μ r x j))

/-- Stability, by hand. -/
def hStable (p : ℕ) [Fact p.Prime] (Λ Μ : ℕ)
    (L : Submodule ℤ_[p] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p])) : Prop :=
  (∀ t : ℕ, 1 ≤ t → ∀ v ∈ L, hF p Λ Μ t v ∈ L ∧ hE p Λ Μ t v ∈ L) ∧
    ∀ w : ℤ, ∀ v ∈ L, hP p Λ Μ w v ∈ L

/-- `ν`, by hand. -/
def hnu (p r a : ℕ) : ℕ := if r ≤ p - 1 ∧ a = p - 1 then 2 else 1

/-- (G1) by hand, with `λ = p − 1 + r + p a`, `μ = λ − 2r`. -/
theorem hG1 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) :
    hStable p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r)
        (hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x) ↔
      ‖x‖ ≤ (p : ℝ) ^ hnu p r a :=
  G1_stability_threshold hr1 hrp ha hra x

/-- (G2) by hand. -/
theorem hG2 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1)
    (L : Submodule ℤ_[p] (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]))
    (hS : hStable p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) L)
    (hi : ∀ v : Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p],
      (∀ j, v (.inr j) = 0) →
      (v ∈ L ↔ v ∈ Submodule.span ℤ_[p] (Set.range (fun i : Fin (p - 1 + r + p * a + 1) =>
        hl p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) i))))
    (hii1 : ∀ v ∈ L, ∀ j, ‖v (.inr j)‖ ≤ 1)
    (hii2 : ∀ j : Fin (p - 1 + r + p * a - 2 * r + 1), ∃ v ∈ L,
      ∀ j', v (.inr j') = hs p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) j (.inr j')) :
    ∃ x : ℚ_[p], L = hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x ∧
      ‖x‖ ≤ (p : ℝ) ^ hnu p r a :=
  G2_glue_forced hr1 hrp ha hra L hS hi hii1 hii2

/-- (G3)(b) by hand. -/
theorem hG3b (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ = (p : ℝ) ^ hnu p r a)
    (w : Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p])
    (hwL : w ∈ hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x)
    (hwP : hP p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r)
      ((p - 1 + r + p * a - 2 * r : ℕ) : ℤ) w = w)
    (hw0 : w (.inr ⟨0, Nat.succ_pos _⟩) = 1) :
    ∃ t, 1 ≤ t ∧ t ≤ r ∧ hE p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t w ∉
      (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x :=
  G3b_nonsplit hr1 hrp ha hra x hx w hwL hwP hw0

/-- (G3)(a) by hand. -/
theorem hG3a (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ < (p : ℝ) ^ hnu p r a) (t j : ℕ)
    (hj : j ≤ p - 1 + r + p * a - 2 * r) :
    hE p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t
        (hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x j) -
        (if t ≤ j then ((p - 1 + r + p * a - 2 * r - j + t).choose t : ℚ_[p]) •
          hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x (j - t) else 0) ∈
        (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x ∧
      hF p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t
          (hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x j) -
          ((j + t).choose t : ℚ_[p]) • hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x (j + t) ∈
        (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x :=
  G3a_split hr1 hrp ha hra x hx t j hj

/-- (G4) by hand (any `Λ`, `Μ`, `r`). -/
theorem hG4 (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    ∃ φ : (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]),
      (∀ t v, φ (hF p Λ Μ t v) = hF p Λ Μ t (φ v)) ∧
      (∀ t v, φ (hE p Λ Μ t v) = hE p Λ Μ t (φ v)) ∧
      (∀ (w : ℤ) v, φ (hP p Λ Μ w v) = hP p Λ Μ w (φ v)) ∧
      (∀ i, φ (hl p Λ Μ i) = hl p Λ Μ i) ∧
      (hLx p Λ Μ r x).map ((φ.restrictScalars ℤ_[p]).toLinearMap) =
        hLx p Λ Μ r (((u : ℤ_[p]) : ℚ_[p]) * x) :=
  G4_rescaling (p := p) (L := Λ) (M := Μ) r u x

/-- (G5)(a) by hand: the basis vectors with `x₀ = p^{−ν}` written explicitly. -/
theorem hG5a (p : ℕ) [Fact p.Prime] (r a : ℕ) :
    (∀ i : Fin (p - 1 + r + p * a + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inl i) : V p (lam p r a) (mu p r a)) =
        hl p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) i) ∧
    (∀ j : Fin (p - 1 + r + p * a - 2 * r + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inr j) : V p (lam p r a) (mu p r a)) =
        hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r
          ((p : ℚ_[p]) ^ (-(hnu p r a : ℤ))) j) :=
  G5a_basis (p := p) r a

/-- The operator `q(c+H)+U` on the block, by hand: diagonal `N_i` on `ℓ_i`, `N_{j+r}` on `s_j`, plus `F 1`. -/
noncomputable def hO (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) :
    (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]) →ₗ[ℚ_[p]]
      (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.diagonal fun y => match y with
    | .inl i => ((((q * (c + k + (i : ℕ)) : ℕ) : ℤ_[p])) : ℚ_[p])
    | .inr j => ((((q * (c + k + ((j : ℕ) + r)) : ℕ) : ℤ_[p])) : ℚ_[p])) +
  hF p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) 1

/-- The operator `O = q(c+H) + F 1` by hand, for any `Λ`, `Μ`, `r`: diagonal `N_i` on `ℓ_i` and
`N_{j+r}` on `s_j` (`N_t = q(c+k+t)`), plus `F 1`; it is the project's `Oop`. -/
theorem hOop (p : ℕ) [Fact p.Prime] (Λ Μ q c k r : ℕ) :
    Oop p Λ Μ q c k r =
      Matrix.mulVecLin (Matrix.diagonal fun y : Fin (Λ + 1) ⊕ Fin (Μ + 1) => match y with
        | .inl i => ((((q * (c + k + (i : ℕ)) : ℕ) : ℤ_[p])) : ℚ_[p])
        | .inr j => ((((q * (c + k + ((j : ℕ) + r)) : ℕ) : ℤ_[p])) : ℚ_[p])) +
      Matrix.mulVecLin (Matrix.of fun y z => match y, z with
        | .inl i', .inl i => if (i' : ℕ) = i + 1 then (((i : ℕ) + 1).choose 1 : ℚ_[p]) else 0
        | .inr j', .inr j => if (j' : ℕ) = j + 1 then (((j : ℕ) + 1).choose 1 : ℚ_[p]) else 0
        | _, _ => 0) := by
  unfold Oop Hop Fop Hmat Fmat Nt
  congr 2

/-- (G5)(b): `Orestr` is the restriction of `Oop` to `Lx x₀` (by its definition, read), and its
matrix in the glue basis is `Mblk` (the matrix of CSG1, rewritten by hand in `CheckCSG1`). -/
theorem hG5b (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    (∀ v : Lx p (lam p r a) (mu p r a) r (xzero p r a),
      ((Orestr hr1 hrp ha hra q c k v : Lx p (lam p r a) (mu p r a) r (xzero p r a)) :
        V p (lam p r a) (mu p r a)) = Oop p (lam p r a) (mu p r a) q c k r v) ∧
    LinearMap.toMatrix (glueBasis p (lam p r a) (mu p r a) r (xzero p r a))
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a)) (Orestr hr1 hrp ha hra q c k) =
      Mblk p q c k r a :=
  ⟨fun _ => rfl, G5b_matrix hr1 hrp ha hra q c k⟩

end CheckCSG2

#print axioms CheckCSG2.hG1
#print axioms CheckCSG2.hG2
#print axioms CheckCSG2.hG3a
#print axioms CheckCSG2.hG3b
#print axioms CheckCSG2.hG4
#print axioms CheckCSG2.hG5a
#print axioms CheckCSG2.hOop
#print axioms CheckCSG2.hG5b
#print axioms ColouredSand.Glue.G1_stability_threshold
#print axioms ColouredSand.Glue.G2_glue_forced
#print axioms ColouredSand.Glue.G3a_split
#print axioms ColouredSand.Glue.G3b_nonsplit
#print axioms ColouredSand.Glue.G4_rescaling
#print axioms ColouredSand.Glue.G5a_basis
#print axioms ColouredSand.Glue.G5b_maps
#print axioms ColouredSand.Glue.G5b_matrix
#print axioms ColouredSand.Glue.G6_B1
#print axioms ColouredSand.Glue.G6_B2
