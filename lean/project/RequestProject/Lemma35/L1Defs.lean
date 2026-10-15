module

public import RequestProject.Lemma35.Basic

/-!
# `C22_lemma_35_over_F2.md`: Part L, (L1) `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)`

Encodings (namespace `Lemma35`):

* `T3 B := tensorV (tensorV (V B))` is `V^{⊗3}`, with basis `Fin 2 × (Fin 2 × Fin 2)`; the word
  `e_1e_2e_3` is the basis vector `w e_1 e_2 e_3 := Pi.single (e_1, (e_2, e_3)) 1`.
* `D3 B := dsum (delta B 3) (dsum (V B) (V B))` is `D = Δ(3) ⊕ (V ⊕ V)`, with basis
  `Fin 4 ⊕ (Fin 2 ⊕ Fin 2)`; `eD r = δ_{inl r}` is `e_r`, `bD e = δ_{inr (inl e)}` is `b_e`
  (first copy of `V`) and `cD e = δ_{inr (inr e)}` is `c_e` (second copy).
* `gL = ofImg gimg : D → V^{⊗3}` and `hL = ofImg himg : V^{⊗3} → D` are the linear maps given on
  basis vectors by the tables of the file (`g_basis`, `h_basis`).
* `gHom h2`, `hHom h2` are the corresponding `Hom`s (they need `h2 : (2 : B) = 0`), and
  `isoL1 h2 : Doubling.Iso (T3 B) (D3 B)` has `hom = hHom h2`, `inv = gHom h2`.
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {B : Type*} [CommRing B]

/-- (L1) `V^{⊗3} = tensorV (tensorV (V B))`, basis `Fin 2 × (Fin 2 × Fin 2)`. -/
abbrev T3 (B : Type*) [CommRing B] : DPLattice B := tensorV (tensorV (V B))

/-- (L1) `D = Δ(3) ⊕ (V ⊕ V) = dsum (delta B 3) (dsum (V B) (V B))`, basis
`Fin 4 ⊕ (Fin 2 ⊕ Fin 2)`. -/
abbrev D3 (B : Type*) [CommRing B] : DPLattice B := dsum (delta B 3) (dsum (V B) (V B))

/-- (L1) the index type `Fin 2 × (Fin 2 × Fin 2)` of the basis of `V^{⊗3}`. -/
abbrev IT : Type := Fin 2 × (Fin 2 × Fin 2)

/-- (L1) the index type `Fin 4 ⊕ (Fin 2 ⊕ Fin 2)` of the basis of `D`. -/
abbrev ID : Type := Fin 4 ⊕ (Fin 2 ⊕ Fin 2)

/-- (L1) the word `e_1e_2e_3`, i.e. the basis vector `δ_{(e_1, (e_2, e_3))}` of `V^{⊗3}`. -/
abbrev w (a b c : Fin 2) : IT → B := Pi.single (a, (b, c)) 1

/-- (L1) the basis vector `e_r = δ_{inl r}` of `D`. -/
abbrev eD (r : Fin 4) : ID → B := Pi.single (Sum.inl r) 1

/-- (L1) the basis vector `b_e = δ_{inr (inl e)}` of `D` (first copy of `V`). -/
abbrev bD (e : Fin 2) : ID → B := Pi.single (Sum.inr (Sum.inl e)) 1

/-- (L1) the basis vector `c_e = δ_{inr (inr e)}` of `D` (second copy of `V`). -/
abbrev cD (e : Fin 2) : ID → B := Pi.single (Sum.inr (Sum.inr e)) 1

/-- (L1) the images of the basis vectors of `D` under `g` (the table of the file). -/
def gimg : ID → IT → B :=
  Sum.elim ![w 0 0 0, w 1 0 0 + w 0 1 0 + w 0 0 1, w 1 1 0 + w 1 0 1 + w 0 1 1, w 1 1 1]
    (Sum.elim ![w 1 0 0 + w 0 1 0, w 1 0 1 + w 0 1 1] ![w 0 1 0 + w 0 0 1, w 1 1 0 + w 1 0 1])

/-- (L1) the images of the basis vectors of `V^{⊗3}` under `h` (the table of the file). -/
def himg : IT → ID → B := fun p =>
  ![![![eD 0, eD 1 + bD 0], ![eD 1 + bD 0 + cD 0, eD 2 + cD 1]],
    ![![eD 1 + cD 0, eD 2 + bD 1 + cD 1], ![eD 2 + bD 1, eD 3]]] p.1 p.2.1 p.2.2

/-- (L1) the linear map `g : D → V^{⊗3}`. -/
def gL : (ID → B) →ₗ[B] (IT → B) := ofImg gimg

/-- (L1) the linear map `h : V^{⊗3} → D`. -/
def hL : (IT → B) →ₗ[B] (ID → B) := ofImg himg

/-- (L1) `g` on basis vectors, exactly as in the file. -/
theorem g_basis :
    gL (eD 0) = w (B := B) 0 0 0 ∧
    gL (eD 1) = w (B := B) 1 0 0 + w 0 1 0 + w 0 0 1 ∧
    gL (eD 2) = w (B := B) 1 1 0 + w 1 0 1 + w 0 1 1 ∧
    gL (eD 3) = w (B := B) 1 1 1 ∧
    gL (bD 0) = w (B := B) 1 0 0 + w 0 1 0 ∧
    gL (bD 1) = w (B := B) 1 0 1 + w 0 1 1 ∧
    gL (cD 0) = w (B := B) 0 1 0 + w 0 0 1 ∧
    gL (cD 1) = w (B := B) 1 1 0 + w 1 0 1 := by
  simp only [gL, ofImg_single]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (L1) `h` on basis vectors, exactly as in the file. -/
theorem h_basis :
    hL (w 0 0 0) = eD (B := B) 0 ∧
    hL (w 0 0 1) = eD (B := B) 1 + bD 0 ∧
    hL (w 0 1 0) = eD (B := B) 1 + bD 0 + cD 0 ∧
    hL (w 1 0 0) = eD (B := B) 1 + cD 0 ∧
    hL (w 0 1 1) = eD (B := B) 2 + cD 1 ∧
    hL (w 1 0 1) = eD (B := B) 2 + bD 1 + cD 1 ∧
    hL (w 1 1 0) = eD (B := B) 2 + bD 1 ∧
    hL (w 1 1 1) = eD (B := B) 3 := by
  simp only [hL, ofImg_single]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma T3_wt_bound : ∀ i, -((3 : ℕ) : ℤ) ≤ (T3 B).wt i ∧ (T3 B).wt i ≤ ((3 : ℕ) : ℤ) := by
  rintro ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [tensorV, tensorWt, V]

lemma D3_wt_bound : ∀ i, -((3 : ℕ) : ℤ) ≤ (D3 B).wt i ∧ (D3 B).wt i ≤ ((3 : ℕ) : ℤ) := by
  rintro (i | i | i) <;> fin_cases i <;> simp [dsum, delta, weylWt, V]

lemma g_wt : ∀ (i : ID) (j : IT), (T3 B).wt j ≠ (D3 B).wt i → gL (Pi.single i 1 : ID → B) j = 0 := by
  rintro (i | i | i) ⟨a, b, c⟩ hj <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    fin_cases c <;>
    simp [tensorV, tensorWt, V, dsum, delta, weylWt] at hj <;>
    simp [gL, gimg, Prod.mk.injEq]

lemma h_wt : ∀ (i : IT) (j : ID), (D3 B).wt j ≠ (T3 B).wt i → hL (Pi.single i 1 : IT → B) j = 0 := by
  rintro ⟨a, b, c⟩ (j | j | j) hj <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    fin_cases c <;>
    simp [tensorV, tensorWt, V, dsum, delta, weylWt] at hj <;>
    simp [hL, himg, Sum.inl.injEq, Sum.inr.injEq]


set_option maxHeartbeats 1000000 in
lemma hg_single (h2 : (2 : B) = 0) (i : ID) :
    hL (gL (Pi.single i 1 : ID → B)) = Pi.single i 1 := by
  funext j
  rcases i with i | i | i <;> rcases j with j | j | j <;> fin_cases i <;> fin_cases j <;>
    simp [hL, gL, gimg, himg, map_add, one_add_one_eq_two, h2]

set_option maxHeartbeats 1000000 in
lemma gh_single (h2 : (2 : B) = 0) (i : IT) :
    gL (hL (Pi.single i 1 : IT → B)) = Pi.single i 1 := by
  funext ⟨a, b, c⟩
  obtain ⟨a', b', c'⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;>
    fin_cases c' <;>
    simp [hL, gL, gimg, himg, map_add, one_add_one_eq_two, h2]

end Lemma35
