module

public import RequestProject.OddPayment.Layers

/-!
# Part A of `CSI7_the_twist_move.md`: the odd twist move (Proposition 2.1 of «the odd dance»)

Notation (see `Basic.lean`): `M^S = Payment.Sys N S` (C11's module of a system),
`G_T = Gp p (flT p fl) (FT p F) Q` on `Payment.Sys (NT p N) S`, and `G(QT) = Gp p fl F (QT p Q)`.
As in C11's `Payment.theorem_A`, «`X ≅ Y`» is `Nonempty (X ≃ₗ[A] Y)`, `c • G` is the scalar
multiple of the operator, and `c • ⊤` is the submodule `c · M^S`.

* **(A1) Theorem A_p** (`theorem_Ap`): for odd `p` (with the twisted data `QT` exactly as in
  the file), every graded family, every `Q` and every `c : A`,
  `M_T^S ⧸ range (c • G_T) ≃ (Fin (p − 1) → M^S ⧸ c • ⊤) × (M^S ⧸ range ((c * p) • G(QT)))`.
  The file allows odd `p` or a sign built into `QT`; **both** are proved: `theorem_Ap_sign` holds
  for **every** `p ≥ 1` (also even `p`) with `QTsign p Q = ((−1)^p · p^(p−2)) • (product)`, and
  `theorem_Ap` is its odd case (where `QTsign = QT`). Odd `p = 1` is allowed (more general than
  the file's `p ≥ 2`); `p` need not be prime.
* `corollary_Ap_one` (`c = 1`, the form of C11's `corollary_A1`):
  `coker G_T ≅ coker (p · G(QT))`.
* **(A2)** `corollary_Ap2` (`c = p^h`, as C11's `corollary_A2`):
  `coker (p^h G_T) ≅ (M^S ⧸ p^h)^{p−1} × coker (p^{h+1} G(QT))`.
* **(A3) Evenness** `evenness_A3`: if every entry of every `Q φ` lies in an ideal `I`, every entry
  of every `QT p Q f` lies in `(p)^(p−2) · I^p`; the shape is `QT_shape`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- A product of scaled matrices: `Π (c • M j) = c^length • Π M j` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma list_prod_map_smul (c : A) (M : ℕ → Matrix S S A) (l : List ℕ) :
    (l.map (fun j => c • M j)).prod = c ^ l.length • (l.map M).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, smul_mul_assoc,
      mul_smul_comm, smul_smul, pow_succ]

/-- Step 3 of the *Proof* of (A1) of `CSI7_the_twist_move.md`: the composite of the layer
operators is `D 0 ⋯ D (p−1) = DSm (p^p • Q (p fl i) ⋯ Q (p fl i + p − 1))`, the matrices
multiplied with floors increasing from left to right. -/
lemma chainProd_layerD (p : ℕ) (hp : 0 < p) (fl : ι → ℕ) (Q : ℕ → Matrix S S A) :
    chainProd (layerD (N := N) p fl Q) (p - 1) =
      (p : A) ^ p • DSm (N := N)
        (fun i => ((List.range p).map (fun j => Q (p * fl i + j))).prod) := by
  rw [chainProd, Nat.sub_add_cancel hp]
  have hD : layerD (N := N) p fl Q = fun j => DSmHom A N S (fun i => (p : A) • Q (p * fl i + j)) :=
    rfl
  have hm : (List.range p).map (fun j => DSmHom A N S (fun i => (p : A) • Q (p * fl i + j))) =
      ((List.range p).map (fun j i => (p : A) • Q (p * fl i + j))).map (DSmHom A N S) := by
    rw [List.map_map]; rfl
  rw [hD, hm, ← map_list_prod, ← DSm_smul]
  change DSm _ = DSm _
  congr 1
  funext i
  have he := map_list_prod (Pi.evalMonoidHom (fun _ : ι => Matrix S S A) i)
    ((List.range p).map (fun j i => (p : A) • Q (p * fl i + j)))
  simp only [Pi.evalMonoidHom_apply, List.map_map, Function.comp_def] at he
  rw [Pi.smul_apply, he, list_prod_map_smul, List.length_range]

/-- The scalar bookkeeping of step 3 of the *Proof* of (A1) of `CSI7_the_twist_move.md`:
`(c p) • G(QTsign) = −(c • (−p • F + (−1)^(p−1) • D 0 ⋯ D (p−1)))`. -/
lemma smul_Gp_QTsign (p : ℕ) (hp : 0 < p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    (c * p) • Gp p fl F (QTsign p Q) =
      -(c • (-(p : A) • FSo F + (-1 : A) ^ (p - 1) • chainProd (layerD (N := N) p fl Q) (p - 1))) := by
  rw [Gp_eq, chainProd_layerD p hp]
  have h1 : (fun i => (p : A) • QTsign p Q (fl i)) = ((p : A) * ((-1 : A) ^ p * (p : A) ^ (p - 2))) •
      (fun i => ((List.range p).map (fun j => Q (p * fl i + j))).prod) := by
    funext i
    simp [QTsign, smul_smul]
  rw [h1, DSm_smul]
  generalize DSm (N := N) (fun i => ((List.range p).map (fun j => Q (p * fl i + j))).prod) = P
  generalize FSo (S := S) F = F'
  obtain _ | _ | m := p
  · omega
  · simp only [Nat.cast_one, zero_add, pow_one, Nat.sub_self, pow_zero]
    module
  · simp only [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega]
    push_cast
    module

/-- **(A1) Theorem A_p, with the sign `(−1)^p` built into the data** (*Part A* of
`CSI7_the_twist_move.md`, valid for **every** `p ≥ 1`, also even `p`): for every graded family
`(ι, fl, N, F)`, every slot type `S`, all data `Q` and every `c : A`,
`M_T^S ⧸ range (c • G_T) ≃ (Fin (p − 1) → M^S ⧸ c • ⊤) × (M^S ⧸ range ((c * p) • G(QTsign)))`,
with `G_T = Gp p (flT p fl) (FT p F) Q`. -/
theorem theorem_Ap_sign (p : ℕ) (hp : 0 < p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F (QTsign p Q))))) := by
  have hmap : (LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)).map
      (layerEquiv (A := A) (N := N) (S := S) p :
        Payment.Sys (NT p N) S →ₗ[A] (Fin p → Payment.Sys N S)) =
      LinearMap.range (c • chainOp p (layerD p fl Q) (-(p : A) • FSo F)) := by
    have hsurj : LinearMap.range (layerProj (A := A) (N := N) (S := S) p) = ⊤ :=
      LinearMap.range_eq_top.2 (layerEquiv (A := A) (N := N) (S := S) p).surjective
    rw [layerEquiv_toLinearMap, ← LinearMap.range_comp, LinearMap.comp_smul, layerProj_comp_Gp,
      ← LinearMap.smul_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]
  have hrange : LinearMap.range (c • (-(p : A) • FSo F + (-1 : A) ^ (p - 1) •
      chainProd (layerD (N := N) p fl Q) (p - 1))) =
      LinearMap.range ((c * p) • Gp p fl F (QTsign p Q)) := by
    rw [smul_Gp_QTsign p hp fl F Q c, LinearMap.range_neg]
  let e1 := Submodule.Quotient.equiv _ _ (layerEquiv (A := A) (N := N) (S := S) p) hmap
  let e2 := chainCokerEquiv p hp (layerD (N := N) p fl Q) (-(p : A) • FSo F) c
  exact ⟨(e1.trans e2).trans (LinearEquiv.prodCongr (LinearEquiv.refl A _)
    (Submodule.quotEquivOfEq _ _ hrange))⟩

/-- **(A1) Theorem A_p** (*Part A* of `CSI7_the_twist_move.md`; Proposition 2.1 of «the odd
dance», scaled): for odd `p`, every graded family `(ι, fl, N, F)`, every slot type `S`, all data
`Q : ℕ → Matrix S S A` and every `c : A`,
`Sys (NT N) S ⧸ range (c • G_T) ≃
  (Fin (p − 1) → Sys N S ⧸ c • ⊤) × (Sys N S ⧸ range ((c * p) • Gp fl F (QT p Q)))`,
with `G_T = Gp p (flT p fl) (FT p F) Q` and `QT p Q f = −p^(p−2) • Q (p f) ⋯ Q (p f + p − 1)`.
(`p` odd includes `p = 1`; no primality is needed.) -/
theorem theorem_Ap (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F (QT p Q))))) := by
  rw [← QTsign_of_odd hp]
  exact theorem_Ap_sign p hp.pos fl F Q c

/-- **(A1) with `c = 1`** (*Part A* of `CSI7_the_twist_move.md`, the form of C11's
`corollary_A1`): for odd `p`, `coker G_T ≅ coker (p · G(QT))`, i.e.
`Sys (NT N) S ⧸ range G_T ≃ Sys N S ⧸ range (p • Gp p fl F (QT p Q))`. -/
theorem corollary_Ap_one (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      (Payment.Sys N S ⧸ LinearMap.range ((p : A) • Gp p fl F (QT p Q)))) := by
  obtain ⟨e⟩ := theorem_Ap p hp fl F Q (1 : A)
  rw [one_smul, one_smul, one_mul] at e
  haveI : Subsingleton (Payment.Sys N S ⧸ (⊤ : Submodule A (Payment.Sys N S))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Unique (Fin (p - 1) → Payment.Sys N S ⧸ (⊤ : Submodule A (Payment.Sys N S))) :=
    uniqueOfSubsingleton 0
  exact ⟨e.trans LinearEquiv.uniqueProd⟩

/-- **(A2) Corollary (powers)** (*Part A* of `CSI7_the_twist_move.md`, as C11's
`corollary_A2`): for odd `p` and `c = p^h`,
`Sys (NT N) S ⧸ range (p^h • G_T) ≃
  (Fin (p − 1) → Sys N S ⧸ p^h • ⊤) × (Sys N S ⧸ range (p^(h+1) • G(QT)))`. -/
theorem corollary_Ap2 (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NT p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QT p Q))))) := by
  rw [pow_succ]
  exact theorem_Ap p hp fl F Q ((p : A) ^ h)

/-- The shape of the twisted data (*(A3)* of `CSI7_the_twist_move.md`): `QT p Q f` is `p^(p−2)`
times (minus) a product of `p` of the `Q`'s. -/
lemma QT_shape (p : ℕ) (Q : ℕ → Matrix S S A) (f : ℕ) :
    QT p Q f = (p : A) ^ (p - 2) • -((List.range p).map (fun j => Q (p * f + j))).prod := by
  simp [QT]

/-- Entries of a product of `n` matrices with entries in `I` lie in `I^n` (*(A3)* of
`CSI7_the_twist_move.md`). -/
lemma list_prod_mem_pow (I : Ideal A) (M : ℕ → Matrix S S A) (l : List ℕ)
    (hM : ∀ j ∈ l, ∀ s s', M j s s' ∈ I) (s s' : S) :
    (l.map M).prod s s' ∈ I ^ l.length := by
  induction l generalizing s s' with
  | nil =>
    simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, Matrix.mul_apply]
    rw [pow_succ']
    exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_mul (hM a (by simp) s t)
      (ih (fun j hj => hM j (by simp [hj])) t s')

/-- **(A3) Evenness** (*Part A* of `CSI7_the_twist_move.md`): if every `Q φ` has entries in an
ideal `I`, then every `QT p Q f` has entries in `(p)^(p−2) · I^p`. -/
theorem evenness_A3 (p : ℕ) (Q : ℕ → Matrix S S A) (I : Ideal A)
    (hQ : ∀ φ s s', Q φ s s' ∈ I) (f : ℕ) (s s' : S) :
    QT p Q f s s' ∈ Ideal.span {(p : A)} ^ (p - 2) * I ^ p := by
  have hprod := list_prod_mem_pow I (fun j => Q (p * f + j)) (List.range p)
    (fun j _ s s' => hQ _ s s') s s'
  rw [List.length_range] at hprod
  have hpow : (p : A) ^ (p - 2) ∈ Ideal.span {(p : A)} ^ (p - 2) :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
  simp only [QT, Matrix.smul_apply, smul_eq_mul, neg_mul]
  exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_mul hpow hprod)

end ColouredSand.OddTwist
