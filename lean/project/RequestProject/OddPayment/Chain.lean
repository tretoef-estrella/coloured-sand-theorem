module

public import Mathlib
public import RequestProject.Payment.Block

/-!
# The row/column reduction of the *Proof* of (A1) of `CSI7_the_twist_move.md`

This file is pure linear algebra; it is the `p`-layer analogue of C11's `Payment.blockCokerEquiv`
(`RequestProject/Payment/Block.lean`), whose quotient lemma `Payment.quotProdEquiv` is reused.

## Encoding

* `X` is an `A`-module (later `X = Sys N S = M^S`); `Fin p → X` is the direct sum of `p` copies
  of `X`, the `j`-th copy being the layer `b_j` of the odd twist.
* `D : ℕ → Module.End A X` are the payment parts of the layers (`D j` is the part of the system on
  layer `j`), and `E : Module.End A X` is the part of the system going from the last layer
  `p − 1` back to layer `0` (later `E = −p • F`).
* `chainOp p D E` is the operator `G_T` read in the layers:
  `(chainOp w)_0 = D 0 (w_0) + E (w_{p−1})` and
  `(chainOp w)_j = w_{j−1} + D j (w_j)` for `1 ≤ j ≤ p − 1`.
* `chainProd D m = D 0 * D 1 * ⋯ * D m` (product in `Module.End`, i.e. composition).

## Main result

`chainCokerEquiv`: for `0 < p` and every `c`,
`(Fin p → X) ⧸ range (c • chainOp p D E) ≃
  (Fin (p − 1) → X ⧸ c • ⊤) × (X ⧸ range (c • (E + (−1)^(p−1) • chainProd D (p − 1))))`.
This is steps 1–3 of the *Proof* of (A1): each relation of layer `j ≤ p − 2` eliminates the
generators of layer `j + 1` (one copy of `X ⧸ c` each), and what remains is the relation of the
last layer, with the product `D 0 ⋯ D (p−1)`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open scoped Pointwise

variable {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]

/-- The projection `(Fin p → X) → X` on the layer `k` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
def lproj {p : ℕ} (k : Fin p) : (Fin p → X) →ₗ[A] X := LinearMap.proj (φ := fun _ => X) k

@[simp] lemma lproj_apply {p : ℕ} (k : Fin p) (w : Fin p → X) : lproj (A := A) k w = w k := rfl

/-- `chainProd D m = D 0 * D 1 * ⋯ * D m` in `Module.End A X` (the composite of the layer
operators in step 3 of the *Proof* of (A1) of `CSI7_the_twist_move.md`). -/
def chainProd (D : ℕ → Module.End A X) (m : ℕ) : Module.End A X :=
  ((List.range (m + 1)).map D).prod

/-- `chainProd D 0 = D 0` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainProd_zero (D : ℕ → Module.End A X) : chainProd D 0 = D 0 := by
  simp [chainProd]

/-- `chainProd D (m+1) = chainProd D m * D (m+1)` (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma chainProd_succ (D : ℕ → Module.End A X) (m : ℕ) :
    chainProd D (m + 1) = chainProd D m * D (m + 1) := by
  rw [chainProd, List.range_succ, List.map_append, List.prod_append]
  simp [chainProd]

/-- The operator of the odd twist read in the `p` layers (*Proof* of (A1) of
`CSI7_the_twist_move.md`): `(chainOp w)_0 = D 0 (w_0) + E (w_{p−1})`, and
`(chainOp w)_j = w_{j−1} + D j (w_j)` for `j ≥ 1`. -/
def chainOp (p : ℕ) (D : ℕ → Module.End A X) (E : Module.End A X) :
    (Fin p → X) →ₗ[A] (Fin p → X) :=
  LinearMap.pi fun k =>
    if h : k.val = 0 then D 0 ∘ₗ lproj k + E ∘ₗ lproj (⟨p - 1, by omega⟩ : Fin p)
    else lproj (⟨k.val - 1, by omega⟩ : Fin p) + D k.val ∘ₗ lproj k

/-- The value of `chainOp` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainOp_apply (p : ℕ) (D : ℕ → Module.End A X) (E : Module.End A X) (w : Fin p → X)
    (k : Fin p) :
    chainOp p D E w k = if h : k.val = 0 then D 0 (w k) + E (w ⟨p - 1, by omega⟩)
      else w ⟨k.val - 1, by omega⟩ + D k.val (w k) := by
  unfold chainOp
  split_ifs with h <;> simp [h]

/-- `chainOp` on a single layer `j < p − 1`: `chainOp (b_j y) = b_{j+1} y + b_j (D j y)`
(step 1 of the *Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainOp_single_lt (p : ℕ) (D : ℕ → Module.End A X) (E : Module.End A X) (j : Fin p)
    (hj : j.val + 1 < p) (y : X) :
    chainOp p D E (Pi.single j y) = Pi.single ⟨j.val + 1, hj⟩ y + Pi.single j (D j.val y) := by
  funext k
  rw [chainOp_apply, Pi.add_apply]
  have hl : (⟨p - 1, by omega⟩ : Fin p) ≠ j := fun h => by
    have := congrArg Fin.val h; simp at this; omega
  by_cases hk : k.val = 0
  · have h1 : k ≠ ⟨j.val + 1, hj⟩ := fun h => by rw [h] at hk; simp at hk
    rw [dif_pos hk, Pi.single_eq_of_ne hl, Pi.single_eq_of_ne h1, map_zero, add_zero,
      zero_add]
    by_cases hjk : k = j
    · subst hjk; simp [hk]
    · rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk, map_zero]
  · rw [dif_neg hk]
    by_cases hjk : k = j
    · subst hjk
      have h1 : k ≠ ⟨k.val + 1, hj⟩ := fun h => by have := congrArg Fin.val h; simp at this
      have h2 : (⟨k.val - 1, by omega⟩ : Fin p) ≠ k := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      rw [Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h1]
      simp
    · rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk, map_zero, add_zero, add_zero]
      by_cases h1 : k = ⟨j.val + 1, hj⟩
      · subst h1
        have h2 : (⟨j.val + 1 - 1, by omega⟩ : Fin p) = j := Fin.ext (by simp)
        rw [h2]; simp
      · have h2 : (⟨k.val - 1, by omega⟩ : Fin p) ≠ j := fun h => by
          apply h1; ext; have := congrArg Fin.val h; simp at this ⊢; omega
        rw [Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h1]

/-- `chainOp` on the last layer `j = p − 1`: `chainOp (b_j y) = b_0 (E y) + b_j (D j y)`
(step 1 of the *Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainOp_single_last (p : ℕ) (D : ℕ → Module.End A X) (E : Module.End A X) (j : Fin p)
    (hj : ¬ j.val + 1 < p) (y : X) :
    chainOp p D E (Pi.single j y) = Pi.single ⟨0, j.pos⟩ (E y) + Pi.single j (D j.val y) := by
  have hl : (⟨p - 1, by omega⟩ : Fin p) = j := Fin.ext (by simp; omega)
  funext k
  rw [chainOp_apply, Pi.add_apply]
  by_cases hk : k.val = 0
  · have h0 : k = ⟨0, j.pos⟩ := Fin.ext hk
    rw [dif_pos hk, hl, Pi.single_eq_same]
    subst h0
    by_cases hjk : (⟨0, j.pos⟩ : Fin p) = j
    · rw [hjk, ← hjk]; simp [add_comm]
    · rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk, map_zero]; simp
  · rw [dif_neg hk]
    have h0 : k ≠ ⟨0, j.pos⟩ := fun h => by rw [h] at hk; simp at hk
    have h2 : (⟨k.val - 1, by omega⟩ : Fin p) ≠ j := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    rw [Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h0, zero_add, zero_add]
    by_cases hjk : k = j
    · subst hjk; simp
    · rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk, map_zero]

/-- The row operation `ψ` (step 2 of the *Proof* of (A1) of `CSI7_the_twist_move.md`):
`ψ y = (y_0 − Σ_{k < p−1} (−1)^k (D 0 ⋯ D k)(y_{k+1}), (y_{j+1})_{j < p−1})`. -/
def chainRow (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) :
    (Fin p → X) →ₗ[A] X × (Fin (p - 1) → X) :=
  (lproj (⟨0, hp⟩ : Fin p) - ∑ k : Fin (p - 1),
      ((-1 : A) ^ (k : ℕ) • chainProd D k) ∘ₗ lproj (⟨k.val + 1, by omega⟩ : Fin p)).prod
    (LinearMap.pi fun j : Fin (p - 1) => lproj (⟨j.val + 1, by omega⟩ : Fin p))

/-- The value of `chainRow` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainRow_apply (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) (y : Fin p → X) :
    chainRow p hp D y = (y ⟨0, hp⟩ - ∑ k : Fin (p - 1),
      (-1 : A) ^ (k : ℕ) • chainProd D k (y ⟨k.val + 1, by omega⟩),
      fun j => y ⟨j.val + 1, by omega⟩) := by
  rw [Prod.ext_iff]
  exact ⟨by simp [chainRow], funext fun j => by simp [chainRow]⟩

/-- The column operation `τ` (step 2 of the *Proof* of (A1) of `CSI7_the_twist_move.md`):
`τ w = (w_{p−1}, (w_j + D (j+1) (w_{j+1}))_{j < p−1})`. -/
def chainCol (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) :
    (Fin p → X) →ₗ[A] X × (Fin (p - 1) → X) :=
  (lproj (⟨p - 1, by omega⟩ : Fin p)).prod
    (LinearMap.pi fun j : Fin (p - 1) => lproj (⟨j.val, by omega⟩ : Fin p) +
      D (j.val + 1) ∘ₗ lproj (⟨j.val + 1, by omega⟩ : Fin p))

/-- The value of `chainCol` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma chainCol_apply (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) (w : Fin p → X) :
    chainCol p hp D w = (w ⟨p - 1, by omega⟩,
      fun j => w ⟨j.val, by omega⟩ + D (j.val + 1) (w ⟨j.val + 1, by omega⟩)) := by
  rw [Prod.ext_iff]
  exact ⟨by simp [chainCol], funext fun j => by simp [chainCol]⟩

/-- The row operation `ψ` is bijective (it is unipotent) (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma chainRow_bijective (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) :
    Function.Bijective (chainRow p hp D) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [chainRow_apply, Prod.mk_eq_zero] at hy
    obtain ⟨h0, h1⟩ := hy
    have hs : ∀ k : Fin (p - 1), y ⟨k.val + 1, by omega⟩ = 0 := fun k => congr_fun h1 k
    simp only [hs, map_zero, smul_zero, Finset.sum_const_zero, sub_zero] at h0
    funext k
    by_cases hk : k.val = 0
    · have : k = ⟨0, hp⟩ := Fin.ext hk
      rw [this, h0]; rfl
    · have := hs ⟨k.val - 1, by omega⟩
      have e : (⟨k.val - 1 + 1, by omega⟩ : Fin p) = k := Fin.ext (by simp; omega)
      rw [e] at this
      rw [this]; rfl
  · rintro ⟨a, z⟩
    refine ⟨fun k => if h : k.val = 0 then a + ∑ k : Fin (p - 1),
      (-1 : A) ^ (k : ℕ) • chainProd D k (z k) else z ⟨k.val - 1, by omega⟩, ?_⟩
    rw [chainRow_apply]
    simp

/-- The column operation `τ` is surjective (solve the layers downwards) (*Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma chainCol_surjective (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) :
    Function.Surjective (chainCol p hp D) := by
  rintro ⟨a, z⟩
  let zN : ℕ → X := fun k => if h : k < p - 1 then z ⟨k, h⟩ else 0
  let v : ℕ → X := fun k => Nat.rec a (fun k vk => zN (p - 2 - k) - D (p - 1 - k) vk) k
  have hv : ∀ k, v (k + 1) = zN (p - 2 - k) - D (p - 1 - k) (v k) := fun k => rfl
  refine ⟨fun j => v (p - 1 - j.val), ?_⟩
  rw [chainCol_apply]
  refine Prod.ext ?_ ?_
  · simp [v]
  · funext j
    simp only
    have e : p - 1 - j.val = (p - 2 - j.val) + 1 := by omega
    rw [e, hv]
    have e1 : p - 2 - (p - 2 - j.val) = j.val := by omega
    have e2 : p - 1 - (p - 2 - j.val) = j.val + 1 := by omega
    have e3 : p - 1 - (j.val + 1) = p - 2 - j.val := by omega
    rw [e1, e2, e3]
    simp [zN, j.isLt]

/-- The key identity of the *Proof* of (A1) of `CSI7_the_twist_move.md`:
`ψ ∘ chainOp = (H × id) ∘ τ`, with `H = E + (−1)^(p−1) (D 0 ⋯ D (p−1))`.
The first component is a telescoping sum. -/
lemma chainRow_chainOp (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) (E : Module.End A X)
    (w : Fin p → X) :
    chainRow p hp D (chainOp p D E w) =
      ((E + (-1 : A) ^ (p - 1) • chainProd D (p - 1)).prodMap LinearMap.id)
        (chainCol p hp D w) := by
  rw [chainRow_apply, chainCol_apply]
  refine Prod.ext ?_ ?_
  · simp only [LinearMap.prodMap_apply, LinearMap.add_apply, LinearMap.smul_apply]
    rw [chainOp_apply]
    simp only [dite_true]
    let wN : ℕ → X := fun k => if h : k < p then w ⟨k, h⟩ else 0
    let b : ℕ → X := fun k => (-1 : A) ^ k • chainProd D k (wN k)
    have hsum : ∑ k : Fin (p - 1), (-1 : A) ^ (k : ℕ) • chainProd D k
        (chainOp p D E w ⟨k.val + 1, by omega⟩) =
          ∑ k ∈ Finset.range (p - 1), (b k - b (k + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [chainOp_apply]
      have h1 : k.val + 1 < p := by omega
      have h2 : k.val < p := by omega
      simp only [Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel, b, wN, h1, h2,
        dite_true, chainProd_succ, Module.End.mul_apply, map_add, smul_add, pow_succ,
        mul_neg_one, neg_smul, sub_neg_eq_add]
    rw [hsum, Finset.sum_range_sub']
    have hb0 : b 0 = D 0 (w ⟨0, hp⟩) := by simp [b, wN, hp, chainProd_zero]
    have hbp : b (p - 1) = (-1 : A) ^ (p - 1) • chainProd D (p - 1) (w ⟨p - 1, by omega⟩) := by
      have : p - 1 < p := by omega
      simp [b, wN, this]
    rw [hb0, hbp]
    abel
  · funext j
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply]
    rw [chainOp_apply]
    simp

/-- The row operation `ψ` sends the relations `range (c • chainOp)` onto
`range (c • H) × c • ⊤` (*Proof* of (A1) of `CSI7_the_twist_move.md`). -/
lemma map_chainRow_range (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X) (E : Module.End A X)
    (c : A) :
    (LinearMap.range (c • chainOp p D E)).map (chainRow p hp D) =
      (LinearMap.range (c • (E + (-1 : A) ^ (p - 1) • chainProd D (p - 1)))).prod
        (c • (⊤ : Submodule A (Fin (p - 1) → X))) := by
  rw [← LinearMap.range_comp, LinearMap.comp_smul]
  have hc : chainRow p hp D ∘ₗ chainOp p D E =
      ((E + (-1 : A) ^ (p - 1) • chainProd D (p - 1)).prodMap LinearMap.id) ∘ₗ
        chainCol p hp D := LinearMap.ext (chainRow_chainOp p hp D E)
  rw [hc, ← LinearMap.smul_comp,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (chainCol_surjective p hp D))]
  ext ⟨y, z⟩
  simp only [LinearMap.mem_range, Submodule.mem_prod,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [LinearMap.smul_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Prod.smul_mk, Prod.mk.injEq] at h
    exact ⟨⟨a, by simpa using h.1⟩, ⟨b, h.2⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨by simpa using ha, hb⟩

/-- `c • (Fin m → X) = Π_j c • X` (*Proof* of (A1) of `CSI7_the_twist_move.md`: the
`Fin (p − 1)` copies of `X ⧸ c`). -/
lemma smul_top_pi_eq {m : ℕ} (c : A) :
    (c • (⊤ : Submodule A (Fin m → X))) =
      Submodule.pi Set.univ (fun _ : Fin m => c • (⊤ : Submodule A X)) := by
  ext z
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    Submodule.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨b, rfl⟩ j
    exact ⟨b j, rfl⟩
  · intro h
    choose b hb using h
    exact ⟨b, funext hb⟩

/-- **The chain reduction** (steps 1–3 of the *Proof* of (A1) of `CSI7_the_twist_move.md`):
for `0 < p` and every `c`,
`(Fin p → X) ⧸ range (c • chainOp p D E) ≃
  (Fin (p − 1) → X ⧸ c • ⊤) × (X ⧸ range (c • (E + (−1)^(p−1) • D 0 ⋯ D (p−1))))`. -/
noncomputable def chainCokerEquiv (p : ℕ) (hp : 0 < p) (D : ℕ → Module.End A X)
    (E : Module.End A X) (c : A) :
    ((Fin p → X) ⧸ LinearMap.range (c • chainOp p D E)) ≃ₗ[A]
      (Fin (p - 1) → X ⧸ c • (⊤ : Submodule A X)) ×
        (X ⧸ LinearMap.range (c • (E + (-1 : A) ^ (p - 1) • chainProd D (p - 1)))) :=
  ((((Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective _ (chainRow_bijective p hp D))
      (map_chainRow_range p hp D E c)).trans (Payment.quotProdEquiv _ _)).trans
    (LinearEquiv.prodComm A _ _))).trans
    (LinearEquiv.prodCongr
      ((Submodule.quotEquivOfEq _ _ (smul_top_pi_eq c)).trans (Submodule.quotientPi _))
      (LinearEquiv.refl A _))

end ColouredSand.OddTwist
