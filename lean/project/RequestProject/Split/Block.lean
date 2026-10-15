module

public import RequestProject.Payment.Block

/-!
# The row/column reduction of the *Proof* of Theorem B of `C12_split_move.md`

Abstract linear algebra on `X⁴ = X × X × X × X` (components ordered `A, B, C, Dd`):

* `blk4 D0 D1 D2 Fs`: the block operator
  `(a, b, c, d) ↦ (D0 a + 2 Fs b, a + D1 b, 2 a + D1 c + 2 Fs d, c + D2 d)`
  (`G_Ψ` in the decomposition `Sys_Ψ = A ⊕ B ⊕ C ⊕ Dd`).
* `blkH Fs D1 E0 E1`: the block operator `(a, c) ↦ (Fs a + E0 a, −D1 a + Fs c + E1 c)` on `X × X`
  (`G''` in the decomposition `M^{S×{A,C}} = A ⊕ C`).
* `blk4CokerEquiv`: if `D0 ∘ D1 = −2 E0` and `D1 ∘ D2 = −2 E1`, then for every `c`,
  `X⁴ ⧸ range (c • blk4) ≃ (X ⧸ c • ⊤) × (X ⧸ c • ⊤) × ((X × X) ⧸ range (c • 2 • blkH))`.
-/

@[expose] public section

namespace Split

open scoped Pointwise
open Payment

variable {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]

/-- The block operator `(a, b, c, d) ↦ (D0 a + 2 Fs b, a + D1 b, 2 a + D1 c + 2 Fs d, c + D2 d)`
on `X × X × X × X` (the operator `G_Ψ` in the decomposition `A ⊕ B ⊕ C ⊕ Dd` of the *Proof* of
Theorem B of `C12_split_move.md`). -/
def blk4 (D0 D1 D2 Fs : X →ₗ[A] X) : (X × X × X × X) →ₗ[A] (X × X × X × X) where
  toFun v := (D0 v.1 + (2 : A) • Fs v.2.1, v.1 + D1 v.2.1,
    (2 : A) • v.1 + D1 v.2.2.1 + (2 : A) • Fs v.2.2.2, v.2.2.1 + D2 v.2.2.2)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [smul_comm r (2 : A)]

/-- The block operator on a quadruple (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma blk4_apply (D0 D1 D2 Fs : X →ₗ[A] X) (v : X × X × X × X) :
    blk4 D0 D1 D2 Fs v = (D0 v.1 + (2 : A) • Fs v.2.1, v.1 + D1 v.2.1,
      (2 : A) • v.1 + D1 v.2.2.1 + (2 : A) • Fs v.2.2.2, v.2.2.1 + D2 v.2.2.2) := rfl

/-- The block operator `(a, c) ↦ (Fs a + E0 a, −D1 a + Fs c + E1 c)` on `X × X` (the operator
`G''` in the decomposition `A ⊕ C` of the *Proof* of Theorem B of `C12_split_move.md`). -/
def blkH (Fs D1 E0 E1 : X →ₗ[A] X) : (X × X) →ₗ[A] (X × X) :=
  ((Fs + E0).coprod 0).prod ((-D1).coprod (Fs + E1))

/-- The block operator `blkH` on a pair (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma blkH_apply (Fs D1 E0 E1 : X →ₗ[A] X) (v : X × X) :
    blkH Fs D1 E0 E1 v = (Fs v.1 + E0 v.1, -D1 v.1 + (Fs v.2 + E1 v.2)) := by
  simp [blkH]

/-- The change of coordinates `(yA, yB, yC, yD) ↦ (yB, yD, (yA − D0 yB, yC − 2 yB − D1 yD))`
(the inverse of the unipotent automorphism `φ` of the *Proof* of Theorem B of
`C12_split_move.md`, followed by a reordering of the factors). -/
def tau4 (D0 D1 : X →ₗ[A] X) : (X × X × X × X) ≃ₗ[A] (X × X × (X × X)) where
  toFun v := (v.2.1, v.2.2.2, (v.1 - D0 v.2.1, v.2.2.1 - (2 : A) • v.2.1 - D1 v.2.2.2))
  invFun w := (w.2.2.1 + D0 w.1, w.1, w.2.2.2 + (2 : A) • w.1 + D1 w.2.1, w.2.1)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨trivial, trivial, ?_, ?_⟩ <;> abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk,
      smul_sub, smul_comm r (2 : A)]
  left_inv v := by
    obtain ⟨a, b, c, d⟩ := v
    dsimp only
    exact Prod.ext (by abel_nf) (Prod.ext rfl (Prod.ext (by abel_nf) rfl))
  right_inv w := by
    obtain ⟨u, w, z1, z2⟩ := w
    dsimp only
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext (by abel_nf) (by abel_nf)))

/-- The change of coordinates on a quadruple (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma tau4_apply (D0 D1 : X →ₗ[A] X) (v : X × X × X × X) :
    tau4 D0 D1 v = (v.2.1, v.2.2.2, (v.1 - D0 v.2.1, v.2.2.1 - (2 : A) • v.2.1 - D1 v.2.2.2)) :=
  rfl

/-- The image of `range (c • blk4)` under the change of coordinates is
`c • ⊤ × c • ⊤ × range (c • 2 • blkH)`, i.e. `range(c G_Ψ) = c·φ(B ⊕ Dd) + c·2G''(A ⊕ C)`
(*Proof* of Theorem B of `C12_split_move.md`). -/
lemma map_tau4_range (D0 D1 D2 Fs E0 E1 : X →ₗ[A] X) (h0 : D0 ∘ₗ D1 = -(2 : A) • E0)
    (h1 : D1 ∘ₗ D2 = -(2 : A) • E1) (c : A) :
    (LinearMap.range (c • blk4 D0 D1 D2 Fs)).map
        (tau4 D0 D1 : (X × X × X × X) →ₗ[A] (X × X × (X × X))) =
      (c • (⊤ : Submodule A X)).prod ((c • (⊤ : Submodule A X)).prod
        (LinearMap.range (c • (2 : A) • blkH Fs D1 E0 E1))) := by
  have hT0 : ∀ b, D0 (D1 b) = -(2 : A) • E0 b := fun b => by
    simpa using LinearMap.congr_fun h0 b
  have hT1 : ∀ b, D1 (D2 b) = -(2 : A) • E1 b := fun b => by
    simpa using LinearMap.congr_fun h1 b
  ext ⟨u, w, z⟩
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_prod,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨_, ⟨⟨a, b, c', d⟩, rfl⟩, hv⟩
    simp only [LinearMap.smul_apply, blk4_apply, LinearEquiv.coe_coe, tau4_apply,
      Prod.smul_mk, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    refine ⟨⟨a + D1 b, rfl⟩, ⟨c' + D2 d, rfl⟩, ⟨(b, d), ?_⟩⟩
    simp only [LinearMap.smul_apply, blkH_apply, Prod.smul_mk, map_add, map_smul, hT0, hT1,
      Prod.mk.injEq]
    constructor <;> module
  · rintro ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩, ⟨⟨b, d⟩, hz⟩⟩
    refine ⟨_, ⟨(x1 - D1 b, b, x2 - D2 d, d), rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, blk4_apply, LinearEquiv.coe_coe, tau4_apply,
      Prod.smul_mk, Prod.mk.injEq, sub_add_cancel]
    refine ⟨trivial, trivial, ?_⟩
    rw [← hz]
    simp only [LinearMap.smul_apply, blkH_apply, Prod.smul_mk, map_sub, map_smul,
      hT0, hT1, Prod.mk.injEq]
    constructor <;> module

/-- The row/column reduction of the *Proof* of Theorem B of `C12_split_move.md`: if
`D0 ∘ D1 = −2 E0` and `D1 ∘ D2 = −2 E1`, then for every `c`,
`X⁴ ⧸ range (c • blk4 D0 D1 D2 Fs) ≃
  (X ⧸ c • ⊤) × (X ⧸ c • ⊤) × ((X × X) ⧸ range (c • 2 • blkH Fs D1 E0 E1))`. -/
noncomputable def blk4CokerEquiv (D0 D1 D2 Fs E0 E1 : X →ₗ[A] X)
    (h0 : D0 ∘ₗ D1 = -(2 : A) • E0) (h1 : D1 ∘ₗ D2 = -(2 : A) • E1) (c : A) :
    ((X × X × X × X) ⧸ LinearMap.range (c • blk4 D0 D1 D2 Fs)) ≃ₗ[A]
      (X ⧸ c • (⊤ : Submodule A X)) × (X ⧸ c • (⊤ : Submodule A X)) ×
        ((X × X) ⧸ LinearMap.range (c • (2 : A) • blkH Fs D1 E0 E1)) :=
  ((Submodule.Quotient.equiv _ _ (tau4 D0 D1) (map_tau4_range D0 D1 D2 Fs E0 E1 h0 h1 c)).trans
    (quotProdEquiv _ _)).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl A _) (quotProdEquiv _ _))

end Split
