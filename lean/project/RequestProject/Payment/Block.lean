module

public import Mathlib

/-!
# Linear-algebra lemmas for the proof of Theorem A of `C11_payment_systems_twist.md`

* `quotProdEquiv`: `(X × Y) ⧸ (P.prod Q) ≃ (X ⧸ P) × (Y ⧸ Q)`.
* `blockOp T0 T1 Fs`: the block operator `(a, b) ↦ (T0 a + 2 Fs b, a + T1 b)` on `X × X`
  (`G_Φ` in the decomposition `M_Φ^S = B_0 ⊕ B_1`).
* `block_coker`: the row/column reduction of the *Proof* of Theorem A: if `T0 ∘ T1 = −2 D`,
  then `(X × X) ⧸ range (c • blockOp) ≃ (X ⧸ c • ⊤) × (X ⧸ range (c • 2 • (Fs + D)))`.
-/

@[expose] public section

namespace Payment

open scoped Pointwise

variable {A X Y : Type*} [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y]
  [Module A Y]

/-- `(X × Y) ⧸ (P × Q) ≃ (X ⧸ P) × (Y ⧸ Q)` (used in the *Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
noncomputable def quotProdEquiv (P : Submodule A X) (Q : Submodule A Y) :
    ((X × Y) ⧸ P.prod Q) ≃ₗ[A] (X ⧸ P) × (Y ⧸ Q) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ])).trans
    (LinearMap.quotKerEquivOfSurjective (P.mkQ.prodMap Q.mkQ) (by
      rintro ⟨a, b⟩
      obtain ⟨a', rfl⟩ := Submodule.mkQ_surjective P a
      obtain ⟨b', rfl⟩ := Submodule.mkQ_surjective Q b
      exact ⟨(a', b'), rfl⟩))

/-- The block operator `(a, b) ↦ (T0 a + 2 Fs b, a + T1 b)` on `X × X` (the operator `G_Φ` in
the decomposition `B_0 ⊕ B_1` of the *Proof* of Theorem A of `C11_payment_systems_twist.md`). -/
def blockOp (T0 T1 Fs : X →ₗ[A] X) : (X × X) →ₗ[A] (X × X) :=
  (T0.coprod ((2 : A) • Fs)).prod (LinearMap.id.coprod T1)

/-- The block operator on a pair (*Proof* of Theorem A of `C11_payment_systems_twist.md`). -/
@[simp] lemma blockOp_apply (T0 T1 Fs : X →ₗ[A] X) (v : X × X) :
    blockOp T0 T1 Fs v = (T0 v.1 + (2 : A) • Fs v.2, v.1 + T1 v.2) := by
  simp [blockOp]

/-- The shear `(y, z) ↦ (y − T0 z, z)` (the inverse of the automorphism `φ` of the *Proof* of
Theorem A of `C11_payment_systems_twist.md`). -/
def shear (T0 : X →ₗ[A] X) : (X × X) ≃ₗ[A] (X × X) :=
  LinearEquiv.ofLinear ((LinearMap.fst A X X - T0 ∘ₗ LinearMap.snd A X X).prod
      (LinearMap.snd A X X))
    ((LinearMap.fst A X X + T0 ∘ₗ LinearMap.snd A X X).prod (LinearMap.snd A X X))
    (by ext <;> simp) (by ext <;> simp)

/-- The shear on a pair (*Proof* of Theorem A of `C11_payment_systems_twist.md`). -/
@[simp] lemma shear_apply (T0 : X →ₗ[A] X) (v : X × X) : shear T0 v = (v.1 - T0 v.2, v.2) := by
  simp [shear]

/-- The image of `range (c • blockOp)` under the shear is
`range (c • 2 • (Fs + D)) × c • ⊤` (the *Proof* of Theorem A of
`C11_payment_systems_twist.md`). -/
lemma map_shear_range (T0 T1 Fs D : X →ₗ[A] X) (h : T0 ∘ₗ T1 = -(2 : A) • D) (c : A) :
    (LinearMap.range (c • blockOp T0 T1 Fs)).map (shear T0 : (X × X) →ₗ[A] (X × X)) =
      (LinearMap.range (c • (2 : A) • (Fs + D))).prod (c • (⊤ : Submodule A X)) := by
  have hT : ∀ b, T0 (T1 b) = -(2 : A) • D b := fun b => by
    simpa using LinearMap.congr_fun h b
  ext ⟨y, z⟩
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_prod,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨_, ⟨⟨a, b⟩, rfl⟩, hv⟩
    simp only [LinearMap.smul_apply, blockOp_apply, LinearEquiv.coe_coe, shear_apply,
      Prod.smul_mk, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨⟨b, ?_⟩, ⟨a + T1 b, rfl⟩⟩
    simp only [LinearMap.smul_apply, LinearMap.add_apply, map_add, map_smul, hT]
    module
  · rintro ⟨⟨b, hb⟩, ⟨w, rfl⟩⟩
    refine ⟨_, ⟨(w - T1 b, b), rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, blockOp_apply, LinearEquiv.coe_coe, shear_apply,
      Prod.smul_mk, Prod.mk.injEq, sub_add_cancel, and_true]
    rw [← hb]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, map_sub, map_smul, hT]
    module

/-- The row/column reduction of the *Proof* of Theorem A of `C11_payment_systems_twist.md`:
if `T0 ∘ T1 = −2 D`, then for every `c`,
`(X × X) ⧸ range (c • blockOp T0 T1 Fs) ≃ (X ⧸ c • ⊤) × (X ⧸ range (c • 2 • (Fs + D)))`. -/
noncomputable def blockCokerEquiv (T0 T1 Fs D : X →ₗ[A] X) (h : T0 ∘ₗ T1 = -(2 : A) • D)
    (c : A) :
    ((X × X) ⧸ LinearMap.range (c • blockOp T0 T1 Fs)) ≃ₗ[A]
      (X ⧸ c • (⊤ : Submodule A X)) × (X ⧸ LinearMap.range (c • (2 : A) • (Fs + D))) :=
  ((Submodule.Quotient.equiv _ _ (shear T0) (map_shear_range T0 T1 Fs D h c)).trans
    (quotProdEquiv _ _)).trans (LinearEquiv.prodComm A _ _)

end Payment
