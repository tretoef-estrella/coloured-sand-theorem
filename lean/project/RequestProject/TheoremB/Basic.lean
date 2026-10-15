module

public import RequestProject.Splitting.All
public import RequestProject.Strings.All

/-!
# Theorem B: objects and general lemmas on `p`-primary components and torsion

This file corresponds to **§0 (Objects)** of `CS3_theorem_B.md`.

## Encoding

* The Laplacian `L` of `H(d,q)` is `ColouredSand.Splitting.laplacian d q`, acting on
  `(Fin d → Fin q) → ℤ` (as in CS2), and `coker L` is `((Fin d → Fin q) → ℤ) ⧸ LinearMap.range L`
  (`cokerL d q`).
* The **sandpile group** `K(H(d,q))` is `sandpile d q := Submodule.torsion ℤ (coker L)`, the
  torsion subgroup of `coker L` (the elements killed by some nonzero integer), viewed as an abelian
  group (a `ℤ`-submodule of `coker L`).
* For an abelian group `G` and a prime `p`, `Syl_p G` (the `p`-primary component, i.e. the
  elements of `p`-power order) is Mathlib's `AddCommGroup.primaryComponent G p`,
  `{g | ∃ n, addOrderOf g = p ^ n}`.  The lemma `mem_primaryComponent_iff` shows that this is
  `{g | ∃ n, p ^ n • g = 0}`.
* "`≅` as abelian groups" is the existence of an additive group isomorphism `≃+`.

The rest of the file contains general transport lemmas for `p`-primary components and torsion
submodules (along isomorphisms, finite products, and products with a torsion-free factor).
-/

@[expose] public section

open Finset

namespace ColouredSand.TheoremB

/-- `coker L = ((Fin d → Fin q) → ℤ) ⧸ range L` for the Laplacian `L` of the Hamming graph
`H(d,q)` (§0). -/
abbrev cokerL (d q : ℕ) : Type :=
  ((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (ColouredSand.Splitting.laplacian d q)

/-- The **sandpile group** `K(H(d,q))` (§0): the torsion subgroup of `coker L`, encoded as the
torsion `ℤ`-submodule `Submodule.torsion ℤ (coker L)` (elements killed by a nonzero integer). -/
noncomputable abbrev sandpile (d q : ℕ) : Submodule ℤ (cokerL d q) := Submodule.torsion ℤ (cokerL d q)

/-! ### `p`-primary components -/

section primary

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Syl_p G = {g | ∃ n, p ^ n • g = 0}`. -/
lemma mem_primaryComponent_iff {G : Type*} [AddCommGroup G] (x : G) :
    x ∈ AddCommGroup.primaryComponent G p ↔ ∃ n : ℕ, p ^ n • x = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn ▸ addOrderOf_nsmul_eq_zero x⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn)
    exact ⟨k, hk⟩

/-- `Syl_p` as a `ℤ`-submodule. -/
abbrev sylSub (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G] : Submodule ℤ G :=
  (AddCommGroup.primaryComponent G p).toIntSubmodule

lemma mem_sylSub_iff {G : Type*} [AddCommGroup G] (x : G) :
    x ∈ sylSub p G ↔ ∃ n : ℕ, p ^ n • x = 0 :=
  mem_primaryComponent_iff x

/-- A linear equivalence restricts to submodules corresponding to each other. -/
def subEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
    [Module R N] (P : Submodule R M) (Q : Submodule R N) (e : M ≃ₗ[R] N)
    (h : ∀ x, x ∈ P ↔ e x ∈ Q) : P ≃ₗ[R] Q :=
  (e.submoduleMap P).trans (LinearEquiv.ofEq _ _ (by
    ext y
    simp only [Submodule.mem_map_equiv]
    rw [h, LinearEquiv.apply_symm_apply]))

/-- `Syl_p` is transported along isomorphisms. -/
def sylEquiv {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃ₗ[ℤ] G') :
    sylSub p G ≃ₗ[ℤ] sylSub p G' :=
  subEquiv _ _ e fun x => by
    rw [mem_sylSub_iff, mem_sylSub_iff]
    refine exists_congr fun n => ?_
    rw [← map_nsmul, e.map_eq_zero_iff]

/-- `Syl_p (∏ᵢ Gᵢ) = ∏ᵢ Syl_p Gᵢ` (finite products). -/
def sylPi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] :
    sylSub p (∀ i, G i) ≃ₗ[ℤ] ∀ i, sylSub p (G i) where
  toFun x i := ⟨x.1 i, by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp x.2
    exact (mem_sylSub_iff _).mpr ⟨n, by simpa using congrFun hn i⟩⟩
  invFun y := ⟨fun i => (y i).1, by
    classical
    choose n hn using fun i => (mem_sylSub_iff _).mp (y i).2
    refine (mem_sylSub_iff _).mpr ⟨∑ i, n i, funext fun i => ?_⟩
    have hle : n i ≤ ∑ j, n j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [← Nat.sub_add_cancel hle, pow_add, mul_comm, mul_nsmul, hn i, nsmul_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Syl_p (F × T) ≅ Syl_p T` when `Syl_p F = 0`. -/
def sylProdOfBot {F T : Type*} [AddCommGroup F] [AddCommGroup T] (hF : sylSub p F = ⊥) :
    sylSub p (F × T) ≃ₗ[ℤ] sylSub p T where
  toFun x := ⟨x.1.2, by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp x.2
    exact (mem_sylSub_iff _).mpr ⟨n, by simpa using congrArg Prod.snd hn⟩⟩
  invFun y := ⟨(0, y.1), by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp y.2
    exact (mem_sylSub_iff _).mpr ⟨n, by simp [hn]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp x.2
    have h1 : x.1.1 ∈ sylSub p F := (mem_sylSub_iff _).mpr ⟨n, by simpa using congrArg Prod.fst hn⟩
    rw [hF, Submodule.mem_bot] at h1
    ext <;> simp [h1]
  right_inv _ := rfl

lemma pow_mem_nonZeroDivisors_int (n : ℕ) : (p : ℤ) ^ n ∈ nonZeroDivisors ℤ :=
  mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))

lemma mem_torsion_of_pow_smul {F : Type*} [AddCommGroup F] {x : F} {n : ℕ}
    (hn : p ^ n • x = 0) : x ∈ Submodule.torsion ℤ F := by
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨(p : ℤ) ^ n, pow_mem_nonZeroDivisors_int n⟩, ?_⟩
  simp only [Submonoid.mk_smul]
  rw [← natCast_zsmul] at hn
  exact_mod_cast hn

/-- `Syl_p` of a torsion-free group is trivial. -/
lemma sylSub_eq_bot_of_torsion {F : Type*} [AddCommGroup F] (hF : Submodule.torsion ℤ F = ⊥) :
    sylSub p F = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp hx
  have := mem_torsion_of_pow_smul hn
  rwa [hF] at this

/-- `Syl_p` of the torsion subgroup of `G` is `Syl_p G` (elements of `p`-power order are
torsion). -/
def sylTorsion (G : Type*) [AddCommGroup G] :
    sylSub p (Submodule.torsion ℤ G) ≃ₗ[ℤ] sylSub p G where
  toFun x := ⟨x.1.1, by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp x.2
    exact (mem_sylSub_iff _).mpr ⟨n, by simpa using congrArg Subtype.val hn⟩⟩
  invFun y := ⟨⟨y.1, by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp y.2
    exact mem_torsion_of_pow_smul hn⟩, by
    obtain ⟨n, hn⟩ := (mem_sylSub_iff _).mp y.2
    exact (mem_sylSub_iff _).mpr ⟨n, Subtype.ext (by simpa using hn)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end primary

/-! ### Torsion submodules -/

section torsion

variable {R : Type*} [CommRing R]

/-- Torsion is transported along linear equivalences. -/
def torsionEquiv {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : Submodule.torsion R M ≃ₗ[R] Submodule.torsion R N :=
  subEquiv _ _ e fun x => by
    rw [Submodule.mem_torsion_iff, Submodule.mem_torsion_iff]
    refine exists_congr fun a => ?_
    rw [Submonoid.smul_def, Submonoid.smul_def, ← map_smul, e.map_eq_zero_iff]

/-- Torsion of a finite product is the product of the torsions. -/
def torsionPi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    Submodule.torsion R (∀ i, M i) ≃ₗ[R] ∀ i, Submodule.torsion R (M i) where
  toFun x i := ⟨x.1 i, by
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp x.2
    exact (Submodule.mem_torsion_iff _).mpr ⟨a, by simpa using congrFun ha i⟩⟩
  invFun y := ⟨fun i => (y i).1, by
    classical
    choose a ha using fun i => (Submodule.mem_torsion_iff _).mp (y i).2
    refine (Submodule.mem_torsion_iff _).mpr ⟨∏ i, a i, funext fun i => ?_⟩
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), mul_comm, mul_smul, ha i, smul_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `torsion (F × T) ≅ T` when `F` is torsion-free and `T` is torsion. -/
def torsionProdFree {F T : Type*} [AddCommGroup F] [Module R F] [AddCommGroup T] [Module R T]
    (hF : Submodule.torsion R F = ⊥) (hT : Submodule.torsion R T = ⊤) :
    Submodule.torsion R (F × T) ≃ₗ[R] T where
  toFun x := x.1.2
  invFun y := ⟨(0, y), by
    have hy : y ∈ Submodule.torsion R T := hT ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hy
    exact (Submodule.mem_torsion_iff _).mpr ⟨a, by simp [ha]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp x.2
    have h1 : x.1.1 ∈ Submodule.torsion R F :=
      (Submodule.mem_torsion_iff _).mpr ⟨a, by simpa using congrArg Prod.fst ha⟩
    rw [hF, Submodule.mem_bot] at h1
    ext <;> simp [h1]
  right_inv _ := rfl

/-- `torsion M ≅ M` when `M` is torsion. -/
def torsionOfTop {M : Type*} [AddCommGroup M] [Module R M] (hT : Submodule.torsion R M = ⊤) :
    Submodule.torsion R M ≃ₗ[R] M :=
  (LinearEquiv.ofEq _ _ hT).trans (LinearEquiv.ofTop ⊤ rfl)

/-- A module killed by a non-zero-divisor is torsion. -/
lemma torsion_eq_top_of_smul {M : Type*} [AddCommGroup M] [Module R M] (a : R)
    (ha : a ∈ nonZeroDivisors R) (h : ∀ x : M, a • x = 0) : Submodule.torsion R M = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact (Submodule.mem_torsion_iff _).mpr ⟨⟨a, ha⟩, h x⟩

/-- Over a domain, a free module (`ι → R`) is torsion-free. -/
lemma torsion_pi_eq_bot [IsDomain R] (ι : Type*) : Submodule.torsion R (ι → R) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff _).mp hx
  rw [Submodule.mem_bot]
  funext i
  have := congrFun hax i
  simp only [Submonoid.mk_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left (nonZeroDivisors.ne_zero ha)

end torsion

end ColouredSand.TheoremB
