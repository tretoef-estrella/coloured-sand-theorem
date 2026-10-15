module

public import RequestProject.DPLattice.All

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: Setting

Encodings (namespace `WeylFilt`), reusing C18 (namespace `DPLattice`):

* DP-lattices, `IsDP`, `H`, `Hom`, `one`, `V`, `tensorV`, `bvec`, `delta`, `nabla` are those of
  C18. `delta A l = Δ_A(l)` and `nabla A l = ∇_A(l)` have basis `Fin (l + 1)` (the basis vector
  `r` is `e_r`, resp. `w_r`, i.e. `Pi.single r 1`). `tensorV M = V ⊗ M` has basis `Fin 2 × M.ι`;
  the vector `b_e m` is `bvec e m`.
* `ev l k` (for `k : ℤ`) is the vector `e_k` of `Δ_A(l)` (or `w_k` of `∇_A(l)`) when
  `0 ≤ k ≤ l`, and `0` otherwise ("`e_r := 0` when `r < 0` or `r > λ`").
* `Hom.id M`, `Hom.comp g f` are the identity and the composition of morphisms (Setting,
  "Morphisms").
* `ShortExact f g` (Setting, "Short exact sequence"): `f` injective, `g` surjective and
  `range f = ker g` as `A`-submodules.
* `ext0 u k` (auxiliary, for proofs) is the coordinate `k : ℕ` of `u : Fin n → A`, and `0` when
  `k ≥ n`.
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-- Setting: `ev l k` is `e_k ∈ Δ_A(l)` (or `w_k ∈ ∇_A(l)`) if `0 ≤ k ≤ l`, and `0` otherwise. -/
def ev (l : ℕ) (k : ℤ) : Fin (l + 1) → A := fun j => if (j : ℤ) = k then 1 else 0

lemma ev_fin (l : ℕ) (r : Fin (l + 1)) : ev (A := A) l (r : ℕ) = Pi.single r 1 := by
  funext j; simp [ev, Pi.single_apply, Fin.ext_iff]

lemma ev_of_lt (l : ℕ) (k : ℤ) (hk : k < 0) : ev (A := A) l k = 0 := by
  funext j; simp only [ev, Pi.zero_apply]; rw [if_neg]; omega

lemma ev_of_gt (l : ℕ) (k : ℤ) (hk : (l : ℤ) < k) : ev (A := A) l k = 0 := by
  funext j; simp only [ev, Pi.zero_apply]; rw [if_neg]; have := j.isLt; omega

/-! ### Morphisms -/

/-- Setting ("Morphisms"), (M2): the identity morphism `Hom.id M`. -/
def Hom.id (M : DPLattice A) : Hom M M where
  toLin := LinearMap.id
  comm_F _ := by rw [LinearMap.id_comp, LinearMap.comp_id]
  comm_E _ := by rw [LinearMap.id_comp, LinearMap.comp_id]
  comm_H := by rw [LinearMap.id_comp, LinearMap.comp_id]

/-- Setting ("Morphisms"), (M2): the composition `Hom.comp g f = g ∘ f` of morphisms. -/
def Hom.comp {M N P : DPLattice A} (g : Hom N P) (f : Hom M N) : Hom M P where
  toLin := g.toLin ∘ₗ f.toLin
  comm_F r := by rw [LinearMap.comp_assoc, f.comm_F, ← LinearMap.comp_assoc, g.comm_F,
    LinearMap.comp_assoc]
  comm_E r := by rw [LinearMap.comp_assoc, f.comm_E, ← LinearMap.comp_assoc, g.comm_E,
    LinearMap.comp_assoc]
  comm_H := by rw [LinearMap.comp_assoc, f.comm_H, ← LinearMap.comp_assoc, g.comm_H,
    LinearMap.comp_assoc]

lemma Hom.ext' {M N : DPLattice A} {f g : Hom M N} (h : f.toLin = g.toLin) : f = g := by
  cases f; cases g; cases h; rfl

/-! ### Short exact sequences -/

/-- Setting ("Short exact sequence"): `X —f→ Y —g→ Z` is short exact if `f` is injective, `g` is
surjective and `range f = ker g` (as `A`-submodules of `Y`). -/
structure ShortExact {X Y Z : DPLattice A} (f : Hom X Y) (g : Hom Y Z) : Prop where
  inj : Function.Injective f.toLin
  surj : Function.Surjective g.toLin
  exact : LinearMap.range f.toLin = LinearMap.ker g.toLin

/-! ### Coordinates (auxiliary) -/

/-- (auxiliary) the coordinate `k : ℕ` of `u : Fin n → A`, `0` if `k ≥ n`. -/
def ext0 {n : ℕ} (u : Fin n → A) (k : ℕ) : A := if h : k < n then u ⟨k, h⟩ else 0

@[simp] lemma ext0_fin {n : ℕ} (u : Fin n → A) (k : Fin n) : ext0 u k = u k := by
  simp [ext0]

lemma ext0_of_ge {n : ℕ} (u : Fin n → A) (k : ℕ) (hk : n ≤ k) : ext0 u k = 0 := by
  simp [ext0]; omega

@[simp] lemma ext0_add {n : ℕ} (u v : Fin n → A) (k : ℕ) : ext0 (u + v) k = ext0 u k + ext0 v k := by
  unfold ext0; split_ifs <;> simp

@[simp] lemma ext0_sub {n : ℕ} (u v : Fin n → A) (k : ℕ) : ext0 (u - v) k = ext0 u k - ext0 v k := by
  unfold ext0; split_ifs <;> simp

@[simp] lemma ext0_neg {n : ℕ} (u : Fin n → A) (k : ℕ) : ext0 (-u) k = -ext0 u k := by
  unfold ext0; split_ifs <;> simp

@[simp] lemma ext0_smul {n : ℕ} (c : A) (u : Fin n → A) (k : ℕ) : ext0 (c • u) k = c * ext0 u k := by
  unfold ext0; split_ifs <;> simp

@[simp] lemma ext0_zero {n : ℕ} (k : ℕ) : ext0 (0 : Fin n → A) k = 0 := by
  unfold ext0; split_ifs <;> simp

lemma ext_ext0 {n : ℕ} {u v : Fin n → A} (h : ∀ k : ℕ, k < n → ext0 u k = ext0 v k) : u = v := by
  funext k; have := h k k.isLt; simpa using this

lemma ext0_ev (l : ℕ) (k : ℤ) (n : ℕ) :
    ext0 (ev (A := A) l k) n = if n ≤ l ∧ (n : ℤ) = k then 1 else 0 := by
  unfold ext0 ev; split_ifs <;> simp_all; omega

lemma sum_shift (l t n : ℕ) (c : ℕ → A) (u : Fin (l+1) → A) :
    ∑ r : Fin (l+1), (if n = (r:ℕ) + t then c r else 0) * u r =
      if t ≤ n then c (n - t) * ext0 u (n - t) else 0 := by
  split_ifs with h
  · by_cases h2 : n - t < l + 1
    · rw [Finset.sum_eq_single ⟨n - t, h2⟩]
      · simp [ext0, h2]; intro h3; omega
      · intro b _ hb; rw [if_neg, zero_mul]; intro h3; apply hb; ext; simp; omega
      · simp
    · rw [ext0_of_ge _ _ (by omega), mul_zero]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg, zero_mul]; have := r.isLt; omega
  · refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg, zero_mul]; omega

lemma sum_shift' (l s n : ℕ) (c : ℕ → A) (u : Fin (l+1) → A) :
    ∑ r : Fin (l+1), (if n + s = (r:ℕ) then c r else 0) * u r = c (n + s) * ext0 u (n + s) := by
  by_cases h2 : n + s < l + 1
  · rw [Finset.sum_eq_single ⟨n + s, h2⟩]
    · simp [ext0, h2]
    · intro b _ hb; rw [if_neg, zero_mul]; intro h3; apply hb; ext; simp; omega
    · simp
  · rw [ext0_of_ge _ _ (by omega), mul_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg, zero_mul]; have := r.isLt; omega

lemma ext0_deltaF (l t : ℕ) (u : Fin (l + 1) → A) (n : ℕ) :
    ext0 (deltaF l t u) n = if n ≤ l ∧ t ≤ n then (n.choose t : A) * ext0 u (n - t) else 0 := by
  by_cases hn : n < l + 1
  · simp only [ext0, hn, dif_pos, deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      deltaMatF]
    rw [sum_shift l t n (fun r => ((r + t).choose t : A)) u]
    by_cases ht : t ≤ n
    · simp [ht, show n ≤ l by omega, Nat.sub_add_cancel ht, ext0]
    · simp [ht]
  · rw [ext0_of_ge _ _ (by omega), if_neg (by omega)]

lemma ext0_deltaE (l s : ℕ) (u : Fin (l + 1) → A) (n : ℕ) :
    ext0 (deltaE l s u) n = if n ≤ l then ((l - n).choose s : A) * ext0 u (n + s) else 0 := by
  by_cases hn : n < l + 1
  · simp only [ext0, hn, dif_pos, deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      deltaMatE]
    rw [sum_shift' l s n (fun r => ((l - r + s).choose s : A)) u]
    rw [if_pos (by omega)]
    by_cases h2 : n + s < l + 1
    · rw [show l - (n + s) + s = l - n by omega]; rfl
    · simp [ext0, h2]
  · rw [ext0_of_ge _ _ (by omega), if_neg (by omega)]

lemma ext0_nablaF (l t : ℕ) (u : Fin (l + 1) → A) (n : ℕ) :
    ext0 (nablaF l t u) n =
      if n ≤ l ∧ t ≤ n then ((l - (n - t)).choose t : A) * ext0 u (n - t) else 0 := by
  by_cases hn : n < l + 1
  · simp only [ext0, hn, dif_pos, nablaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      nablaMatF]
    rw [sum_shift l t n (fun r => ((l - r).choose t : A)) u]
    by_cases ht : t ≤ n
    · simp [ht, show n ≤ l by omega, ext0]
    · simp [ht]
  · rw [ext0_of_ge _ _ (by omega), if_neg (by omega)]

lemma ext0_nablaE (l s : ℕ) (u : Fin (l + 1) → A) (n : ℕ) :
    ext0 (nablaE l s u) n = if n ≤ l then ((n + s).choose s : A) * ext0 u (n + s) else 0 := by
  by_cases hn : n < l + 1
  · simp only [ext0, hn, dif_pos, nablaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      nablaMatE]
    rw [sum_shift' l s n (fun r => ((r : ℕ).choose s : A)) u]
    rw [if_pos (by omega)]
    rfl
  · rw [ext0_of_ge _ _ (by omega), if_neg (by omega)]

end WeylFilt
