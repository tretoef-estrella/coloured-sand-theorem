module

public import RequestProject.WeylFilt.PartM

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: Part S — Lemma 2.4

* (S1) `S1`: for `m ≥ 1`, `Δ_A(m+1) —fΔ→ V ⊗ Δ_A(m) —gΔ→ Δ_A(m−1)` is a short exact sequence.
* (S2) `S2`: for `m ≥ 1`, `∇_A(m−1) —f∇→ V ⊗ ∇_A(m) —g∇→ ∇_A(m+1)` is a short exact sequence.
* (S3) `S3`: `fΔ(e'_0) = b_0 e_0`, and `range fΔ` is the `A`-span of the `F^{(R)}(b_0 e_0)`,
  `0 ≤ R ≤ m+1` (for every `m`; the file states it for `m ≥ 1`).
* (S4) `S4_delta`, `S4_nabla`: `V ⊗ Δ_A(0) ≅ V` and `V ⊗ ∇_A(0) ≅ V` by morphisms both ways whose
  composites are the identities.

Everything holds over an arbitrary commutative ring `A`.
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-- (auxiliary) the vector of `Fin N → A` with coordinates given by `f`. -/
def mkV (N : ℕ) (f : ℕ → A) : Fin N → A := fun i => f i

lemma ext0_mkV {N : ℕ} (f : ℕ → A) (k : ℕ) :
    ext0 (mkV N f) k = if k < N then f k else 0 := by
  unfold ext0 mkV; split_ifs <;> rfl

/-- (auxiliary) the vector of `V ⊗ M` with slots given by `f` and `g`. -/
def mkT (l : ℕ) (f g : ℕ → A) : Fin 2 × Fin (l + 1) → A := fun p => if p.1 = 0 then f p.2 else g p.2

lemma ext0_slice0_mkT {l : ℕ} (f g : ℕ → A) (k : ℕ) :
    ext0 (slice 0 (mkT l f g)) k = if k < l + 1 then f k else 0 := by
  unfold ext0; split_ifs <;> simp [mkT]

lemma ext0_slice1_mkT {l : ℕ} (f g : ℕ → A) (k : ℕ) :
    ext0 (slice 1 (mkT l f g)) k = if k < l + 1 then g k else 0 := by
  unfold ext0; split_ifs <;> simp [mkT]

/-- (S1) Lemma 2.4 for `Δ`: for every `m ≥ 1`, `Δ_A(m+1) —fΔ→ V ⊗ Δ_A(m) —gΔ→ Δ_A(m−1)` is a
short exact sequence (`fΔ` injective, `gΔ` surjective, `range fΔ = ker gΔ`). -/
theorem S1 (m : ℕ) (hm : 1 ≤ m) : ShortExact (fDelta A m) (gDelta A m hm) where
  inj := by
    intro x y hxy
    change fDeltaLin m x = fDeltaLin m y at hxy
    rw [fDeltaLin_eq] at hxy
    refine ext_ext0 fun n hn => ?_
    by_cases h : n ≤ m
    · have := congrArg (fun w => ext0 (slice 0 w) n) hxy
      simpa [ext0_slice0_fDelta, h] using this
    · have := congrArg (fun w => ext0 (slice 1 w) m) hxy
      simp only [ext0_slice1_fDelta, le_refl, if_true] at this
      rwa [show n = m + 1 by omega]
  surj := by
    intro z
    refine ⟨mkT m (fun _ => 0) (fun k => ext0 z k), ?_⟩
    change gDeltaLin m _ = z
    rw [gDeltaLin_eq]
    refine ext_ext0 fun n hn => ?_
    rw [ext0_gDelta, ext0_slice0_mkT, ext0_slice1_mkT]
    rw [if_pos (by omega), if_pos (by omega)]
    simp
  exact := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change gDeltaLin m (fDeltaLin m x) = 0
      rw [gDeltaLin_eq, fDeltaLin_eq]
      refine ext_ext0 fun n hn => ?_
      rw [ext0_gDelta, ext0_slice0_fDelta, ext0_slice1_fDelta, ext0_zero]
      split_ifs <;> first | (exfalso; omega) | simp
    · intro hy
      change gDeltaLin m y = 0 at hy
      rw [gDeltaLin_eq] at hy
      have hy' : ∀ n, n ≤ m - 1 → ext0 (slice 1 y) n = ext0 (slice 0 y) (n + 1) := by
        intro n hn
        have := congrArg (fun w => ext0 w n) hy
        simp only [ext0_gDelta, if_pos hn, ext0_zero] at this
        exact sub_eq_zero.mp this
      refine ⟨mkV (m + 1 + 1) fun n => if n ≤ m then ext0 (slice 0 y) n else ext0 (slice 1 y) m, ?_⟩
      change fDeltaLin m _ = y
      rw [fDeltaLin_eq]
      refine ext_tensor (fun n hn => ?_) (fun n hn => ?_)
      · rw [ext0_slice0_fDelta, ext0_mkV, if_pos hn, if_pos (by omega), if_pos hn]
      · rw [ext0_slice1_fDelta, ext0_mkV, if_pos hn, if_pos (by omega)]
        split_ifs with h
        · exact (hy' n (by omega)).symm
        · rw [show n = m by omega]

/-- (S2) Lemma 2.4 for `∇`: for every `m ≥ 1`, `∇_A(m−1) —f∇→ V ⊗ ∇_A(m) —g∇→ ∇_A(m+1)` is a
short exact sequence (`f∇` injective, `g∇` surjective, `range f∇ = ker g∇`). -/
theorem S2 (m : ℕ) (hm : 1 ≤ m) : ShortExact (fNabla A m hm) (gNabla A m) where
  inj := by
    intro x y hxy
    change fNablaLin m x = fNablaLin m y at hxy
    rw [fNablaLin_eq] at hxy
    refine ext_ext0 fun n hn => ?_
    have := congrArg (fun w => ext0 (slice 1 w) n) hxy
    simpa [ext0_slice1_fNabla, show n ≤ m by omega] using this
  surj := by
    intro z
    refine ⟨mkT m (fun k => ext0 z k) (fun k => if k = m then ext0 z (m + 1) else 0), ?_⟩
    change gNablaLin m _ = z
    rw [gNablaLin_eq]
    refine ext_ext0 fun n hn => ?_
    rw [ext0_gNabla, ext0_slice0_mkT, ext0_slice1_mkT, if_pos (by omega)]
    split_ifs <;> first | (exfalso; omega) | (rw [show n = m + 1 by omega]; simp) | simp
  exact := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change gNablaLin m (fNablaLin m x) = 0
      rw [gNablaLin_eq, fNablaLin_eq]
      refine ext_ext0 fun n hn => ?_
      rw [ext0_gNabla, ext0_slice0_fNabla, ext0_slice1_fNabla, ext0_zero]
      split_ifs <;> first | (exfalso; omega) | (rw [ext0_of_ge _ _ (by omega)]; simp) | simp
    · intro hy
      change gNablaLin m y = 0 at hy
      rw [gNablaLin_eq] at hy
      have hy' : ∀ n, n ≤ m + 1 →
          ext0 (slice 0 y) n + (if 1 ≤ n then ext0 (slice 1 y) (n - 1) else 0) = 0 := by
        intro n hn
        have := congrArg (fun w => ext0 w n) hy
        simpa only [ext0_gNabla, if_pos hn, ext0_zero] using this
      refine ⟨mkV (m - 1 + 1) fun r => -ext0 (slice 1 y) r, ?_⟩
      change fNablaLin m _ = y
      rw [fNablaLin_eq]
      refine ext_tensor (fun n hn => ?_) (fun n hn => ?_)
      · rw [ext0_slice0_fNabla, ext0_mkV]
        have h := hy' n (by omega)
        split_ifs at h ⊢ with h1 h2 <;> first | (exfalso; omega) | skip
        · linear_combination -h
        · simpa using h.symm
      · rw [ext0_slice1_fNabla, ext0_mkV, if_pos hn]
        split_ifs with h1
        · simp
        · have h := hy' (m + 1) le_rfl
          rw [ext0_of_ge _ _ (by omega), if_pos (by omega), Nat.add_sub_cancel] at h
          rw [show n = m by omega]; simpa using h.symm

end WeylFilt

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-- (S3) `fΔ(e'_0) = b_0 e_0`, and the image of `fΔ` is the sublattice generated by `b_0 e_0`:
`range fΔ` is the `A`-span of the vectors `F^{(R)}(b_0 e_0)`, `0 ≤ R ≤ m+1`. (This holds for every
`m`; the file states it for `m ≥ 1`.) -/
theorem S3 (m : ℕ) :
    (fDelta A m).toLin (Pi.single (0 : Fin (m + 1 + 1)) 1) = bvec 0 (Pi.single (0 : Fin (m + 1)) 1) ∧
    LinearMap.range (fDelta A m).toLin = Submodule.span A (Set.range fun R : Fin (m + 1 + 1) =>
      (tensorV (delta A m)).Fd R (bvec 0 (Pi.single (0 : Fin (m + 1)) 1))) := by
  have h0 : (fDelta A m).toLin (Pi.single (0 : Fin (m + 1 + 1)) 1) =
      bvec 0 (Pi.single (0 : Fin (m + 1)) 1) := by
    change fDeltaLin m _ = _
    rw [fDeltaLin_single]
    have h1 := ev_fin (A := A) m 0
    simp only [Fin.val_zero, Nat.cast_zero, zero_sub] at h1 ⊢
    rw [ev_of_lt m (-1) (by norm_num), map_zero, add_zero, h1]
  refine ⟨h0, ?_⟩
  have key : (fun R : Fin (m + 1 + 1) =>
      (tensorV (delta A m)).Fd R (bvec 0 (Pi.single (0 : Fin (m + 1)) 1))) =
      (fDelta A m).toLin ∘ (Pi.basisFun A (Fin (m + 1 + 1))) := by
    funext R
    erw [← h0]
    rw [Function.comp_apply, ← LinearMap.comp_apply, ← (fDelta A m).comm_F,
      LinearMap.comp_apply, Pi.basisFun_apply]
    congr 1
    rw [delta_Fd_single, dif_pos (by simp; omega)]
    simp
  rw [key, Set.range_comp, Submodule.span_image, (Pi.basisFun A _).span_eq, Submodule.map_top]

/-! ### (S4) -/

/-- (S4, auxiliary) a morphism whose underlying map has a two-sided linear inverse `g`; then `g` is
a morphism. -/
def Hom.ofInverse {M N : DPLattice A} (f : Hom M N) (g : (N.ι → A) →ₗ[A] (M.ι → A))
    (h1 : g ∘ₗ f.toLin = LinearMap.id) (h2 : f.toLin ∘ₗ g = LinearMap.id) : Hom N M where
  toLin := g
  comm_F r := by
    refine LinearMap.ext fun v => ?_
    have e1 : ∀ w, g (f.toLin w) = w := fun w => LinearMap.congr_fun h1 w
    have e2 : ∀ v, f.toLin (g v) = v := fun v => LinearMap.congr_fun h2 v
    have hc : ∀ w, f.toLin (M.Fd r w) = N.Fd r (f.toLin w) :=
      fun w => LinearMap.congr_fun (f.comm_F r) w
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← e2 v]
    rw [← hc, e1]
  comm_E r := by
    refine LinearMap.ext fun v => ?_
    have e1 : ∀ w, g (f.toLin w) = w := fun w => LinearMap.congr_fun h1 w
    have e2 : ∀ v, f.toLin (g v) = v := fun v => LinearMap.congr_fun h2 v
    have hc : ∀ w, f.toLin (M.Ed r w) = N.Ed r (f.toLin w) :=
      fun w => LinearMap.congr_fun (f.comm_E r) w
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← e2 v]
    rw [← hc, e1]
  comm_H := by
    refine LinearMap.ext fun v => ?_
    have e1 : ∀ w, g (f.toLin w) = w := fun w => LinearMap.congr_fun h1 w
    have e2 : ∀ v, f.toLin (g v) = v := fun v => LinearMap.congr_fun h2 v
    have hc : ∀ w, f.toLin (H M w) = H N (f.toLin w) :=
      fun w => LinearMap.congr_fun f.comm_H w
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← e2 v]
    rw [← hc, e1]

/-- (S4, auxiliary) the identification morphism `M → N` given by an equality `M = N` of
DP-lattices (used with C18 (T5): `Δ_A(1) = V = ∇_A(1)`). -/
def Hom.ofEq {M N : DPLattice A} (h : M = N) : Hom M N := h ▸ Hom.id M

lemma Hom.ofEq_comp {M N : DPLattice A} (h : M = N) :
    (Hom.ofEq h.symm).toLin ∘ₗ (Hom.ofEq h).toLin = LinearMap.id ∧
    (Hom.ofEq h).toLin ∘ₗ (Hom.ofEq h.symm).toLin = LinearMap.id := by
  subst h; exact ⟨rfl, rfl⟩

/-- (S4, auxiliary) the inverse of `fΔ : Δ_A(1) → V ⊗ Δ_A(0)`: `b_0 e_0 ↦ e'_0`, `b_1 e_0 ↦ e'_1`. -/
def fDelta0Inv : (Fin 2 × Fin (0 + 1) → A) →ₗ[A] (Fin (0 + 1 + 1) → A) where
  toFun w := mkV (0 + 1 + 1) fun k => if k = 0 then ext0 (slice 0 w) 0 else ext0 (slice 1 w) 0
  map_add' v w := by funext i; simp only [mkV, map_add, ext0_add, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c v := by
    funext i; simp only [mkV, map_smul, ext0_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

/-- (S4, auxiliary) the inverse of `g∇ : V ⊗ ∇_A(0) → ∇_A(1)`: `w'_0 ↦ b_0 w_0`, `w'_1 ↦ b_1 w_0`. -/
def gNabla0Inv : (Fin (0 + 1 + 1) → A) →ₗ[A] (Fin 2 × Fin (0 + 1) → A) where
  toFun x := mkT 0 (fun k => ext0 x k) (fun k => ext0 x (k + 1))
  map_add' v w := by funext p; simp only [mkT, ext0_add, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c v := by
    funext p; simp only [mkT, ext0_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

lemma fDelta0_inv :
    fDelta0Inv (A := A) ∘ₗ (fDelta A 0).toLin = LinearMap.id ∧
    (fDelta A 0).toLin ∘ₗ fDelta0Inv (A := A) = LinearMap.id := by
  constructor
  · refine LinearMap.ext fun x => ext_ext0 fun n hn => ?_
    change ext0 (fDelta0Inv (fDeltaLin 0 x)) n = ext0 x n
    rw [fDeltaLin_eq]
    simp only [fDelta0Inv, LinearMap.coe_mk, AddHom.coe_mk, ext0_mkV, ext0_slice0_fDelta,
      ext0_slice1_fDelta]
    interval_cases n <;> simp
  · refine LinearMap.ext fun w => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
    all_goals
      change ext0 (slice _ (fDeltaLin 0 (fDelta0Inv w))) n = _
      rw [fDeltaLin_eq]
      simp only [fDelta0Inv, LinearMap.coe_mk, AddHom.coe_mk, ext0_mkV, ext0_slice0_fDelta,
        ext0_slice1_fDelta]
      interval_cases n
      simp only [le_refl, if_true, zero_add, one_ne_zero]
      rfl

lemma gNabla0_inv :
    gNabla0Inv (A := A) ∘ₗ (gNabla A 0).toLin = LinearMap.id ∧
    (gNabla A 0).toLin ∘ₗ gNabla0Inv (A := A) = LinearMap.id := by
  constructor
  · refine LinearMap.ext fun w => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
    all_goals
      change ext0 (slice _ (gNabla0Inv (gNablaLin 0 w))) n = ext0 (slice _ w) n
      rw [gNablaLin_eq]
      simp only [gNabla0Inv, LinearMap.coe_mk, AddHom.coe_mk, ext0_slice0_mkT, ext0_slice1_mkT,
        ext0_gNabla]
      interval_cases n
      simp [ext0_of_ge (slice 0 w) 1 le_rfl]
  · refine LinearMap.ext fun x => ext_ext0 fun n hn => ?_
    change ext0 (gNablaLin 0 (gNabla0Inv x)) n = ext0 x n
    rw [gNablaLin_eq]
    simp only [gNabla0Inv, LinearMap.coe_mk, AddHom.coe_mk, ext0_slice0_mkT, ext0_slice1_mkT,
      ext0_gNabla]
    interval_cases n <;> simp

/-- (S4) the morphism `V ⊗ Δ_A(0) → V`: the inverse of `fΔ : Δ_A(1) → V ⊗ Δ_A(0)` followed by the
identification `Δ_A(1) = V` of C18 (T5). -/
def phiDelta (A : Type*) [CommRing A] : Hom (tensorV (delta A 0)) (V A) :=
  Hom.comp (Hom.ofEq T5_delta_one) (Hom.ofInverse (fDelta A 0) fDelta0Inv fDelta0_inv.1 fDelta0_inv.2)

/-- (S4) the morphism `V → V ⊗ Δ_A(0)`: the identification `V = Δ_A(1)` of C18 (T5) followed by
`fΔ : Δ_A(1) → V ⊗ Δ_A(0)` (`e'_0 ↦ b_0 e_0`, `e'_1 ↦ b_1 e_0`). -/
def psiDelta (A : Type*) [CommRing A] : Hom (V A) (tensorV (delta A 0)) :=
  Hom.comp (fDelta A 0) (Hom.ofEq T5_delta_one.symm)

/-- (S4) the morphism `V ⊗ ∇_A(0) → V`: `g∇ : V ⊗ ∇_A(0) → ∇_A(1)` (`b_0 w_0 ↦ w'_0`,
`b_1 w_0 ↦ w'_1`) followed by the identification `∇_A(1) = V` of C18 (T5). -/
def phiNabla (A : Type*) [CommRing A] : Hom (tensorV (nabla A 0)) (V A) :=
  Hom.comp (Hom.ofEq T5_nabla_one) (gNabla A 0)

/-- (S4) the morphism `V → V ⊗ ∇_A(0)`: the identification `V = ∇_A(1)` of C18 (T5) followed by the
inverse of `g∇`. -/
def psiNabla (A : Type*) [CommRing A] : Hom (V A) (tensorV (nabla A 0)) :=
  Hom.comp (Hom.ofInverse (gNabla A 0) gNabla0Inv gNabla0_inv.1 gNabla0_inv.2)
    (Hom.ofEq T5_nabla_one.symm)

/-- (S4) `V ⊗ Δ_A(0) ≅ V` as DP-lattices: the morphisms `phiDelta A : V ⊗ Δ_A(0) → V` and
`psiDelta A : V → V ⊗ Δ_A(0)` have both composites equal to the identities. -/
theorem S4_delta :
    Hom.comp (psiDelta A) (phiDelta A) = Hom.id _ ∧ Hom.comp (phiDelta A) (psiDelta A) = Hom.id _ := by
  obtain ⟨e1, e2⟩ := Hom.ofEq_comp (T5_delta_one (A := A))
  obtain ⟨i1, i2⟩ := fDelta0_inv (A := A)
  constructor
  · refine Hom.ext' ?_
    change (fDelta A 0).toLin ∘ₗ (Hom.ofEq T5_delta_one.symm).toLin ∘ₗ
      ((Hom.ofEq T5_delta_one).toLin ∘ₗ fDelta0Inv) = LinearMap.id
    rw [← LinearMap.comp_assoc fDelta0Inv, e1, LinearMap.id_comp, i2]
  · refine Hom.ext' ?_
    change (Hom.ofEq T5_delta_one).toLin ∘ₗ fDelta0Inv ∘ₗ
      ((fDelta A 0).toLin ∘ₗ (Hom.ofEq T5_delta_one.symm).toLin) = LinearMap.id
    rw [← LinearMap.comp_assoc (Hom.ofEq T5_delta_one.symm).toLin, i1, LinearMap.id_comp, e2]

/-- (S4) `V ⊗ ∇_A(0) ≅ V` as DP-lattices: the morphisms `phiNabla A : V ⊗ ∇_A(0) → V` and
`psiNabla A : V → V ⊗ ∇_A(0)` have both composites equal to the identities. -/
theorem S4_nabla :
    Hom.comp (psiNabla A) (phiNabla A) = Hom.id _ ∧ Hom.comp (phiNabla A) (psiNabla A) = Hom.id _ := by
  obtain ⟨e1, e2⟩ := Hom.ofEq_comp (T5_nabla_one (A := A))
  obtain ⟨i1, i2⟩ := gNabla0_inv (A := A)
  constructor
  · refine Hom.ext' ?_
    change gNabla0Inv ∘ₗ (Hom.ofEq T5_nabla_one.symm).toLin ∘ₗ
      ((Hom.ofEq T5_nabla_one).toLin ∘ₗ (gNabla A 0).toLin) = LinearMap.id
    rw [← LinearMap.comp_assoc (gNabla A 0).toLin, e1, LinearMap.id_comp, i1]
  · refine Hom.ext' ?_
    change (Hom.ofEq T5_nabla_one).toLin ∘ₗ (gNabla A 0).toLin ∘ₗ
      (gNabla0Inv ∘ₗ (Hom.ofEq T5_nabla_one.symm).toLin) = LinearMap.id
    rw [← LinearMap.comp_assoc (Hom.ofEq T5_nabla_one.symm).toLin, i2, LinearMap.id_comp, e2]

/-- (S4) `V ⊗ Δ_A(0) ≅ V` and `V ⊗ ∇_A(0) ≅ V` as DP-lattices: in each case there are morphisms
both ways whose composites are the identities. -/
theorem S4 :
    (∃ (φ : Hom (tensorV (delta A 0)) (V A)) (ψ : Hom (V A) (tensorV (delta A 0))),
      Hom.comp ψ φ = Hom.id _ ∧ Hom.comp φ ψ = Hom.id _) ∧
    (∃ (φ : Hom (tensorV (nabla A 0)) (V A)) (ψ : Hom (V A) (tensorV (nabla A 0))),
      Hom.comp ψ φ = Hom.id _ ∧ Hom.comp φ ψ = Hom.id _) :=
  ⟨⟨_, _, S4_delta⟩, ⟨_, _, S4_nabla⟩⟩

end WeylFilt
