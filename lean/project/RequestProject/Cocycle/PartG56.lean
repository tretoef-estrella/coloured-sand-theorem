module

public import RequestProject.Cocycle.PartG

/-!
# `C27_cocycles_and_filtrations.md`: Part G — (G5) splitting, (G6) change of the ends

Encodings (namespace `Cocycle`):

* (G5) a section of `proj` is `s : Hom M (glue M N c hc)` with
  `Hom.comp (proj M N c hc) s = Hom.id M`; a retraction of `incl` is
  `r : Hom (glue M N c hc) N` with `Hom.comp r (incl M N c hc) = Hom.id N`.
  For a coboundary `c = dψ` the section is `secHom`, with underlying map `v ↦ (ψ v, v)`.
* (G6) `pcomp c i = c ∘ i := (r ↦ cF r ∘ i, r ↦ cE r ∘ i)` and
  `qcomp j c = j ∘ c := (r ↦ j ∘ cF r, r ↦ j ∘ cE r)`.
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

variable {M N M' N' M'' : DPLattice A}

/-! ### (G5) Splitting -/

/-- (G5) the linear map `v ↦ (ψ v, v)`. -/
def secL (ψ : Lin M N) : (M.ι → A) →ₗ[A] (N.ι ⊕ M.ι → A) where
  toFun v := Sum.elim (ψ v) v
  map_add' v v' := by simp
  map_smul' t v := by simp

/-- (G5), (i) ⇒ (ii): for a weight-preserving `ψ`, the section `v ↦ (ψ v, v)` of `proj` for the
glued lattice of `dψ`. -/
def secHom {ψ : Lin M N} (hψ : IsWtPres ψ) (hc : IsCocycle (d ψ)) :
    Hom M (glue M N (d ψ) hc) where
  toLin := secL ψ
  comm_F r := LinearMap.ext fun v => by
    change Sum.elim (ψ (M.Fd r v)) (M.Fd r v) = gF (d ψ) r (Sum.elim (ψ v) v)
    rw [gF_elim, d_fst, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      add_sub_cancel]
  comm_E r := LinearMap.ext fun v => by
    change Sum.elim (ψ (M.Ed r v)) (M.Ed r v) = gE (d ψ) r (Sum.elim (ψ v) v)
    rw [gE_elim, d_snd, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      add_sub_cancel]
  comm_H := LinearMap.ext fun v => by
    change Sum.elim (ψ (Hop M.wt v)) (Hop M.wt v) = Hop (gwt M N) (Sum.elim (ψ v) v)
    rw [hop_elim]
    congr 1
    exact LinearMap.congr_fun (comm_H_of_isWtPres hψ) v

@[simp] lemma secHom_toLin {ψ : Lin M N} (hψ : IsWtPres ψ) (hc : IsCocycle (d ψ))
    (v : M.ι → A) : (secHom hψ hc).toLin v = Sum.elim (ψ v) v := rfl

/-- (G5, auxiliary) comparison of weight components: if `T`, `T'` shift weights by `δ` and so
does `ψ' ∘ T − T' ∘ ψ'`, then the weight-diagonal part `wd ψ'` satisfies
`wd ψ' ∘ T − T' ∘ wd ψ' = ψ' ∘ T − T' ∘ ψ'`. -/
lemma wd_shift (ψ' : Lin M N) (T : Module.End A (M.ι → A)) (T' : Module.End A (N.ι → A))
    (δ : ℤ) (hT : ∀ w, T ∘ₗ pr M w = pr M (w + δ) ∘ₗ T)
    (hT' : ∀ w, T' ∘ₗ pr N w = pr N (w + δ) ∘ₗ T')
    (hc : ∀ w, (ψ' ∘ₗ T - T' ∘ₗ ψ') ∘ₗ pr M w = pr N (w + δ) ∘ₗ (ψ' ∘ₗ T - T' ∘ₗ ψ')) :
    wd ψ' ∘ₗ T - T' ∘ₗ wd ψ' = ψ' ∘ₗ T - T' ∘ₗ ψ' := by
  refine LinearMap.ext fun z => funext fun j => ?_
  have hu : N.wt j - δ + δ = N.wt j := by ring
  have e1 := LinearMap.congr_fun (hT (N.wt j - δ)) z
  have e2 := LinearMap.congr_fun (hT' (N.wt j - δ)) (wd ψ' z)
  have e3 := LinearMap.congr_fun (pr_wd ψ' (N.wt j - δ)) z
  have e4 := LinearMap.congr_fun (hT' (N.wt j - δ)) (ψ' (pr M (N.wt j - δ) z))
  have e5 := LinearMap.congr_fun (hc (N.wt j - δ)) z
  rw [hu] at e1 e2 e4 e5
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at e1 e2 e3 e4 e5 ⊢
  have g1 : wd ψ' (T z) j = ψ' (T (pr M (N.wt j - δ) z)) j := by rw [wd_apply, ← e1]
  have g2 : T' (wd ψ' z) j = T' (ψ' (pr M (N.wt j - δ) z)) j := by
    rw [apply_eq_pr N (T' (wd ψ' z)) j, ← e2, e3, e4, pr_apply, if_pos rfl]
  have g3 := congrFun e5 j
  simp only [Pi.sub_apply, pr_apply, ↓reduceIte] at g3
  rw [Pi.sub_apply, Pi.sub_apply, g1, g2, g3]

/-- (G5) For a cocycle `c`, the following are equivalent: (i) `c` is a coboundary; (ii) `proj`
has a section in `Hom`; (iii) `incl` has a retraction in `Hom`. Stated as (i) ⇔ (ii) and
(ii) ⇔ (iii). -/
theorem G5 (c : Pair M N) (hc : IsCocycle c) :
    (IsCoboundary c ↔ ∃ s : Hom M (glue M N c hc), Hom.comp (proj M N c hc) s = Hom.id M) ∧
    ((∃ s : Hom M (glue M N c hc), Hom.comp (proj M N c hc) s = Hom.id M) ↔
      ∃ r : Hom (glue M N c hc) N, Hom.comp r (incl M N c hc) = Hom.id N) := by
  refine ⟨⟨?_, ?_⟩, E1 (G3 c hc).2.2⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨secHom hψ hc, Hom.ext' (LinearMap.ext fun v => rfl)⟩
  · rintro ⟨s, hs⟩
    have hcE := (G2 c).mp hc
    let ψ' : Lin M N := LinearMap.funLeft A A Sum.inl ∘ₗ s.toLin
    have hs' : ∀ v, s.toLin v = Sum.elim (ψ' v) v := fun v => by
      have h1 : s.toLin v ∘ Sum.inr = v := LinearMap.congr_fun (congrArg Hom.toLin hs) v
      rw [← elim_comp (s.toLin v), h1]; rfl
    have hcF : ∀ r, c.1 r = ψ' ∘ₗ M.Fd r - N.Fd r ∘ₗ ψ' := fun r => LinearMap.ext fun v => by
      have h1 := LinearMap.congr_fun (s.comm_F r) v
      simp only [LinearMap.comp_apply] at h1
      change s.toLin (M.Fd r v) = gF c r (s.toLin v) at h1
      rw [hs', hs', gF_elim, elim_eq_iff] at h1
      show _ = ψ' (M.Fd r v) - N.Fd r (ψ' v)
      rw [h1.1]
      abel
    have hcE' : ∀ r, c.2 r = ψ' ∘ₗ M.Ed r - N.Ed r ∘ₗ ψ' := fun r => LinearMap.ext fun v => by
      have h1 := LinearMap.congr_fun (s.comm_E r) v
      simp only [LinearMap.comp_apply] at h1
      change s.toLin (M.Ed r v) = gE c r (s.toLin v) at h1
      rw [hs', hs', gE_elim, elim_eq_iff] at h1
      show _ = ψ' (M.Ed r v) - N.Ed r (ψ' v)
      rw [h1.1]
      abel
    refine ⟨wd ψ', wd_isWtPres ψ', Prod.ext (funext fun r => ?_) (funext fun r => ?_)⟩
    · rw [d_fst, wd_shift ψ' (M.Fd r) (N.Fd r) (-(2 * r)), hcF]
      · intro w; rw [P2_F, sub_eq_add_neg]
      · intro w; rw [P2_F, sub_eq_add_neg]
      · intro w
        rw [← hcF]
        exact comm_prW_of_shift M.wt N.wt (-(2 * r)) (c.1 r)
          (fun i j hj => hcE.W_F i r j (by omega)) w
    · rw [d_snd, wd_shift ψ' (M.Ed r) (N.Ed r) (2 * r), hcE']
      · intro w; rw [P2_E]
      · intro w; rw [P2_E]
      · intro w
        rw [← hcE']
        exact comm_prW_of_shift M.wt N.wt (2 * r) (c.2 r)
          (fun i j hj => hcE.W_E i r j hj) w

/-! ### (G6) Change of the ends -/

/-- (G6) `c ∘ i := (r ↦ cF r ∘ i, r ↦ cE r ∘ i)`. -/
def pcomp (c : Pair M N) (i : Lin M' M) : Pair M' N :=
  (fun r => c.1 r ∘ₗ i, fun r => c.2 r ∘ₗ i)

/-- (G6) `j ∘ c := (r ↦ j ∘ cF r, r ↦ j ∘ cE r)`. -/
def qcomp (j : Lin N N') (c : Pair M N) : Pair M N' :=
  (fun r => j ∘ₗ c.1 r, fun r => j ∘ₗ c.2 r)

@[simp] lemma pcomp_fst (c : Pair M N) (i : Lin M' M) (r : ℕ) :
    (pcomp c i).1 r = c.1 r ∘ₗ i := rfl
@[simp] lemma pcomp_snd (c : Pair M N) (i : Lin M' M) (r : ℕ) :
    (pcomp c i).2 r = c.2 r ∘ₗ i := rfl
@[simp] lemma qcomp_fst (j : Lin N N') (c : Pair M N) (r : ℕ) :
    (qcomp j c).1 r = j ∘ₗ c.1 r := rfl
@[simp] lemma qcomp_snd (j : Lin N N') (c : Pair M N) (r : ℕ) :
    (qcomp j c).2 r = j ∘ₗ c.2 r := rfl

lemma pcomp_sub (c c' : Pair M N) (i : Lin M' M) :
    pcomp (c - c') i = pcomp c i - pcomp c' i := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;> simp [LinearMap.sub_comp]

lemma qcomp_sub (j : Lin N N') (c c' : Pair M N) :
    qcomp j (c - c') = qcomp j c - qcomp j c' := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;> simp [LinearMap.comp_sub]

lemma pcomp_pcomp (c : Pair M N) (i : Lin M' M) (i' : Lin M'' M') :
    pcomp (pcomp c i) i' = pcomp c (i ∘ₗ i') := rfl

lemma qcomp_qcomp {N'' : DPLattice A} (j : Lin N N') (j' : Lin N' N'') (c : Pair M N) :
    qcomp j' (qcomp j c) = qcomp (j' ∘ₗ j) c := rfl

/-- (G6)(a), first half: `c ∘ i` is a cocycle from `M'` to `N`. -/
theorem G6a_pcomp {c : Pair M N} (hc : IsCocycle c) (i : Hom M' M) (hi : IsWtPres i.toLin) :
    IsCocycle (pcomp c i.toLin) := by
  have hcE := (G2 c).mp hc
  have hiF : ∀ r v, i.toLin (M'.Fd r v) = M.Fd r (i.toLin v) := fun r v =>
    LinearMap.congr_fun (i.comm_F r) v
  have hiE : ∀ r v, i.toLin (M'.Ed r v) = M.Ed r (i.toLin v) := fun r v =>
    LinearMap.congr_fun (i.comm_E r) v
  refine (G2 _).mpr ⟨fun k r j hj => ?_, fun k r j hj => ?_, ?_, ?_, fun a b => ?_,
    fun a b => ?_, fun k r s => ?_⟩
  · exact cF_inWt hc r (inWt_map hi (inWt_single M'.wt k)) j hj
  · exact cE_inWt hc r (inWt_map hi (inWt_single M'.wt k)) j hj
  · simp [hcE.P0_F]
  · simp [hcE.P0_E]
  · simp only [pcomp_fst]
    rw [LinearMap.comp_assoc, i.comm_F, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      ← LinearMap.add_comp, hcE.P1_F, LinearMap.smul_comp]
  · simp only [pcomp_snd]
    rw [LinearMap.comp_assoc, i.comm_E, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      ← LinearMap.add_comp, hcE.P1_E, LinearMap.smul_comp]
  · simp only [pcomp_fst, pcomp_snd, LinearMap.comp_apply, hiF, hiE]
    exact K_cocycle_vec hc (inWt_map hi (inWt_single M'.wt k)) r s

/-- (G6)(a), second half: `j ∘ c` is a cocycle from `M` to `N'`. -/
theorem G6a_qcomp {c : Pair M N} (hc : IsCocycle c) (j : Hom N N') (hj : IsWtPres j.toLin) :
    IsCocycle (qcomp j.toLin c) := by
  have hcE := (G2 c).mp hc
  have hjF : ∀ r v, j.toLin (N.Fd r v) = N'.Fd r (j.toLin v) := fun r v =>
    LinearMap.congr_fun (j.comm_F r) v
  have hjE : ∀ r v, j.toLin (N.Ed r v) = N'.Ed r (j.toLin v) := fun r v =>
    LinearMap.congr_fun (j.comm_E r) v
  refine (G2 _).mpr ⟨fun k r l hl => ?_, fun k r l hl => ?_, ?_, ?_, fun a b => ?_,
    fun a b => ?_, fun k r s => ?_⟩
  · exact inWt_map hj (cF_inWt hc r (inWt_single M.wt k)) l hl
  · exact inWt_map hj (cE_inWt hc r (inWt_single M.wt k)) l hl
  · simp [hcE.P0_F]
  · simp [hcE.P0_E]
  · simp only [qcomp_fst]
    rw [← LinearMap.comp_assoc, ← j.comm_F, LinearMap.comp_assoc, LinearMap.comp_assoc,
      ← LinearMap.comp_add, hcE.P1_F, LinearMap.comp_smul]
  · simp only [qcomp_snd]
    rw [← LinearMap.comp_assoc, ← j.comm_E, LinearMap.comp_assoc, LinearMap.comp_assoc,
      ← LinearMap.comp_add, hcE.P1_E, LinearMap.comp_smul]
  · simp only [qcomp_fst, qcomp_snd, LinearMap.comp_apply, ← hjF, ← hjE, ← map_add,
      hcE.K k r s, map_sum, map_smul]

/-- (G6)(a), identity: `d(ψ ∘ i) = (dψ) ∘ i` (for any linear `ψ`; weight preservation is not
needed). -/
theorem G6a_d_pcomp (ψ : Lin M N) (i : Hom M' M) : d (ψ ∘ₗ i.toLin) = pcomp (d ψ) i.toLin := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_)
  · simp only [d_fst, pcomp_fst, LinearMap.sub_comp, LinearMap.comp_assoc, i.comm_F]
  · simp only [d_snd, pcomp_snd, LinearMap.sub_comp, LinearMap.comp_assoc, i.comm_E]

/-- (G6)(a), identity: `d(j ∘ ψ) = j ∘ dψ` (for any linear `ψ`; weight preservation is not
needed). -/
theorem G6a_d_qcomp (ψ : Lin M N) (j : Hom N N') : d (j.toLin ∘ₗ ψ) = qcomp j.toLin (d ψ) := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_)
  · simp only [d_fst, qcomp_fst, LinearMap.comp_sub, ← LinearMap.comp_assoc, j.comm_F]
  · simp only [d_snd, qcomp_snd, LinearMap.comp_sub, ← LinearMap.comp_assoc, j.comm_E]

/-- (G6)(a): if `c` is a cocycle from `M` to `N` and `i : Hom M' M`, `j : Hom N N'` have
weight-preserving underlying maps, then `c ∘ i` and `j ∘ c` are cocycles, and
`d(ψ ∘ i) = (dψ) ∘ i`, `d(j ∘ ψ) = j ∘ dψ` for weight-preserving `ψ` (the identities hold for
every linear `ψ`). -/
theorem G6a {c : Pair M N} (hc : IsCocycle c) (i : Hom M' M) (hi : IsWtPres i.toLin)
    (j : Hom N N') (hj : IsWtPres j.toLin) :
    IsCocycle (pcomp c i.toLin) ∧ IsCocycle (qcomp j.toLin c) ∧
    (∀ ψ : Lin M N, IsWtPres ψ → d (ψ ∘ₗ i.toLin) = pcomp (d ψ) i.toLin ∧
      d (j.toLin ∘ₗ ψ) = qcomp j.toLin (d ψ)) :=
  ⟨G6a_pcomp hc i hi, G6a_qcomp hc j hj, fun ψ _ => ⟨G6a_d_pcomp ψ i, G6a_d_qcomp ψ j⟩⟩

/-- (G6)(b): if `p : Hom M M''` is surjective with `p.toLin` weight-preserving and `c'' ∘ p` is
a cocycle from `M` to `N`, then `c''` is a cocycle from `M''` to `N`. -/
theorem G6b (p : Hom M M'') (hp : Function.Surjective p.toLin) (hpw : IsWtPres p.toLin)
    {c'' : Pair M'' N} (h : IsCocycle (pcomp c'' p.toLin)) : IsCocycle c'' := by
  refine isDP_transport (glue M N (pcomp c'' p.toLin) h)
    (blk (LinearMap.id : Module.End A (N.ι → A)) 0 p.toLin) ?_ ?_ ?_ ?_
  · intro i k hik
    change gwt M N i ≠ gwt M'' N k at hik
    change blk LinearMap.id 0 p.toLin (Pi.single i (1 : A) : N.ι ⊕ M.ι → A) k = 0
    cases i with
    | inl i =>
      rw [single_inl, blk_elim]
      cases k with
      | inl k =>
        have : k ≠ i := fun h => hik (h ▸ rfl)
        simp [this]
      | inr k => simp
    | inr i =>
      rw [single_inr, blk_elim]
      cases k with
      | inl k => simp
      | inr k => simpa using hpw i k hik
  · intro r
    change blk LinearMap.id 0 p.toLin ∘ₗ blk (N.Fd r) (c''.1 r ∘ₗ p.toLin) (M.Fd r) =
      blk (N.Fd r) (c''.1 r) (M''.Fd r) ∘ₗ blk LinearMap.id 0 p.toLin
    rw [blk_comp, blk_comp, blk_eq_iff]
    refine ⟨rfl, ?_, p.comm_F r⟩
    simp
  · intro r
    change blk LinearMap.id 0 p.toLin ∘ₗ blk (N.Ed r) (c''.2 r ∘ₗ p.toLin) (M.Ed r) =
      blk (N.Ed r) (c''.2 r) (M''.Ed r) ∘ₗ blk LinearMap.id 0 p.toLin
    rw [blk_comp, blk_comp, blk_eq_iff]
    refine ⟨rfl, ?_, p.comm_E r⟩
    simp
  · intro k
    cases k with
    | inl k =>
      refine ⟨Sum.elim (Pi.single k 1) 0, elim_inWt (inWt_single N.wt k) inWt_zero, ?_⟩
      show blk LinearMap.id 0 p.toLin (Sum.elim (Pi.single k 1) (0 : M.ι → A)) = _
      rw [single_inl, blk_elim]
      simp
    | inr k =>
      obtain ⟨y, hy⟩ := hp (Pi.single k 1)
      have hpy : p.toLin (pr M (M''.wt k) y) = Pi.single k 1 := by
        rw [← LinearMap.comp_apply, P2_wtPres hpw, LinearMap.comp_apply, hy]
        exact (hasWt_iff_inWt M'' _ _).mpr (inWt_single M''.wt k)
      refine ⟨Sum.elim 0 (pr M (M''.wt k) y), elim_inWt inWt_zero
        ((hasWt_iff_inWt M _ _).mp (hasWt_pr M _ y)), ?_⟩
      show blk LinearMap.id 0 p.toLin (Sum.elim (0 : N.ι → A) (pr M (M''.wt k) y)) = _
      rw [single_inr, blk_elim, hpy]
      simp

/-- (G6, auxiliary) an injective weight-preserving map reflects weights of vectors. -/
lemma inWt_of_inj {a : Lin N' N} (ha : Function.Injective a) (haw : IsWtPres a) {w : ℤ}
    {x : N'.ι → A} (hx : InWt N.wt w (a x)) : InWt N'.wt w x := by
  rw [← hasWt_iff_inWt] at hx ⊢
  unfold HasWt at hx ⊢
  apply ha
  rw [← LinearMap.comp_apply, P2_wtPres haw, LinearMap.comp_apply, hx]

lemma comp_cancel_left {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] {a : Y →ₗ[A] Z} (ha : Function.Injective a)
    {f g : X →ₗ[A] Y} (h : a ∘ₗ f = a ∘ₗ g) : f = g :=
  LinearMap.ext fun v => ha (LinearMap.congr_fun h v)

/-- (G6)(c): if `a : Hom N' N` is injective with `a.toLin` weight-preserving and `a ∘ c'` is a
cocycle from `M` to `N`, then `c'` is a cocycle from `M` to `N'`. -/
theorem G6c (a : Hom N' N) (ha : Function.Injective a.toLin) (haw : IsWtPres a.toLin)
    {c' : Pair M N'} (h : IsCocycle (qcomp a.toLin c')) : IsCocycle c' := by
  have hq := (G2 _).mp h
  have haF : ∀ r v, a.toLin (N'.Fd r v) = N.Fd r (a.toLin v) := fun r v =>
    LinearMap.congr_fun (a.comm_F r) v
  have haE : ∀ r v, a.toLin (N'.Ed r v) = N.Ed r (a.toLin v) := fun r v =>
    LinearMap.congr_fun (a.comm_E r) v
  refine (G2 _).mpr ⟨fun i r j hj => ?_, fun i r j hj => ?_, ?_, ?_, fun x y => ?_,
    fun x y => ?_, fun i r s => ?_⟩
  · exact inWt_of_inj ha haw (cF_inWt h r (inWt_single M.wt i)) j hj
  · exact inWt_of_inj ha haw (cE_inWt h r (inWt_single M.wt i)) j hj
  · apply comp_cancel_left ha
    rw [← qcomp_fst, hq.P0_F, LinearMap.comp_zero]
  · apply comp_cancel_left ha
    rw [← qcomp_snd, hq.P0_E, LinearMap.comp_zero]
  · apply comp_cancel_left ha
    have := hq.P1_F x y
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun this v
    simp only [qcomp_fst, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
      at h1 ⊢
    rw [map_add, map_smul, haF, h1]
  · apply comp_cancel_left ha
    have := hq.P1_E x y
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun this v
    simp only [qcomp_snd, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
      at h1 ⊢
    rw [map_add, map_smul, haE, h1]
  · apply ha
    have := hq.K i r s
    simp only [qcomp_fst, qcomp_snd, LinearMap.comp_apply] at this
    simp only [map_add, map_sum, map_smul, haF, haE]
    exact this

end Cocycle
