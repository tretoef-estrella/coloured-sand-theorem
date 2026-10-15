module

public import RequestProject.OddDance.Lattice
public import RequestProject.TiltP.All
public import RequestProject.TiltRules.PartS
public import RequestProject.FamDec.All
public import RequestProject.TiltDec.All

/-!
# `CSI6_the_dance_lattices.md`, Part R — the tensor rule `V ⊗ L(λ)` (R2) and every tensor
power (R3)

Namespace `ColouredSand.OddTwist`. Reuses C18 `delta`, `one`, `tensorV`, `T5_delta_zero`;
C20 `Doubling.Iso` (`trans`, `symm`, `ofDataEquiv`); C22 `dsum`; C23 `Tensor2.tensor`,
`tensorIso`, `dsumIso`, `tensorVIsoTensor`; C24 `Iso.refl`, `dsumComm`; C29 `Filt.tpow`;
C30 `Step36.dsumList`, `dsumListAppendIso`, `tensorVDsumListIso`; CSG3 (G3) `TiltP.G3`;
CSG4 (S0) `TiltRules.S0`; CSG5 `isoSingle`, `isoPair`, `isoTriple`; CSI1 `twist`, `Iso.twist`,
`D3`; CSI3 `psi`; CSI5 `tensor_T0`, `tensor_T1`, `tensor_T2`, `tensor_T3`, `psi_congr`; and
Part A (`twistDsumListIso`) and Part L (`danceL`).

Encodings: «`X ≅ Y`» is `Nonempty (Doubling.Iso X Y)`; `V` is `V ℤ_[p]` and `V ⊗ X` is
`Tensor2.tensor (V ℤ_[p]) X` (C29's `Filt.tpow` is built with C18's `tensorV`, which is
isomorphic to it by `tensorVIsoTensor`); a direct sum of a list of lattices is `dsumList`.
"`p` an odd prime" is `[Fact p.Prime]` with `p ≠ 2`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Lemma35 Step36

variable (p : ℕ) [Fact p.Prime]

local notation "Vp" => DPLattice.V ℤ_[p]

/-! ### Small isomorphisms -/

/-- (R2), auxiliary: pointwise isomorphic families have isomorphic direct sums. -/
lemma dsumList_map_iso {α : Type*} (L : List α) (f g : α → DPLattice ℤ_[p])
    (h : ∀ a ∈ L, Nonempty (Doubling.Iso (f a) (g a))) :
    Nonempty (Doubling.Iso (dsumList (L.map f)) (dsumList (L.map g))) := by
  induction L with
  | nil => exact ⟨Lemma35b.Iso.refl _⟩
  | cons a L ih =>
    obtain ⟨u⟩ := h a (List.mem_cons_self ..)
    obtain ⟨v⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨Tensor2.dsumIso u v⟩

/-- (R3), auxiliary: `⊕_i ⊕ Ls_i ≅ ⊕ (concatenation of the Ls_i)`. -/
def dsumListFlattenIso : (Ls : List (List (DPLattice ℤ_[p]))) →
    Doubling.Iso (dsumList (Ls.map dsumList)) (dsumList Ls.flatten)
  | [] => Lemma35b.Iso.refl _
  | X :: Ls => (Tensor2.dsumIso (Lemma35b.Iso.refl _) (dsumListFlattenIso Ls)).trans
      (dsumListAppendIso X Ls.flatten).symm

/-- `Δ(0) ≅ 𝟙` (C18 (T5)). -/
def deltaZeroIso : Doubling.Iso (delta ℤ_[p] 0) (one ℤ_[p]) :=
  Doubling.Iso.ofDataEquiv finOneEquivUnit T5_delta_zero

/-- (R2), auxiliary: for `λ ≤ p − 1`, `L(λ) ≅ Δ(λ)` (for `λ = p − 1` this is
`Φ_p(Δ(0)) ≅ Φ_p(𝟙) ≅ Δ(p − 1)`, CSI1 (D3)). -/
lemma danceL_iso_delta {l : ℕ} (hl : l ≤ p - 1) :
    Nonempty (Doubling.Iso (danceL p l) (delta ℤ_[p] l)) := by
  have hp := two_le_prime p
  by_cases h : l + 1 < p
  · rw [danceL_lt p h]; exact ⟨Lemma35b.Iso.refl _⟩
  · have hl' : l = p * 0 + p - 1 := by omega
    rw [hl', danceL_twist_eq, danceL_lt p (by omega), ← hl']
    obtain ⟨u⟩ := D3 p
    rw [show l = p - 1 by omega]
    exact ⟨(Iso.twist p (deltaZeroIso p)).trans u⟩

/-! ### (R2) -/

/-- **(R2)** (Part R of `CSI6_the_dance_lattices.md`) **the tensor rule**: for an odd prime `p`
and every `λ`, `V ⊗ L(λ) ≅ ⊕_{μ ∈ VdotL p λ} L(μ)`. Strong induction on `λ`: `λ = 0` is CSG4
(S0); `1 ≤ λ ≤ p − 2` is CSG3 (G3) (with CSI1 (D3) at `λ = p − 2`); for `λ ≥ p − 1`, the cases
`d₀ = 0`, `d₀ = 1`, `2 ≤ d₀ ≤ p − 2`, `d₀ = p − 1` are CSI5 (T0), (T2), (T1), (T3), the last one
with the induction hypothesis at `b < λ` and Part A. -/
theorem tensor_danceL (hp2 : p ≠ 2) (l : ℕ) :
    Nonempty (Doubling.Iso (Tensor2.tensor Vp (danceL p l))
      (dsumList ((VdotL p l).map (danceL p)))) := by
  have hp := two_le_prime p
  have hp3 : 3 ≤ p := by omega
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  by_cases h0 : l = 0
  · -- `λ = 0`: `V ⊗ Δ(0) ≅ Δ(1)`
    subst h0
    rw [VdotL_zero, danceL_lt p (by omega)]
    simp only [List.map_cons, List.map_nil]
    obtain ⟨u⟩ := ColouredSand.TiltRules.S0 (p := p)
    obtain ⟨v⟩ := danceL_iso_delta p (l := 1) (by omega)
    exact ⟨((Tensor2.tensorVIsoTensor _).symm.trans u).trans
      ((ColouredSand.TiltDec.isoSingle (p := p) _).trans (Tensor2.dsumIso v.symm (Lemma35b.Iso.refl _)))⟩
  by_cases h1 : l + 1 < p
  · -- `1 ≤ λ ≤ p − 2`: CSG3 (G3)
    rw [VdotL_small (by omega) (by omega), danceL_lt p h1]
    simp only [List.map_cons, List.map_nil]
    obtain ⟨u⟩ := ColouredSand.TiltP.G3 (p := p) (l := l) (by omega)
      (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)
    obtain ⟨v⟩ := danceL_iso_delta p (l := l + 1) (by omega)
    obtain ⟨w⟩ := danceL_iso_delta p (l := l - 1) (by omega)
    exact ⟨((Tensor2.tensorVIsoTensor _).symm.trans u).trans
      ((Tensor2.dsumIso v.symm w.symm).trans (ColouredSand.TiltDec.isoPair (p := p) _ _))⟩
  -- `λ ≥ p − 1`
  have hl' : p - 1 ≤ l := by omega
  have hk := succ_eq_d0_b (by omega : 1 ≤ p) hl'
  have hblt := b_lt hp (show 1 ≤ l by omega)
  have hdp : (l + 1) % p < p := Nat.mod_lt _ (by omega)
  have IH := ih _ hblt
  generalize hd : (l + 1) % p = d at *
  generalize hb : (l + 1) / p - 1 = b at *
  have hpb : p * (b + 1) = p * b + p := Nat.mul_succ p b
  by_cases hd0 : d = 0
  · -- `d₀ = 0`: CSI5 (T0)
    subst hd0
    rw [VdotL_d0_zero hp hl' hd]
    have e1 : danceL p l = twist p (danceL p b) := by
      rw [show l = p * b + p - 1 by omega, danceL_twist_eq]
    have e2 : danceL p (l + 1) = psi p (danceL p b) 1 le_rfl (by omega) := by
      rw [← danceL_psi_eq p b 1 le_rfl (by omega)]; congr 1; omega
    simp only [List.map_cons, List.map_nil]
    rw [e1, e2]
    obtain ⟨u⟩ := tensor_T0 (N := danceL p b) (p := p) le_rfl (by omega)
    exact ⟨u.trans (ColouredSand.TiltDec.isoSingle (p := p) _)⟩
  have hd1 : 1 ≤ d := by omega
  have e0 : danceL p l = psi p (danceL p b) d hd1 (by omega) := by
    rw [← danceL_psi_eq p b d hd1 (by omega)]; congr 1; omega
  rw [e0]
  by_cases hdo : d = 1
  · -- `d₀ = 1`: CSI5 (T2)
    subst hdo
    rw [VdotL_d0_one hp hl' hd]
    have e1 : danceL p (l + 1) = psi p (danceL p b) 2 (by omega) (by omega) := by
      rw [← danceL_psi_eq p b 2 (by omega) (by omega)]; congr 1; omega
    have e2 : danceL p (l - 1) = twist p (danceL p b) := by
      rw [show l - 1 = p * b + p - 1 by omega, danceL_twist_eq]
    simp only [List.map_cons, List.map_nil]
    rw [e1, e2]
    obtain ⟨u⟩ := tensor_T2 (N := danceL p b) hp3 le_rfl (by omega)
    exact ⟨u.trans (ColouredSand.TiltDec.isoTriple (p := p) _ _ _)⟩
  by_cases hdm : d ≤ p - 2
  · -- `2 ≤ d₀ ≤ p − 2`: CSI5 (T1)
    rw [VdotL_d0_mid hl' (by omega) (by omega)]
    have e1 : danceL p (l + 1) = psi p (danceL p b) (d + 1) (by omega) (by omega) := by
      rw [← danceL_psi_eq p b (d + 1) (by omega) (by omega)]; congr 1; omega
    have e2 : danceL p (l - 1) = psi p (danceL p b) (d - 1) (by omega) (by omega) := by
      rw [← danceL_psi_eq p b (d - 1) (by omega) (by omega)]; congr 1; omega
    simp only [List.map_cons, List.map_nil]
    rw [e1, e2]
    obtain ⟨u⟩ := tensor_T1 (N := danceL p b) d (by omega) hdm
    exact ⟨u.trans (ColouredSand.TiltDec.isoPair (p := p) _ _)⟩
  -- `d₀ = p − 1`: CSI5 (T3), the induction hypothesis at `b`, and Part A
  have hdt : d = p - 1 := by omega
  subst hdt
  rw [VdotL_d0_top hp3 hl' hd, hb]
  have e1 : danceL p (l - 1) = psi p (danceL p b) (p - 2) (by omega) (by omega) := by
    rw [← danceL_psi_eq p b (p - 2) (by omega) (by omega)]; congr 1; omega
  have e2 : ((VdotL p b).map (fun b' => p * b' + p - 1)).map (danceL p) =
      ((VdotL p b).map (danceL p)).map (twist p) := by
    simp only [List.map_map]
    exact List.map_congr_left fun b' _ => danceL_twist_eq p b'
  simp only [List.map_cons]
  rw [e1, e2]
  obtain ⟨u⟩ := tensor_T3 (N := danceL p b) hp3
  obtain ⟨v⟩ := IH
  exact ⟨u.trans ((Lemma35b.dsumComm _ _).trans
    (Tensor2.dsumIso (Lemma35b.Iso.refl _) ((Iso.twist p v).trans (twistDsumListIso p _))))⟩

/-! ### (R3) -/

/-- **(R3)** (Part R of `CSI6_the_dance_lattices.md`) **every tensor power** (Theorem 1.6 (iii)
of «the odd dance», without Donkin and without a Lift lemma): for an odd prime `p` and every
`m`, `V^{⊗m} ⊗ ℤ_p = Filt.tpow ℤ_[p] m ≅ ⊕_{λ ∈ LL p m} L(λ)`, i.e.
`≅ ⊕_λ L(λ)^{n_λ(m)}` with `n_λ(m) = (LL p m).count λ` (`nL`). -/
theorem tpow_danceL (hp2 : p ≠ 2) (m : ℕ) :
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m) (dsumList ((LL p m).map (danceL p)))) := by
  have hp := two_le_prime p
  induction m with
  | zero =>
    rw [LL_zero]
    simp only [List.map_cons, List.map_nil]
    rw [danceL_lt p (by omega)]
    exact ⟨(deltaZeroIso p).symm.trans (ColouredSand.TiltDec.isoSingle (p := p) _)⟩
  | succ m ih =>
    obtain ⟨u⟩ := ih
    -- `V ⊗ V^{⊗m} ≅ V ⊗ ⊕ L(λ) ≅ ⊕ (V ⊗ L(λ))`
    have s1 : Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] (m + 1))
        (dsumList (((LL p m).map (danceL p)).map tensorV))) :=
      ⟨(((Tensor2.tensorVIsoTensor _).trans (Tensor2.tensorIso (Lemma35b.Iso.refl _) u)).trans
        (Tensor2.tensorVIsoTensor _).symm).trans (tensorVDsumListIso _)⟩
    -- `⊕ (V ⊗ L(λ)) ≅ ⊕_λ ⊕_{μ ∈ VdotL λ} L(μ)` by (R2)
    have s2 : Nonempty (Doubling.Iso (dsumList (((LL p m).map (danceL p)).map tensorV))
        (dsumList ((LL p m).map (fun l => dsumList ((VdotL p l).map (danceL p)))))) := by
      rw [List.map_map]
      refine dsumList_map_iso p _ _ _ fun l _ => ?_
      obtain ⟨v⟩ := tensor_danceL p hp2 l
      exact ⟨(Tensor2.tensorVIsoTensor _).trans v⟩
    -- flatten
    have s3 : Nonempty (Doubling.Iso
        (dsumList ((LL p m).map (fun l => dsumList ((VdotL p l).map (danceL p)))))
        (dsumList ((LL p (m + 1)).map (danceL p)))) := by
      have := dsumListFlattenIso p ((LL p m).map (fun l => (VdotL p l).map (danceL p)))
      rw [List.map_map] at this
      rw [LL_succ, List.map_flatMap, List.flatMap_def]
      exact ⟨this⟩
    obtain ⟨a⟩ := s1
    obtain ⟨b⟩ := s2
    obtain ⟨c⟩ := s3
    exact ⟨(a.trans b).trans c⟩

/-- **(R3)**, multiplicity form: `V^{⊗m} ⊗ ℤ_p ≅ ⊕_λ L(λ)^{n_λ(m)}`, where the right side is
the direct sum over `λ ≤ m` of `n_λ(m) = (LL p m).count λ` copies of `L(λ)` (every weight in
`LL p m` is `≤ m`). -/
theorem tpow_danceL_mult (hp2 : p ≠ 2) (m : ℕ) :
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m)
      (dsumList (((List.range (m + 1)).flatMap fun l =>
        List.replicate (nL p l m) l).map (danceL p)))) := by
  obtain ⟨u⟩ := tpow_danceL p hp2 m
  have hperm := FamDec.perm_flatMap_replicate (LL p m) (m + 1)
    (fun x hx => Nat.lt_succ_of_le (le_of_mem_LL (two_le_prime p) m x hx))
  obtain ⟨v⟩ := FamDec.P1 (hperm.map (danceL p))
  exact ⟨u.trans v⟩

end ColouredSand.OddTwist
