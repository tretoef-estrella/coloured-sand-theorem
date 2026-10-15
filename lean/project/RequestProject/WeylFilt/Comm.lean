module

public import RequestProject.WeylFilt.Coord

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: Part M, commutation relations (auxiliary)

The coordinate maps of "The four maps" commute with `F^{(t)}`, `E^{(s)}` and `H`; the proofs are
the Pascal-type identities of the file's proof sketch, checked coordinatewise.
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

lemma sub_succ_add_one' {n t : ℕ} (h : t + 1 ≤ n) : n - (t + 1) + 1 = n - t := by omega

lemma add_one_sub' {m n : ℕ} (h : n ≤ m) : m + 1 - n = m - n + 1 := by omega

lemma add_one_sub_self' (j t : ℕ) : j + t + 1 - t = j + 1 := by omega

lemma succ_add_comm' (n s : ℕ) : n + 1 + s = n + s + 1 := by omega

/-- (auxiliary) unfolding of all coordinates. -/
macro "wf_simp" : tactic => `(tactic| (
  simp only [LinearMap.comp_apply, slice0_tensorFd, slice1_tensorFd, slice0_tensorEd,
    slice1_tensorEd, ext0_slice0_fDelta, ext0_slice1_fDelta, ext0_gDelta, ext0_slice0_fNabla,
    ext0_slice1_fNabla, ext0_gNabla, ext0_deltaF, ext0_deltaE, ext0_nablaF, ext0_nablaE, ext0_H,
    ext0_slice0_H, ext0_slice1_H, pred_zero, pred_succ, LinearMap.zero_apply, ext0_add, ext0_sub,
    ext0_neg, ext0_zero, add_zero, Nat.add_sub_cancel]))

/-- (auxiliary) closing tactic for the coordinate identities of Part M. -/
macro "wf_close" : tactic => `(tactic| (
  split_ifs <;>
  first
    | rfl
    | (exfalso; omega)
    | ((try simp (disch := omega) only [Nat.add_sub_add_right, Nat.sub_zero, Nat.choose_zero_right,
        Nat.choose_succ_succ', Nat.cast_add, Nat.cast_one, sub_succ_add_one', add_one_sub',
        Nat.add_sub_cancel, add_one_sub_self', succ_add_comm', Nat.sub_sub, Nat.choose_eq_zero_of_lt, ext0_of_ge, Nat.choose_self, Nat.cast_zero,
        zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, ← add_assoc]) <;>
       ring_nf)))

lemma fDelta_F (m t : ℕ) :
    fDeltaCoord (A := A) m ∘ₗ deltaF (m + 1) t = tensorFd (deltaF m) t ∘ₗ fDeltaCoord m := by
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
  · wf_simp; wf_close
  · rcases t with _ | t <;> wf_simp <;> wf_close

lemma fDelta_E (m s : ℕ) :
    fDeltaCoord (A := A) m ∘ₗ deltaE (m + 1) s = tensorEd (deltaE m) s ∘ₗ fDeltaCoord m := by
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
  · rcases s with _ | s <;> wf_simp <;> wf_close
  · wf_simp; wf_close

lemma fDelta_H (m : ℕ) :
    fDeltaCoord (A := A) m ∘ₗ Hop (weylWt (m + 1)) =
      Hop (tensorWt (weylWt m)) ∘ₗ fDeltaCoord m := by
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_) <;> wf_simp <;>
    wf_close

lemma gDelta_F (m t : ℕ) (hm : 1 ≤ m) :
    gDeltaCoord (A := A) m ∘ₗ tensorFd (deltaF m) t = deltaF (m - 1) t ∘ₗ gDeltaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  rcases t with _ | t <;> wf_simp <;> wf_close

lemma gDelta_E (m s : ℕ) (hm : 1 ≤ m) :
    gDeltaCoord (A := A) m ∘ₗ tensorEd (deltaE m) s = deltaE (m - 1) s ∘ₗ gDeltaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  rcases s with _ | s <;> wf_simp <;> wf_close

lemma gDelta_H (m : ℕ) (hm : 1 ≤ m) :
    gDeltaCoord (A := A) m ∘ₗ Hop (tensorWt (weylWt m)) =
      Hop (weylWt (m - 1)) ∘ₗ gDeltaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  wf_simp; wf_close

lemma fNabla_F (m t : ℕ) (hm : 1 ≤ m) :
    fNablaCoord (A := A) m ∘ₗ nablaF (m - 1) t = tensorFd (nablaF m) t ∘ₗ fNablaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
  · rcases n with _ | n <;> wf_simp <;> wf_close
  · rcases t with _ | t
    · wf_simp; wf_close
    · rcases Nat.lt_or_ge n (t + 1) with h | h
      · wf_simp; wf_close
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h
        wf_simp; wf_close

lemma fNabla_E (m s : ℕ) (hm : 1 ≤ m) :
    fNablaCoord (A := A) m ∘ₗ nablaE (m - 1) s = tensorEd (nablaE m) s ∘ₗ fNablaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
  · rcases n with _ | n <;> rcases s with _ | s <;> wf_simp <;> wf_close
  · wf_simp; wf_close

lemma fNabla_H (m : ℕ) (hm : 1 ≤ m) :
    fNablaCoord (A := A) m ∘ₗ Hop (weylWt (m - 1)) =
      Hop (tensorWt (weylWt m)) ∘ₗ fNablaCoord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine LinearMap.ext fun x => ext_tensor (fun n hn => ?_) (fun n hn => ?_)
  · rcases n with _ | n <;> wf_simp <;> wf_close
  · wf_simp; wf_close

lemma gNabla_F (m t : ℕ) :
    gNablaCoord (A := A) m ∘ₗ tensorFd (nablaF m) t = nablaF (m + 1) t ∘ₗ gNablaCoord m := by
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  rcases n with _ | n
  · rcases t with _ | t <;> wf_simp <;> wf_close
  rcases t with _ | t
  · wf_simp; wf_close
  rcases Nat.lt_or_ge n (t + 1) with h | h
  · wf_simp; wf_close
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h
    rcases Nat.lt_or_ge m (j + 1) with h' | h'
    · wf_simp; wf_close
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h'
      wf_simp; wf_close

lemma gNabla_E (m s : ℕ) :
    gNablaCoord (A := A) m ∘ₗ tensorEd (nablaE m) s = nablaE (m + 1) s ∘ₗ gNablaCoord m := by
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  rcases n with _ | n <;> rcases s with _ | s <;> wf_simp <;> wf_close

lemma gNabla_H (m : ℕ) :
    gNablaCoord (A := A) m ∘ₗ Hop (tensorWt (weylWt m)) =
      Hop (weylWt (m + 1)) ∘ₗ gNablaCoord m := by
  refine LinearMap.ext fun y => ext_ext0 fun n hn => ?_
  rcases n with _ | n <;> wf_simp <;> wf_close

end WeylFilt
