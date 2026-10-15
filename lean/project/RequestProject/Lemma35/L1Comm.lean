module

public import RequestProject.Lemma35.L1Defs

/-!
# `C22_lemma_35_over_F2.md`: Part L, (L1) — commutation of `g` with `F^{(r)}`, `E^{(r)}`

For `r = 1, 2, 3` and every basis vector of `D`, `g ∘ F^{(r)} = F^{(r)} ∘ g` and
`g ∘ E^{(r)} = E^{(r)} ∘ g` on that basis vector, when `2 = 0` in `B`: both sides are compared
coordinate by coordinate (the proof sketch of (L1)).
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {B : Type*} [CommRing B]

section comm

variable (h2 : (2 : B) = 0)
include h2

set_option maxHeartbeats 4000000 in
lemma g_comm_F (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (i : ID) :
    gL ((D3 B).Fd r (Pi.single i 1 : ID → B)) = (T3 B).Fd r (gL (Pi.single i 1 : ID → B)) := by
  have h3 : (3 : B) = 1 := by linear_combination h2
  funext ⟨a, b, c⟩
  interval_cases r <;> rcases i with i | i | i <;> fin_cases i <;> fin_cases a <;>
    fin_cases b <;> fin_cases c <;>
    simp [gL, ofImg_apply, gimg, dsum, tensorV, tensorFd, V, VFd, delta, deltaF, VmatF,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply, Matrix.toLin'_apply,
      deltaMatF, one_add_one_eq_two, h2, h3]

set_option maxHeartbeats 4000000 in
lemma g_comm_E (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (i : ID) :
    gL ((D3 B).Ed r (Pi.single i 1 : ID → B)) = (T3 B).Ed r (gL (Pi.single i 1 : ID → B)) := by
  have h3 : (3 : B) = 1 := by linear_combination h2
  funext ⟨a, b, c⟩
  interval_cases r <;> rcases i with i | i | i <;> fin_cases i <;> fin_cases a <;>
    fin_cases b <;> fin_cases c <;>
    simp [gL, ofImg_apply, gimg, dsum, tensorV, tensorEd, V, VEd, delta, deltaE, VmatE,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply, Matrix.toLin'_apply,
      deltaMatE, one_add_one_eq_two, h2, h3]

end comm

end Lemma35
