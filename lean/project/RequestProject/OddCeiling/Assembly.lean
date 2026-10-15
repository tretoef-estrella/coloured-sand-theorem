module

public import RequestProject.OddCeiling.Smith

/-!
# Part T of `CSI14_the_ceiling_at_p.md`: Theorem 6.5 at p (assembly lemma)

## Encoding

* `A : Matrix (Fin N) (Fin N) ℤ`, the prime `p : ℕ` with `hp : p.Prime`; `ddP p A r` is the
  `p`-adic determinantal divisor of Part D, cast to `ℤ`.
* As in C1/C2/C5, the integer sequence is `x : ℕ → ℤ` (only positions `< N` matter) and its
  integer fit is C1's `AntitonicFit.ifit N x`; the window `[N − r, N)` is `Finset.Ico (N - r) N`.
* "The exponents of (Q1)" are the exponents `e` of **any** Smith form at `p` of `A` in the sense
  of (Q1) (`P A Q = diag(u_j p^{e_j} if j < ρ, else 0)` with `p ∤ det P`, `p ∤ det Q`, `ρ ≤ N`,
  `e` non-decreasing on `[0, ρ)`, `p ∤ u_j`); such a form exists by `Q1_smith`.  The conclusion also
  records `ρ = N`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Matrix

variable {p : ℕ}

/-- **(T1)** (Theorem 6.5 at `p`, assembly lemma) of `CSI14_the_ceiling_at_p.md`, for a given
Smith form at `p` of `A`: if `det A ≠ 0` and, for every `r ≤ N`,
(F) `Σ_{j ∈ [N−r, N)} ifit N x j ≤ ddP p A r − r·C` and
(U) `ddP p A r − r·C ≤ Σ_{j ∈ [N−r, N)} x j`, then `ddP p A r = r·C + Σ_{j∈[N−r,N)} ifit N x j`
for every `r ≤ N`, `ρ = N`, and `e j = C + ifit N x (N − 1 − j)` for `j < N`. -/
theorem T1_assembly_of_smith (hp : p.Prime) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : A.det ≠ 0)
    (x : ℕ → ℤ) (C : ℤ)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤ (ddP p A r : ℤ) - r * C)
    (hU : ∀ r ≤ N, (ddP p A r : ℤ) - r * C ≤ ∑ j ∈ Ico (N - r) N, x j)
    (P Q : Matrix (Fin N) (Fin N) ℤ) (hP : ¬ (p : ℤ) ∣ P.det) (hQ : ¬ (p : ℤ) ∣ Q.det)
    {ρ : ℕ} (hρ : ρ ≤ N) {e : ℕ → ℕ} (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j)
    {u : ℕ → ℤ} (hu : ∀ j, ¬ (p : ℤ) ∣ u j)
    (hD : P * A * Q = diagonal (fun j : Fin N =>
      if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0)) :
    (∀ r ≤ N, (ddP p A r : ℤ) = r * C + ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j) ∧
      ρ = N ∧ ∀ j < N, (e j : ℤ) = C + AntitonicFit.ifit N x (N - 1 - j) := by
  obtain ⟨hdd, -, hdet⟩ := Q2_smith hp A P Q hP hQ hρ he hu hD
  have hρN : ρ = N := hdet.1 hA
  subst hρN
  have hdH : ∀ r ≤ ρ, Divisors.dHat C (fun j => (e j : ℤ)) r = (ddP p A r : ℤ) - r * C := by
    intro r hr
    rw [Divisors.dHat, hdd r hr]
    push_cast; ring
  have he' : ∀ i j, i ≤ j → j < ρ → (fun j => (e j : ℤ)) i ≤ (fun j => (e j : ℤ)) j :=
    fun i j hij hj => by simp only; exact_mod_cast he i j hij hj
  obtain ⟨h1, h2⟩ := Divisors.theorem_B_without_M ρ x C (fun j => (e j : ℤ)) he'
    (fun r hr => by rw [hdH r hr]; exact hF r hr) (fun r hr => by rw [hdH r hr]; exact hU r hr)
  refine ⟨fun r hr => ?_, rfl, h2⟩
  have := h1 r hr
  rw [hdH r hr] at this
  linarith

/-- **(T1)** (Theorem 6.5 at `p`, assembly lemma) of `CSI14_the_ceiling_at_p.md`: let
`A : Matrix (Fin N) (Fin N) ℤ` with `det A ≠ 0`, `x : ℕ → ℤ`, `C ∈ ℤ`, and suppose, for every
`r ≤ N`, (F) `Σ_{j ∈ [N−r, N)} ifit N x j ≤ ddP p A r − r·C` and
(U) `ddP p A r − r·C ≤ Σ_{j ∈ [N−r, N)} x j`.  Then `ddP p A r = r·C + Σ_{j∈[N−r,N)} ifit N x j`
for every `r ≤ N`, and for every Smith form at `p` of `A` as in (Q1) (one exists, by `Q1_smith`),
`ρ = N` and its exponents are `e j = C + ifit N x (N − 1 − j)` for `j < N`. -/
theorem T1_assembly (hp : p.Prime) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : A.det ≠ 0)
    (x : ℕ → ℤ) (C : ℤ)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤ (ddP p A r : ℤ) - r * C)
    (hU : ∀ r ≤ N, (ddP p A r : ℤ) - r * C ≤ ∑ j ∈ Ico (N - r) N, x j) :
    (∀ r ≤ N, (ddP p A r : ℤ) = r * C + ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j) ∧
      ∀ (P Q : Matrix (Fin N) (Fin N) ℤ) (ρ : ℕ) (e : ℕ → ℕ) (u : ℕ → ℤ),
        ¬ (p : ℤ) ∣ P.det → ¬ (p : ℤ) ∣ Q.det → ρ ≤ N →
        (∀ i j, i ≤ j → j < ρ → e i ≤ e j) → (∀ j, ¬ (p : ℤ) ∣ u j) →
        P * A * Q = diagonal (fun j : Fin N =>
          if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) →
        ρ = N ∧ ∀ j < N, (e j : ℤ) = C + AntitonicFit.ifit N x (N - 1 - j) := by
  obtain ⟨P, Q, hP, hQ, ρ, hρ, e, he, u, hu, hD⟩ := Q1_smith hp N A
  refine ⟨(T1_assembly_of_smith hp A hA x C hF hU P Q hP hQ hρ he hu hD).1, ?_⟩
  intro P' Q' ρ' e' u' hP' hQ' hρ' he' hu' hD'
  exact (T1_assembly_of_smith hp A hA x C hF hU P' Q' hP' hQ' hρ' he' hu' hD').2

end ColouredSand.OddTwist
