module

public import RequestProject.Windows.Basic

/-!
# Part H of `C14_windows_and_theorem_D.md`: the dance commutes with ring homomorphisms

For a ring homomorphism `φ : A →+* B` between commutative rings, `φ ∘ p` is
`fun s f => φ (p s f)` and `φ ∘ κ` is `fun s u f => φ (κ s u f)`.
* **(H1)** `H1_pT`, `H1_κT`, `H1_pSp`, `H1_κSp`, `H1_relabP`, `H1_relabK`, `H1_danceAux`,
  `H1_dance`;
* **(H2)** `H2_Mfin`, `H2_pσ`;
* **(H3)** `H3_final_matrix`.
-/

@[expose] public section

universe u v

namespace Windows

open Payment Split Dance

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (φ : A →+* B)

/-- **(H1)** for the twisted payments: `pT (φ ∘ p) = φ ∘ pT p` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_pT {S : Type*} (p : S → ℕ → A) :
    pT (fun s f => φ (p s f)) = fun s f => φ (pT p s f) := by
  funext s f; simp [pT]

/-- **(H1)** for the twisted couplings: `κT (φ ∘ p) (φ ∘ κ) = φ ∘ κT p κ` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_κT {S : Type*} [Fintype S] [LinearOrder S] (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    κT (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) = fun s u f => φ (κT p κ s u f) := by
  funext s u f; simp [κT, map_sum]

/-- **(H1)** for the split payments: `pSp (φ ∘ p) = φ ∘ pSp p` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_pSp {S : Type*} (p : S → ℕ → A) :
    pSp (fun s f => φ (p s f)) = fun q f => φ (pSp p q f) := by
  funext q f; unfold pSp; split_ifs <;> simp

/-- **(H1)** for the split couplings: `κSp (φ ∘ p) (φ ∘ κ) = φ ∘ κSp p κ` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_κSp {S : Type*} [Fintype S] [LinearOrder S] (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    κSp (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) =
      fun q' q f => φ (κSp p κ q' q f) := by
  funext q' q f; unfold κSp; split_ifs <;> simp [map_sum]

/-- **(H1)** for the relabelled payments (*Part H* of `C14_windows_and_theorem_D.md`). -/
theorem H1_relabP {S S' : Type*} [LE S] [LE S'] (e : S ≃o S') (p : S' → ℕ → A) :
    relabP e (fun s f => φ (p s f)) = fun s f => φ (relabP e p s f) := rfl

/-- **(H1)** for the relabelled couplings (*Part H* of `C14_windows_and_theorem_D.md`). -/
theorem H1_relabK {S S' : Type*} [LE S] [LE S'] (e : S ≃o S') (κ : S' → S' → ℕ → A) :
    relabK e (fun s u f => φ (κ s u f)) = fun s u f => φ (relabK e κ s u f) := rfl

/-- **(H1)** for the dance data before the final cast (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_danceAux (ds : List Bool) : ∀ (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A),
    danceAux ds r (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) =
      ((fun s f => φ ((danceAux ds r p κ).1 s f)),
        (fun s u f => φ ((danceAux ds r p κ).2 s u f))) := by
  induction ds with
  | nil => intro r p κ; rfl
  | cons d rest ih =>
    intro r p κ
    cases d
    · simp only [danceAux]
      rw [H1_pT, H1_κT, ih]; rfl
    · simp only [danceAux]
      rw [H1_pSp, H1_κSp, H1_relabP, H1_relabK, ih]; rfl

/-- **(H1)** The dance commutes with ring homomorphisms:
`dance ds r (φ ∘ p) (φ ∘ κ) = (φ ∘ (dance ds r p κ).1, φ ∘ (dance ds r p κ).2)` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H1_dance (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    dance ds r (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) =
      ((fun s f => φ ((dance ds r p κ).1 s f)),
        (fun s u f => φ ((dance ds r p κ).2 s u f))) := by
  unfold dance
  rw [H1_danceAux]
  rfl

/-- **(H2)** `Mfin (φ ∘ p) (φ ∘ κ) = (Mfin p κ).map φ` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H2_Mfin {R : ℕ} (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) :
    Mfin (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) = (Mfin p κ).map φ := by
  ext s s'
  simp only [Mfin, Matrix.map_apply]
  split_ifs <;> simp [map_ofNat]

/-- **(H2)** `pσ α i` over `B` is `φ ∘ pσ α i` over `A` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H2_pσ (α i : ℕ) : (pσ α i : Fin 1 → ℕ → B) = fun s f => φ (pσ α i s f) := by
  funext s f; simp [pσ, map_ofNat]

/-- `κσ` over `B` is `φ ∘ κσ` over `A` (used for (H3) of `C14_windows_and_theorem_D.md`). -/
theorem H2_κσ : (κσ : Fin 1 → Fin 1 → ℕ → B) = fun s u f => φ (κσ s u f) := by
  funext s u f; simp [κσ]

/-- **(H3)** For every commutative ring `A`, the final matrix of `dance ds 1 (pσ α i) κσ` over `A`
is the image under `Int.castRingHom A` of the same matrix over `ℤ` (*Part H* of
`C14_windows_and_theorem_D.md`). -/
theorem H3_final_matrix (A : Type u) [CommRing A] (ds : List Bool) (α i : ℕ) :
    Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ (A := A) α i) κσ).2 =
      (Mfin (dance ds 1 (pσ (A := ℤ) α i) κσ).1 (dance ds 1 (pσ (A := ℤ) α i) κσ).2).map
        (Int.castRingHom A) := by
  rw [H2_pσ (Int.castRingHom A), H2_κσ (Int.castRingHom A), H1_dance, H2_Mfin]

end Windows
