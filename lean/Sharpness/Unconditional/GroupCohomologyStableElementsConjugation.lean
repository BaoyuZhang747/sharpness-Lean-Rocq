import Sharpness.Unconditional.GroupCohomologyStableElementsIso

/-! Stable elements impose compatibility with every actual partial conjugation,
not just the double-coset representatives used in the transfer proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory MackeyDecomposition
variable {R G A : Type u} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A]

theorem stableElements_partial_conjugation (S : Subgroup G) (n : ℕ)
    (x : stableElements (R := R) (A := A) S n)
    (P : Subgroup S) (f : P →* S) (g : G)
    (hf : ∀ a : P, (f a : G) = g * ((a : S) : G) * g⁻¹) :
    pull f n x.1 = pull P.subtype n x.1 := by
  let j : P →* intersection S S g := P.subtype.codRestrict _ (fun a => by
    change g * ((a : S) : G) * g⁻¹ ∈ S
    rw [← hf a]
    exact (f a).2)
  have hc : (intersectionConjugation S S g).comp j = f := by
    ext a
    exact (hf a).symm
  have hi : (intersection S S g).subtype.comp j = P.subtype := rfl
  have h := congrArg (fun y => pull (R := R) (A := A) j n y) (x.2 g)
  change (pull (intersectionConjugation S S g) n ≫ pull j n).hom x.1 =
    (pull (intersection S S g).subtype n ≫ pull j n).hom x.1 at h
  rwa [← pull_comp, ← pull_comp, hc, hi] at h

theorem mem_stableElements_iff_partial_conjugations (S : Subgroup G) (n : ℕ)
    (x : value R S A n) :
    x ∈ stableElements (R := R) (A := A) S n ↔
      ∀ (P : Subgroup S) (f : P →* S) (g : G),
        (∀ a : P, (f a : G) = g * ((a : S) : G) * g⁻¹) →
          pull f n x = pull P.subtype n x := by
  constructor
  · intro hx P f g hf
    exact stableElements_partial_conjugation S n ⟨x, hx⟩ P f g hf
  · intro h g
    exact h (intersection S S g) (intersectionConjugation S S g) g (fun _ => rfl)

end Sharpness.OrdinaryCohomology
