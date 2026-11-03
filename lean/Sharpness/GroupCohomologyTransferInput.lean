import Sharpness.GroupCohomologyPull
import Sharpness.MackeyFunctorData

/-! A common interface for ordinary cohomology transfer identities on
fixed native values and pullbacks. DPGroupCohomologyInput specializes it
to the ring itself, exactly as in DP Section 2, p.152. The separate
TrivialModuleTransferInput constructs the localized-integer module case
from accurately recorded additive global transfer facts; this generic
record by itself is not a new bibliography assertion.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A]

abbrev ModuleGroupCohomologyTransfer (R : Type u) [CommRing R] (S : Type u) [Group S]
    (A : Type u) [AddCommGroup A] [Module R A] (n : ℕ) :=
  ∀ (P Q : Subgroup S), P ≤ Q →
    OrdinaryCohomology.value R P A n →ₗ[R] OrdinaryCohomology.value R Q A n

abbrev GroupCohomologyTransfer (R : Type u) [CommRing R] (S : Type u) [Group S] (n : ℕ) :=
  ModuleGroupCohomologyTransfer R S R n

def groupCohomologyRawPull {P Q : F.Object} (f : P ⟶ Q) (n : ℕ) :
    OrdinaryCohomology.value R Q.subgroup A n →ₗ[R]
      OrdinaryCohomology.value R P.subgroup A n :=
  OrdinaryCohomology.pullLinear f.val n

theorem groupCohomologyRawPull_id (P : F.Object) (n : ℕ) :
    F.groupCohomologyRawPull (R := R) (A := A) (𝟙 P) n = LinearMap.id :=
  OrdinaryCohomology.pullLinear_id n

theorem groupCohomologyRawPull_comp {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T) (n : ℕ) :
    F.groupCohomologyRawPull (R := R) (A := A) (f ≫ g) n =
      (F.groupCohomologyRawPull f n).comp (F.groupCohomologyRawPull g n) :=
  OrdinaryCohomology.pullLinear_comp f.val g.val n

/-- The manuscript's explicit covariant map: pull back along the inverse
of the actual image isomorphism, then transfer along the image inclusion. -/
def groupCohomologyRawPush {n : ℕ} (tr : ModuleGroupCohomologyTransfer R S A n)
    {P Q : F.Object} (f : P ⟶ Q) :
    OrdinaryCohomology.value R P.subgroup A n →ₗ[R]
      OrdinaryCohomology.value R Q.subgroup A n :=
  (tr (F.imageSubgroup f) Q.subgroup (F.image_le f)).comp
    (F.groupCohomologyRawPull (F.imageIso f).inv n)

/-- A mathematical intermediate record, independent of its provenance.
Only fixed native values and pullbacks are allowed, before orbit descent.
It has no saturation, characteristic-p, or acyclicity field. -/
structure GroupCohomologyTransferLaws (A : Type u) [AddCommGroup A] [Module R A] (n : ℕ) where
  transfer : ModuleGroupCohomologyTransfer R S A n
  inner : ∀ (P : F.Object) (r : P.subgroup),
    F.groupCohomologyRawPull (R := R) (A := A) (F.inner P r) n = LinearMap.id
  transfer_comp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
    F.groupCohomologyRawPush transfer (f ≫ g) =
      (F.groupCohomologyRawPush transfer g).comp (F.groupCohomologyRawPush transfer f)
  transfer_iso : ∀ {P Q : F.Object} (e : P ≅ Q),
    F.groupCohomologyRawPush transfer e.hom = F.groupCohomologyRawPull e.inv n
  double_coset : ∀ {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T),
    (F.groupCohomologyRawPull f n).comp (F.groupCohomologyRawPush transfer g) =
      ∑ i : F.RawDoubleCosetTerm f g,
        (F.groupCohomologyRawPush transfer (F.concreteSpan f g i.out).left).comp
          (F.groupCohomologyRawPull (F.concreteSpan f g i.out).right n)

/-- The original DP Section 2 example, still restricted to coefficients A=R. -/
abbrev DPGroupCohomologyInput (n : ℕ) := F.GroupCohomologyTransferLaws (R := R) R n

end Sharpness.FusionSystem
