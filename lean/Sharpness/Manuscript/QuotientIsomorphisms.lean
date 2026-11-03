import Sharpness.Unconditional.CollectionRestrictionFusion
import Sharpness.Unconditional.FusionAtomicVanishing
import Sharpness.Unconditional.ScalarImageHigherIso
import Sharpness.Unconditional.QuotientSaturationComplete
import Sharpness.QuotientCategoryIso
import Sharpness.PrimeFieldScalars

/-! The all-degree collection isomorphism and the strict central-quotient
category isomorphism in Lemma 3.1(iii–iv). Atomic deletion supplies the former
without a published restriction theorem as an assumption. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Vanishing of a short exact sequence's kernel in every degree, including
zero, makes its quotient map an isomorphism on every higher limit. -/
theorem higherLimit_map_isIso_of_kernel_zero_all_degrees
    {K D E : CoefficientCategory R C} (f : K ⟶ D) (g : D ⟶ E)
    (hf : ∀ P, Function.Injective (f.app P))
    (hg : ∀ P, Function.Surjective (g.app P))
    (hex : ∀ P, Function.Exact (f.app P) (g.app P))
    (hK : ∀ i, IsZero (higherLimit K i)) (n : ℕ) :
    IsIso ((higherLimitFunctor R C n).map g) := by
  let T : ShortComplex (CoefficientCategory R C) := ShortComplex.mk f g (by
    ext P x
    exact (hex P).apply_apply_eq_zero x)
  let U := T.map coefficientCochainFunctor
  have hU : U.ShortExact := coefficientCochain_shortExact T hf hg hex
  have hzero (i : ℕ) : IsZero (U.X₁.homology i) :=
    IsZero.of_iso (hK i) (Unconditional.categoryBarCohomologyIso K i).symm
  haveI : Mono (HomologicalComplex.homologyMap U.g n) :=
    (hU.homology_exact₂ n).mono_g ((hzero n).eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap U.g n) :=
    (hU.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((hzero (n + 1)).eq_of_tgt _ _)
  have hmap : IsIso (HomologicalComplex.homologyMap U.g n) :=
    isIso_of_mono_of_epi _
  exact (NatIso.isIso_map_iff (Unconditional.categoryBarCohomologyNatIso n) g).mpr hmap

namespace ZeroExtension

variable (R : Type u) [CommRing R] {C : Type u} [Category.{u} C] [Fintype C]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    (X : ObjectProperty C)
    (upward : ∀ {P Q : C}, (P ⟶ Q) → X P → X Q)

/-- Atomic vanishing on the complementary isomorphism classes gives an
actual collection-restriction isomorphism, in degree zero as well. -/
def restrictionHigherLimitIso
    (atomic : ∀ Q, ¬ X Q → ∀ A : CoefficientCategory R C,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (M : CoefficientCategory R C) (n : ℕ) :
    higherLimit M n ≅ higherLimit (X.ι.op ⋙ M) n := by
  classical
  let π := unitMap R X upward M
  let T := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel π }
  have hK : ∀ i, IsZero (higherLimit (kernel π) i) :=
    AtomicFiltration.higherLimits_zero_of_atomic R rank rank_mono iso_of_rank
      (fun Q => ¬ X Q) atomic (kernel π) (by
        intro P hP
        exact unitKernel_zero_on_collection R X upward M P (not_not.mp hP))
  have heval (P : Cᵒᵖ) := hT.map_of_exact ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj P)
  haveI : IsIso ((higherLimitFunctor R C n).map π) :=
    higherLimit_map_isIso_of_kernel_zero_all_degrees (kernel.ι π) π
      (fun P => (heval P).moduleCat_injective_f)
      (fun P => (heval P).moduleCat_surjective_g)
      (fun P => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (heval P).exact) hK n
  exact asIso ((higherLimitFunctor R C n).map π) ≪≫
    ZeroExtension.higherLimitIso R X upward (X.ι.op ⋙ M) n

end ZeroExtension

namespace FusionSystem

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (R : Type u) [CommRing R]

/-- Collection restriction is an isomorphism in every degree for any
conjugacy- and overgroup-closed centric collection containing the radical
objects. The atomic input is the proved saturation theorem. -/
def collectionRestrictionHigherLimitIso
    (C : F.ComparisonCollection p)
    (conjugate : ∀ {P Q : F.Orbit}, (P ≅ Q) →
      C.member P.as.subgroup → C.member Q.as.subgroup)
    (M : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit (C.toCentric.op ⋙ M) n := by
  classical
  letI : Finite F.CentricOrbit := Finite.of_injective (fun P => P.obj)
    (fun P Q h => ObjectProperty.FullSubcategory.ext h)
  letI := Fintype.ofFinite F.CentricOrbit
  let e := ZeroExtension.restrictionHigherLimitIso R
    (fun P : F.CentricOrbit => F.orbitOrder P.obj)
    (fun {P Q : F.CentricOrbit} (f : P ⟶ Q) => F.orbitOrder_mono f.hom)
    (fun {P Q : F.CentricOrbit} (f : P ⟶ Q) h => (ObjectProperty.isIso_hom_iff f).mp
      (F.orbit_isIso_of_equal_order f.hom h))
    C.inCentric (C.inCentric_upward conjugate)
    (fun Q hQ => F.nonradical_atomic_higherLimits_zero p hS sat R Q (fun hrad =>
      hQ (C.contains_centric_radical _ Q.property hrad))) M n
  exact e ≪≫ (higherLimitEquivalenceIso R C.centricEquivalence
    (C.toCentric.op ⋙ M) n).symm

variable {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

/-- Lemma 3.1(iv), over every commutative ring and in every degree. The
quotient system and its saturation are constructed, not supplied inputs. -/
def quotientCollectionHigherLimitIsoUnconditional
    (M : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit
      ((F.quotientComparisonCollection p hS sat hZ
        (F.akoQuotientInput hZ p hS sat)).toCentric.op ⋙ M) n :=
  F.collectionRestrictionHigherLimitIso p hS sat R
    (F.quotientComparisonCollection p hS sat hZ (F.akoQuotientInput hZ p hS sat))
    (fun e hP => F.quotientCollection_conjugate hZ p hS sat
      (F.akoQuotientInput hZ p hS sat) hP
      (F.groupEquivOfOrbitIso e) (F.groupEquivOfOrbitIso_allowed e)) M n

/-- Lemma 3.1(iii) for the constructed central quotient: an isomorphism
of the actual categories, with strict inverse functors. -/
def quotientActualCentricIsoCatUnconditional :
    IsoCat (F.quotientComparisonCollection p hS sat hZ
      (F.akoQuotientInput hZ p hS sat)).Orbit (F.centralQuotient hZ).CentricOrbit :=
  F.quotientActualCentricIsoCat hZ p hS sat (F.akoQuotientInput hZ p hS sat)

/-- The coefficient field and orientation stated literally in Lemma 3.1(iv). -/
def quotientCollectionHigherLimitIsoPrimeField
    (M : CoefficientCategory (PrimeField.{u} p) F.CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit
      ((F.quotientComparisonCollection p hS sat hZ
        (F.akoQuotientInput hZ p hS sat)).toCentric.op ⋙ M) n :=
  F.quotientCollectionHigherLimitIsoUnconditional p hS sat (PrimeField.{u} p) hZ M n

/-- The strict isomorphism has the already constructed quotient map on
every preimage object and every representative morphism. -/
theorem quotientActualCentricIsoCatUnconditional_forward :
    F.quotientLiftToCollection hZ p hS sat (F.akoQuotientInput hZ p hS sat) ⋙
      (F.quotientActualCentricIsoCatUnconditional p hS sat hZ).functor =
      F.quotientCentricFunctor hZ p hS sat (F.akoQuotientInput hZ p hS sat) :=
  F.quotientActualCentricIsoCat_forward hZ p hS sat (F.akoQuotientInput hZ p hS sat)

/-- On every object of the actual collection, the strict isomorphism sends
the subgroup to its image under the quotient projection. -/
theorem quotientActualCentricIsoCatUnconditional_obj
    (P : (F.quotientComparisonCollection p hS sat hZ
      (F.akoQuotientInput hZ p hS sat)).Orbit) :
    ((F.quotientActualCentricIsoCatUnconditional p hS sat hZ).functor.obj P).obj.as.subgroup =
      P.obj.as.subgroup.map (QuotientGroup.mk' Z) := by
  obtain ⟨A, rfl⟩ := (F.quotientLiftToCollection_obj_bijective hZ p hS sat
    (F.akoQuotientInput hZ p hS sat)).surjective P
  change ((F.quotientLiftToCollection hZ p hS sat (F.akoQuotientInput hZ p hS sat) ⋙
    (F.quotientActualCentricIsoCatUnconditional p hS sat hZ).functor).obj A).obj.as.subgroup = _
  rw [F.quotientActualCentricIsoCatUnconditional_forward p hS sat hZ]
  exact (F.quotientPreimage_image A.obj.as).symm

end FusionSystem
end Sharpness
