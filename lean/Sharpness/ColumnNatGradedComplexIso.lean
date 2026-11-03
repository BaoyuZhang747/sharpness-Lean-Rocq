import Sharpness.ColumnNatAssociatedGraded
import Sharpness.CochainUnitTwistCycles
import Sharpness.StrictlySupportedLiftIso
import Sharpness.ColumnFiltrationSupport
import Sharpness.CokernelEvaluationIso
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! The actual natural-number associated graded complex is the
extension of the signed p-th column. This is a cochain isomorphism,
not merely an equality of dimensions or unrelated cohomology modules. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits

def columnNatEmbedding (p : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun q => p+q)
    (fun i j h => Nat.add_left_cancel h) (by
      intro i j
      change i+1 = j ↔ p+i+1 = p+j
      omega)

instance columnNatEmbedding_isRelIff (p : ℕ) : (columnNatEmbedding p).IsRelIff := by
  dsimp only [columnNatEmbedding]
  infer_instance

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem totalColumnNatAssociatedGraded_term_zero (p n : ℕ) (hn : n < p) :
    IsZero ((totalColumnNatAssociatedGraded K p).X n) :=
  cokernel_term_zero (totalColumnFilteredMap K (Nat.le_succ p)) n
    (totalColumnFilteredComplex_term_zero K p n hn)

instance totalColumnNatAssociatedGraded_supported (p : ℕ) :
    (totalColumnNatAssociatedGraded K p).IsStrictlySupported (columnNatEmbedding p) where
  isZero n hn := totalColumnNatAssociatedGraded_term_zero K p n (by
    by_contra! h
    exact hn (n-p) (Nat.add_sub_of_le h))

set_option backward.isDefEq.respectTransparency false in
def totalColumnNatGradedRestrictionIso (p : ℕ) :
    (totalColumnNatAssociatedGraded K p).restriction (columnNatEmbedding p) ≅
      cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p) :=
  HomologicalComplex.Hom.isoOfComponents (totalColumnNatAssociatedGradedTermIso K p) (by
    intro i j hij
    have hj : i+1 = j := hij
    subst j
    rw [cochainUnitTwist_d]
    exact (totalColumnNatAssociatedGradedTermIso_d K p i).symm)

def totalColumnNatGradedComplexIso (p : ℕ) :
    totalColumnNatAssociatedGraded K p ≅
      (cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extend (columnNatEmbedding p) :=
  strictlySupportedLiftIso (columnNatEmbedding p) (totalColumnNatAssociatedGraded K p)
    (cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)) (totalColumnNatGradedRestrictionIso K p)

def totalColumnNatGradedCohomologyIso (p q : ℕ) :
    (totalColumnNatAssociatedGraded K p).homology (p+q) ≅ (K.X p).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (p+q)).mapIso
      (totalColumnNatGradedComplexIso K p) ≪≫
    (cochainUnitTwist (K.X p) ((-1 : ℤˣ)^p)).extendHomologyIso (columnNatEmbedding p) rfl ≪≫
      cochainUnitTwistCycleCohomologyIso (K.X p) ((-1 : ℤˣ)^p) q

end Sharpness
