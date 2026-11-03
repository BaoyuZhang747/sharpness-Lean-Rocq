import Sharpness.ColumnFirstPageHorizontal
import Sharpness.CochainReplacementHorizontal

/-! Entire first-page row complexes, including their differentials,
are identified with vertical cohomology complexes and with the actual
category coefficient complex for the cochain replacement. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

def columnFirstPageRowEmbedding (q : ℕ) :
    (ComplexShape.up ℕ).Embedding (ComplexShape.spectralSequenceNat (1,1-(1 : ℤ))) :=
  ComplexShape.Embedding.mk' _ _ (fun p => (p,q))
    (fun _ _ h => congrArg Prod.fst h) (by
      intro i j
      change i+1=j ↔ (i : ℤ)+1=j ∧ (q : ℤ)+0=q
      omega)

instance columnFirstPageRowEmbedding_isRelIff (q : ℕ) : (columnFirstPageRowEmbedding q).IsRelIff := by
  dsimp only [columnFirstPageRowEmbedding]
  infer_instance

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def totalColumnFirstPageRow (q : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((totalColumnSpectralSequence K).page 1).restriction (columnFirstPageRowEmbedding q)

set_option backward.isDefEq.respectTransparency false in
def totalColumnFirstPageRowVerticalIso (q : ℕ) :
    totalColumnFirstPageRow K q ≅
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun p => totalColumnFirstPageVerticalIso K p q) (by
    intro i j hij
    have hj : i+1=j := hij
    subst j
    exact (totalColumnFirstPageVerticalIso_d K i q).symm)

variable {C : Type u} [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementFirstPageRowIso (q : ℕ) :
    totalColumnFirstPageRow (cochainReplacementBicomplex D) q ≅
      coefficientCochains (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q) :=
  totalColumnFirstPageRowVerticalIso (cochainReplacementBicomplex D) q ≪≫
    cochainReplacementHorizontalIso D q

end Sharpness
