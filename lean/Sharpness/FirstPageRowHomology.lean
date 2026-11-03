import Sharpness.ColumnFirstPageRows
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-! The homology of an actual first-page row equals the native
first-page homology, including the missing incoming differential at
p=0. Consequently its p-th cohomology computes the actual E2 term. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

theorem columnFirstPageShape_next (p q : ℕ) :
    (ComplexShape.spectralSequenceNat (1,1-(1 : ℤ))).next (p,q) = (p+1,q) :=
  ComplexShape.next_eq' _ (by change (p : ℤ)+1=p+1 ∧ (q : ℤ)+0=q; constructor <;> omega)

theorem columnFirstPageShape_prev (p q : ℕ) :
    (ComplexShape.spectralSequenceNat (1,1-(1 : ℤ))).prev (p,q) = (p-1,q) := by
  cases p with
  | zero =>
    apply ComplexShape.prev_eq_self'
    intro a ha
    change (a.1 : ℤ)+1=0 ∧ (a.2 : ℤ)+0=q at ha
    omega
  | succ p =>
    apply ComplexShape.prev_eq'
    change (p : ℤ)+1=p+1 ∧ (q : ℤ)+0=q
    constructor <;> omega

theorem columnNatShape_prev (p : ℕ) : (ComplexShape.up ℕ).prev p = p-1 := by
  cases p with
  | zero =>
    apply ComplexShape.prev_eq_self'
    intro a ha
    change a+1=0 at ha
    omega
  | succ p => exact ComplexShape.prev_eq' _ rfl

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def totalColumnFirstPageRowHomologyIso (p q : ℕ) :
    (totalColumnFirstPageRow K q).homology p ≅
      ((totalColumnSpectralSequence K).page 1).homology (p,q) :=
  ((totalColumnSpectralSequence K).page 1).restrictionHomologyIso (columnFirstPageRowEmbedding q)
    (p-1) p (p+1) (columnNatShape_prev p) ((ComplexShape.up ℕ).next_eq' rfl)
      rfl rfl rfl (columnFirstPageShape_prev p q) (columnFirstPageShape_next p q)

def totalColumnSecondPageRowIso (p q : ℕ) :
    ((totalColumnE₂SpectralSequence K).page 2).X (p,q) ≅ (totalColumnFirstPageRow K q).homology p :=
  (totalColumnSecondPageIso K p q).symm ≪≫ (totalColumnFirstPageRowHomologyIso K p q).symm

variable {C : Type u} [Category.{u} C] (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementSecondPageIso (p q : ℕ) :
    ((totalColumnE₂SpectralSequence (cochainReplacementBicomplex D)).page 2).X (p,q) ≅
    (coefficientCochains (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)).homology p :=
  totalColumnSecondPageRowIso (cochainReplacementBicomplex D) p q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p).mapIso
      (cochainReplacementFirstPageRowIso D q)

end Sharpness
