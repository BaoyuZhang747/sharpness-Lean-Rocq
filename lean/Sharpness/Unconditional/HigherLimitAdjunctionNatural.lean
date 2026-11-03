import Sharpness.Unconditional.AtomicHigherLimits
import Sharpness.HigherLimitsEquivalence

/-! Coefficient-natural derived adjunction for the original module-valued
Ext and higher limits. The projective resolution is fixed in the first
argument, and all comparisons are natural in the coefficient argument.
This supplies the full naturality assertion of the manuscript's adjoint
and equivalence comparison, in every degree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w

namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite

section Ext
variable (R : Type u) [CommRing R]
    {A : Type v} [Category.{u} A] [Abelian A] [Linear R A]

/-- Postcomposition on the Hom complex of a fixed chain complex. -/
def resolutionHomComplexMap (P : ChainComplex A ℕ) {Y Z : A} (a : Y ⟶ Z) :
    P.linearYonedaObj R Y ⟶ P.linearYonedaObj R Z where
  f n := ModuleCat.ofHom (Linear.rightComp R _ a)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change P.d j i ≫ (f ≫ a) = (P.d j i ≫ f) ≫ a
    exact (Category.assoc _ _ _).symm

/-- The Hom complex is a functor of its coefficient object. -/
def resolutionHomComplexFunctor (P : ChainComplex A ℕ) :
    A ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj Y := P.linearYonedaObj R Y
  map := resolutionHomComplexMap R P
  map_id Y := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact Category.comp_id f
  map_comp a b := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (Category.assoc f a b).symm

variable [EnoughProjectives A]

set_option maxHeartbeats 800000 in
/-- The native projective-resolution calculation of Ext is natural in
the coefficient object, including degree zero. -/
theorem projectiveIsoExt_naturality {X : A} (P : ProjectiveResolution X)
    {Y Z : A} (a : Y ⟶ Z) (n : ℕ) :
    ((Ext R A n).obj (op X)).map a ≫ (P.isoExt (R := R) n Z).hom =
      (P.isoExt (R := R) n Y).hom ≫
        HomologicalComplex.homologyMap (resolutionHomComplexMap R P.complex a) n := by
  change ((((linearYoneda R A).map a).rightOp.leftDerived n).app X).unop ≫ _ = _
  rw [P.leftDerived_app_eq ((linearYoneda R A).map a).rightOp n]
  dsimp [ProjectiveResolution.isoExt]
  simp only [Category.assoc, ← Iso.unop_hom, ← Iso.unop_inv,
    Iso.hom_inv_id_assoc]
  congr 1
  have h := (HomologicalComplex.homologyOpNatIso (ModuleCat.{u} R)
    (ComplexShape.up ℕ) n).inv.naturality (resolutionHomComplexMap R P.complex a).op
  exact (congrArg Quiver.Hom.unop h).symm

/-- A fixed projective resolution computes Ext naturally in coefficients. -/
def projectiveExtNatIso {X : A} (P : ProjectiveResolution X) (n : ℕ) :
    (Ext R A n).obj (op X) ≅
      resolutionHomComplexFunctor R P.complex ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n :=
  NatIso.ofComponents (P.isoExt (R := R) n) (by
    intro Y Z a
    exact projectiveIsoExt_naturality R P a n)

variable {B : Type w} [Category.{u} B] [Abelian B] [Linear R B]
    {L : A ⥤ B} {G : B ⥤ A} [L.Additive] [G.Additive] [G.Linear R]

/-- The linear adjunction comparison of Hom complexes is natural in the
coefficient object. -/
def adjunctionResolutionHomNatIso (adj : L ⊣ G) (P : ChainComplex A ℕ) :
    resolutionHomComplexFunctor R ((L.mapHomologicalComplex _).obj P) ≅
      G ⋙ resolutionHomComplexFunctor R P :=
  NatIso.ofComponents (adjunctionLinearYonedaComplexIso R adj P) (by
    intro Y Z a
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change adj.homEquiv _ _ (f ≫ a) = adj.homEquiv _ _ f ≫ G.map a
    exact adj.homEquiv_naturality_right f a)

/-- Exact derived adjunction as a natural isomorphism of the original
module-valued Ext functors, with no additional comparison hypotheses. -/
def extAdjunctionNatIso [EnoughProjectives B]
    [L.PreservesHomology] [G.PreservesEpimorphisms]
    (adj : L ⊣ G) (X : A) (n : ℕ) :
    (Ext R B n).obj (op (L.obj X)) ≅ G ⋙ (Ext R A n).obj (op X) := by
  letI : L.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms adj
  let P := projectiveResolution X
  let Q := L.mapProjectiveResolution P
  exact projectiveExtNatIso R Q n ≪≫
    Functor.isoWhiskerRight (adjunctionResolutionHomNatIso R adj P.complex)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n) ≪≫
    Functor.isoWhiskerLeft G (projectiveExtNatIso R P n).symm

end Ext

section HigherLimits
variable (R : Type u) [CommRing R]
    {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Restriction along a right adjoint preserves higher limits naturally
in arbitrary coefficients, for every degree. -/
def higherLimitRightAdjointNatIso (r : C ⥤ D) (i : D ⥤ C) (adj : r ⊣ i) (n : ℕ) :
    higherLimitFunctor R C n ≅
      restrictionCoefficientFunctor R i ⋙ higherLimitFunctor R D n := by
  let L := restrictionCoefficientFunctor R r
  let G := restrictionCoefficientFunctor R i
  haveI : L.PreservesHomology := by
    dsimp [L, restrictionCoefficientFunctor]
    infer_instance
  haveI : G.PreservesEpimorphisms := by
    dsimp [G, restrictionCoefficientFunctor]
    infer_instance
  exact extAdjunctionNatIso R (L := L) (G := G)
    (adj.op.whiskerLeft (ModuleCat.{u} R)) (constantCoefficient R D) n

/-- Equivalences of indexing categories preserve higher limits naturally
in the coefficient diagram, in all degrees. -/
def higherLimitEquivalenceNatIso (e : C ≌ D) (n : ℕ) :
    higherLimitFunctor R D n ≅
      restrictionCoefficientFunctor R e.functor ⋙ higherLimitFunctor R C n :=
  higherLimitRightAdjointNatIso R e.inverse e.functor e.symm.toAdjunction n

end HigherLimits
end Sharpness.Unconditional
