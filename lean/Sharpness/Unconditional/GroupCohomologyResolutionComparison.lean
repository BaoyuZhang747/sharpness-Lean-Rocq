import Sharpness.GroupCohomologyPull

/-! Explicit contravariant Hom-complex maps and the comparison principle
used to transport restriction and transfer identities between resolutions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G]

/-- Actual precomposition on the linear Hom complex. -/
def homComplexPrecomp {X Y : ChainComplex (Rep R G) ℕ}
    (V : Rep R G) (f : X ⟶ Y) :
    Y.linearYonedaObj R V ⟶ X.linearYonedaObj R V :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R (Rep R G)).obj V).rightOp.mapHomologicalComplex _).map f).op

@[simp]
theorem homComplexPrecomp_apply {X Y : ChainComplex (Rep R G) ℕ}
    (V : Rep R G) (f : X ⟶ Y) (n : ℕ) (a : Y.X n ⟶ V) :
    (homComplexPrecomp V f).f n a = f.f n ≫ a := rfl

/-- Chain homotopies remain homotopies after taking the contravariant
linear Hom complex. -/
def homComplexPrecompHomotopy {X Y : ChainComplex (Rep R G) ℕ}
    (V : Rep R G) {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (homComplexPrecomp V f) (homComplexPrecomp V g) :=
  (((linearYoneda R (Rep R G)).obj V).rightOp.mapHomotopy h).unop

theorem homComplexPrecomp_homology_eq {X Y : ChainComplex (Rep R G) ℕ}
    (V : Rep R G) {f g : X ⟶ Y} (h : Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (homComplexPrecomp V f) n =
      HomologicalComplex.homologyMap (homComplexPrecomp V g) n :=
  (homComplexPrecompHomotopy V h).homologyMap_eq n

/-- Two actual maps of projective resolutions lifting the same map
induce equal maps on cohomology after applying Hom into any representation. -/
theorem homComplexPrecomp_eq_of_same_augmentation
    {Z W : Rep R G} (P : ProjectiveResolution Z) (Q : ProjectiveResolution W)
    (V : Rep R G) (f : Z ⟶ W) (a b : P.complex ⟶ Q.complex)
    (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ (Rep R G)).map f)
    (hb : b ≫ Q.π = P.π ≫ (ChainComplex.single₀ (Rep R G)).map f) (n : ℕ) :
    HomologicalComplex.homologyMap (homComplexPrecomp V a) n =
      HomologicalComplex.homologyMap (homComplexPrecomp V b) n :=
  homComplexPrecomp_homology_eq V (ProjectiveResolution.liftHomotopy f a b ha hb) n

end Sharpness.OrdinaryCohomology
