import Sharpness.RealizationUnitCochains
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Contractible

/-! Base cases for the homology comparison of the actual realization unit.
The uniform comparison for arbitrary simplicial sets is not assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R]

/-- The actual realization unit on a point is an isomorphism of simplicial sets. -/
theorem unit_zero_isIso : IsIso (realizationSingularUnit (Δ[0] : SSet.{u})) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro m
  letI : Subsingleton ((Δ[0] : SSet.{u}).obj m) :=
    ⟨fun x y => SSet.stdSimplex.objEquiv.injective
      (SimplexCategory.isTerminalZero.hom_ext _ _)⟩
  letI : Subsingleton ((realizationSingularFunctor.obj (Δ[0] : SSet.{u})).obj m) :=
    (TopCat.toSSetObjEquiv _ _).subsingleton
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,
    fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

/-- Extra degeneracy contracts the actual simplicial chains to the constant
augmentation target, with the actual augmentation as forward map. -/
def extraDegeneracyChains (X : SSet.Augmented.{u})
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X) :
    HomotopyEquiv (SSet.chainComplex X.left (ModuleCat.of R R))
      (SSet.chainComplex ((SimplicialObject.const (Type u)).obj X.right) (ModuleCat.of R R)) where
  hom := SSet.chainComplexMap X.hom (ModuleCat.of R R)
  inv := SSet.chainComplexMap ed.section_ (ModuleCat.of R R)
  homotopyHomInvId := by
    have h := ed.homotopy.sSetChainComplexMap (ModuleCat.of R R)
    change Homotopy ((simplicialChainsFunctor R).map (X.hom ≫ ed.section_))
      ((simplicialChainsFunctor R).map (𝟙 (X.left : SSet.{u}))) at h
    rw [(simplicialChainsFunctor R).map_comp] at h
    have hid : (simplicialChainsFunctor R).map (𝟙 (X.left : SSet.{u})) = 𝟙 _ :=
      (simplicialChainsFunctor R).map_id _
    rw [hid] at h
    exact h
  homotopyInvHomId := Homotopy.ofEq (by
    change (simplicialChainsFunctor R).map ed.section_ ≫
      (simplicialChainsFunctor R).map X.hom = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, ed.section_comp_hom,
      CategoryTheory.Functor.map_id])

/-- Any map from a contractible space to a one-point space gives the actual
singular-chain homotopy equivalence. -/
def contractibleToPointChains {X Y : TopCat.{u}} [ContractibleSpace X] [Unique Y]
    (f : X ⟶ Y) :
    HomotopyEquiv ((SingularCohomology.chainsFunctor R).obj X)
      ((SingularCohomology.chainsFunctor R).obj Y) := by
  let x := Classical.choose (id_nullhomotopic X)
  let h := Classical.choice (Classical.choose_spec (id_nullhomotopic X))
  let g : Y ⟶ X := TopCat.const x
  let hfg : TopCat.Homotopy (f ≫ g) (𝟙 X) := h.symm
  have hgf : g ≫ f = 𝟙 Y := by
    ext y
    exact Subsingleton.elim _ _
  exact
    { hom := (SingularCohomology.chainsFunctor R).map f
      inv := (SingularCohomology.chainsFunctor R).map g
      homotopyHomInvId := by
        simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
          hfg.singularChainComplexFunctorObjMap (ModuleCat.of R R)
      homotopyInvHomId := Homotopy.ofEq (by
        rw [← CategoryTheory.Functor.map_comp, hgf, CategoryTheory.Functor.map_id]) }

/-- The realized standard simplex is contractible by its actual convex model. -/
theorem standardSimplex_contractible (n : SimplexCategory) :
    ContractibleSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj n)) := by
  letI : ContractibleSpace (_root_.stdSimplex ℝ (Fin (n.len + 1))) :=
    (convex_stdSimplex ℝ (Fin (n.len + 1))).contractibleSpace
      ⟨(_root_.stdSimplex.vertex 0).1, (_root_.stdSimplex.vertex 0).2⟩
  exact n.toTopHomeo.contractibleSpace

/-- The simplicial collapse of a standard simplex induces a quasi-isomorphism. -/
theorem standardSimplex_collapse_quasiIso (n : SimplexCategory) :
    QuasiIso ((simplicialChainsFunctor R).map
      (SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from n))) := by
  let X := SSet.Augmented.stdSimplex.{u}.obj n
  let Y := SSet.Augmented.stdSimplex.{u}.obj ⦋0⦌
  let f : X.left ⟶ Y.left := SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from n)
  let eX := extraDegeneracyChains R X (SSet.Augmented.StandardSimplex.extraDegeneracy n)
  let eY := extraDegeneracyChains R Y (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋0⦌)
  haveI : QuasiIso ((simplicialChainsFunctor R).map X.hom) := eX.quasiIso_hom
  haveI : QuasiIso ((simplicialChainsFunctor R).map Y.hom) := eY.quasiIso_hom
  have h : f ≫ Y.hom = X.hom := by
    apply NatTrans.ext
    funext m
    exact terminalIsTerminal.hom_ext _ _
  have hc : (simplicialChainsFunctor R).map f ≫ (simplicialChainsFunctor R).map Y.hom =
      (simplicialChainsFunctor R).map X.hom := by
    rw [← (simplicialChainsFunctor R).map_comp, h]
  haveI : QuasiIso ((simplicialChainsFunctor R).map f ≫
      (simplicialChainsFunctor R).map Y.hom) := hc.symm ▸ inferInstance
  exact quasiIso_of_comp_right ((simplicialChainsFunctor R).map f)
    ((simplicialChainsFunctor R).map Y.hom)

/-- The actual adjunction unit is a chain quasi-isomorphism on every standard
simplex, over every commutative coefficient ring and in every degree. -/
theorem standardSimplex_unit_quasiIso (n : SimplexCategory) :
    QuasiIso (realizationUnitChainMap R (SSet.stdSimplex.{u}.obj n)) := by
  let f := SSet.stdSimplex.{u}.map (SimplexCategory.isTerminalZero.from n)
  letI := unit_zero_isIso.{u}
  haveI : QuasiIso ((simplicialChainsFunctor R).map f) :=
    standardSimplex_collapse_quasiIso R n
  letI := standardSimplex_contractible.{u} n
  haveI : QuasiIso ((simplicialChainsFunctor R).map (realizationSingularFunctor.map f)) :=
    (contractibleToPointChains R (SSet.toTop.map f)).quasiIso_hom
  haveI : QuasiIso ((simplicialChainsFunctor R).map f ≫
      (simplicialChainsFunctor R).map (realizationSingularUnit (Δ[0] : SSet.{u}))) :=
    inferInstance
  have h : (simplicialChainsFunctor R).map f ≫
      (simplicialChainsFunctor R).map (realizationSingularUnit (Δ[0] : SSet.{u})) =
      realizationUnitChainMap R (SSet.stdSimplex.{u}.obj n) ≫
        (simplicialChainsFunctor R).map (realizationSingularFunctor.map f) := by
    rw [← (simplicialChainsFunctor R).map_comp, realizationSingularUnit_naturality]
    exact (simplicialChainsFunctor R).map_comp _ _
  haveI : QuasiIso (realizationUnitChainMap R (SSet.stdSimplex.{u}.obj n) ≫
      (simplicialChainsFunctor R).map (realizationSingularFunctor.map f)) :=
    h ▸ inferInstance
  exact quasiIso_of_comp_right _
    ((simplicialChainsFunctor R).map (realizationSingularFunctor.map f))

/-- The same actual unit comparison on cochains with an arbitrary coefficient
module; projective chain terms justify dualizing without injectivity assumptions. -/
theorem standardSimplex_unit_cochain_quasiIso (n : SimplexCategory) (A : ModuleCat.{u} R) :
    QuasiIso (realizationUnitCochainMap R (SSet.stdSimplex.{u}.obj n) A) := by
  let X := SSet.stdSimplex.{u}.obj n
  letI (k : ℕ) : Projective ((X.chainComplex (ModuleCat.of R R)).X k) :=
    SingularCohomology.simplicialChains_projective R X k
  letI (k : ℕ) : Projective (((SingularCohomology.chainsFunctor R).obj
      (SSet.toTop.obj X)).X k) :=
    SingularCohomology.chainsFunctor_projective R (SSet.toTop.obj X) k
  letI : QuasiIso (realizationUnitChainMap R X) := standardSimplex_unit_quasiIso R n
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A
    (realizationUnitChainMap R X)

end Sharpness.RealizationUnitHomology
