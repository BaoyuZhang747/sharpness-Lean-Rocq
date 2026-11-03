import Sharpness.Unconditional.CategoryBarExactness
import Mathlib.Algebra.Homology.Functor

/-! The concrete bar augmentation is a pointwise homotopy equivalence,
so the projective bar complex resolves the constant coefficient diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- A section of the evaluated bar augmentation, using the identity string. -/
def categoryBarSection (X : Cᵒᵖ) :
    ModuleCat.of R R ⟶ (categoryBarTerm R C 0).obj X :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R _
    (ModuleCat.freeMk (⟨ComposableArrows.mk₀ X.unop, 𝟙 _⟩ : categoryBarBasis C 0 X)))

@[simp]
theorem categoryBarSection_one (X : Cᵒᵖ) :
    categoryBarSection (R := R) X 1 =
      ModuleCat.freeMk (⟨ComposableArrows.mk₀ X.unop, 𝟙 _⟩ : categoryBarBasis C 0 X) := by
  exact one_smul R (ModuleCat.freeMk (R := R)
    (⟨ComposableArrows.mk₀ X.unop, 𝟙 _⟩ : categoryBarBasis C 0 X))

@[simp]
theorem categoryBarSection_augmentation (X : Cᵒᵖ) :
    categoryBarSection (R := R) X ≫ (categoryBarAugmentation 0).app X = 𝟙 (ModuleCat.of R R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (categoryBarAugmentation (R := R) 0).app X
    (r • ModuleCat.freeMk (⟨ComposableArrows.mk₀ X.unop, 𝟙 _⟩ : categoryBarBasis C 0 X)) = r
  rw [map_smul, categoryBarAugmentation_freeMk]
  exact mul_one r

theorem categoryBarInsert_zero_face_one (X : Cᵒᵖ) :
    categoryBarInsert (R := R) 0 X ≫ (categoryBarMap (SimplexCategory.δ (1 : Fin 2))).app X =
      (categoryBarAugmentation 0).app X ≫ categoryBarSection X := by
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (categoryBarMap (R := R) (SimplexCategory.δ (1 : Fin 2))).app X
      (categoryBarInsert 0 X (ModuleCat.freeMk ⟨s, g⟩)) =
    categoryBarSection X ((categoryBarAugmentation 0).app X (ModuleCat.freeMk ⟨s, g⟩))
  rw [categoryBarAugmentation_freeMk, categoryBarSection_one]
  simp only [categoryBarInsert, categoryBarMap, ModuleCat.free_map_apply]
  apply congrArg (ModuleCat.freeMk (R := R))
  refine Sigma.ext ?_ ?_
  · apply ComposableArrows.ext₀
    rfl
  · change HEq ((𝟙 X.unop) ≫ categoryChainHeadArrow (SimplexCategory.δ (1 : Fin 2))
        (s.precomp g)) (𝟙 X.unop)
    simp only [Category.id_comp]
    rfl

/-- Evaluate the augmented bar simplicial diagram at an object. -/
def categoryBarAugmentedAt (X : Cᵒᵖ) : SimplicialObject.Augmented (ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X)).obj (categoryBarAugmented R C)

@[reassoc (attr := simp)]
theorem categoryBarInsert_delta_zero (n : ℕ) (X : Cᵒᵖ) :
    categoryBarInsert (R := R) n X ≫ (categoryBarAugmentedAt X).left.δ 0 = 𝟙 _ :=
  categoryBarInsert_comp_face_zero n X

@[reassoc (attr := simp)]
theorem categoryBarInsert_delta_succ (n : ℕ) (X : Cᵒᵖ) (i : Fin (n + 2)) :
    categoryBarInsert (R := R) (n + 1) X ≫ (categoryBarAugmentedAt X).left.δ i.succ =
      (categoryBarAugmentedAt X).left.δ i ≫ categoryBarInsert n X :=
  categoryBarInsert_comp_face_succ n X i

@[reassoc (attr := simp)]
theorem categoryBarInsert_delta_one (X : Cᵒᵖ) :
    categoryBarInsert (R := R) 0 X ≫ (categoryBarAugmentedAt X).left.δ (1 : Fin 2) =
      (categoryBarAugmentedAt X).hom.app (op ⦋0⦌) ≫ categoryBarSection X :=
  categoryBarInsert_zero_face_one X

/-- After evaluation at any object, the bar augmentation is a homotopy
equivalence. Only the proved face identities enter the chain homotopy. -/
def categoryBarPointwiseHomotopyEquiv (X : Cᵒᵖ) :
    HomotopyEquiv (AlternatingFaceMapComplex.obj (categoryBarAugmentedAt (R := R) X).left)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj (categoryBarAugmentedAt X).right) where
  hom := AlternatingFaceMapComplex.ε.app (categoryBarAugmentedAt X)
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (categoryBarSection X)
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    simp [categoryBarAugmentedAt, categoryBarAugmented]
    erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    change (categoryBarAugmentation (R := R) 0).app X (categoryBarSection X (1 : R)) = (1 : R)
    rw [categoryBarSection_one, categoryBarAugmentation_freeMk])
  homotopyHomInvId :=
    { hom i := Pi.single (i + 1) (-categoryBarInsert i X)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
          simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C := AlternatingFaceMapComplex.obj (categoryBarAugmentedAt (R := R) X).left)]
          change (categoryBarAugmentation (R := R) 0).app X ≫ categoryBarSection X =
            -𝟙 ((categoryBarTerm R C 0).obj X) +
              (categoryBarAugmentation (R := R) 0).app X ≫ categoryBarSection X +
              𝟙 ((categoryBarTerm R C 0).obj X)
          abel
        | succ i =>
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_succ (n := i + 2), Preadditive.sum_comp,
            Preadditive.comp_sum, pow_succ]
          change 0 = -𝟙 ((categoryBarTerm R C (i + 1)).obj X) +
            𝟙 ((categoryBarTerm R C (i + 1)).obj X)
          simp }

/-- The chain augmentation of the projective bar complex. -/
def categoryBarAugmentationChain :
    categoryBarComplex R C ⟶ (ChainComplex.single₀ (CoefficientCategory R C)).obj
      (constantCoefficient R C) :=
  AlternatingFaceMapComplex.ε.app (categoryBarAugmented R C)

/-- Evaluation commutes with the alternating face construction. -/
def categoryBarEvaluationIso (X : Cᵒᵖ) :
    AlternatingFaceMapComplex.obj (categoryBarAugmentedAt (R := R) X).left ≅
      (((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X).mapHomologicalComplex _).obj
        (categoryBarComplex R C) :=
  eqToIso (CategoryTheory.Functor.congr_obj
    (map_alternatingFaceMapComplex ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X)).symm
    (categoryBarSimplicial R C))

/-- The evaluated chain augmentation is a homotopy equivalence. -/
def categoryBarEvaluationHomotopyEquiv (X : Cᵒᵖ) :
    HomotopyEquiv
      ((((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X).mapHomologicalComplex _).obj
        (categoryBarComplex R C))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj ((constantCoefficient R C).obj X)) :=
  (HomotopyEquiv.ofIso (categoryBarEvaluationIso X).symm).trans
    (categoryBarPointwiseHomotopyEquiv X)

theorem categoryBarEvaluationHomotopyEquiv_f_zero (X : Cᵒᵖ) :
    (categoryBarEvaluationHomotopyEquiv (R := R) X).hom.f 0 =
      (categoryBarAugmentation 0).app X := by
  simp [categoryBarEvaluationHomotopyEquiv, categoryBarEvaluationIso,
    categoryBarPointwiseHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans,
    categoryBarAugmentedAt, categoryBarAugmented]

theorem categoryBarAugmentationChain_evaluation (X : Cᵒᵖ) :
    (((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X).mapHomologicalComplex _).map
        categoryBarAugmentationChain ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app (constantCoefficient R C) =
        (categoryBarEvaluationHomotopyEquiv (R := R) X).hom := by
  apply HomologicalComplex.to_single_hom_ext
  change (categoryBarAugmentation (R := R) 0).app X ≫ 𝟙 _ =
    (categoryBarEvaluationHomotopyEquiv (R := R) X).hom.f 0
  rw [Category.comp_id]
  exact (categoryBarEvaluationHomotopyEquiv_f_zero (R := R) X).symm

instance categoryBarAugmentationChain_quasiIso :
    QuasiIso (categoryBarAugmentationChain (R := R) (C := C)) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro X
  have h : QuasiIso (categoryBarEvaluationHomotopyEquiv (R := R) X).hom := inferInstance
  rw [← categoryBarAugmentationChain_evaluation] at h
  exact quasiIso_of_comp_right (hφφ' := h)

/-- The explicit free-representable bar complex is a genuine projective
resolution of the constant coefficient diagram. -/
def categoryBarResolution : ProjectiveResolution (constantCoefficient R C) where
  complex := categoryBarComplex R C
  π := categoryBarAugmentationChain

end Sharpness.Unconditional
