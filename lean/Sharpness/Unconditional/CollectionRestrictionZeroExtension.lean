import Sharpness.Unconditional.AtomicHigherLimits

/-! Extension by zero from an upward-closed full subcategory, for
contravariant module-valued diagrams. Values are products indexed by the
membership proposition: a one-factor product inside, the zero module outside.
This avoids choices of isomorphic zero objects in the functor laws. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.ZeroExtension
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    (X : ObjectProperty C)
    (upward : ∀ {P Q : C}, (P ⟶ Q) → X P → X Q)

def value (M : CoefficientCategory R X.FullSubcategory) (P : Cᵒᵖ) : ModuleCat.{u} R :=
  ModuleCat.of R (∀ h : PLift (X P.unop), M.obj (op ⟨P.unop, h.down⟩))

def arrow (M : CoefficientCategory R X.FullSubcategory) {P Q : Cᵒᵖ} (f : P ⟶ Q) :
    value R X M P ⟶ value R X M Q := ModuleCat.ofHom
  { toFun := fun x hQ => M.map
      (ObjectProperty.homMk f.unop : (⟨Q.unop, hQ.down⟩ : X.FullSubcategory) ⟶
        ⟨P.unop, upward f.unop hQ.down⟩).op (x ⟨upward f.unop hQ.down⟩)
    map_add' := by intros; funext hQ; exact map_add _ _ _
    map_smul' := by intros; funext hQ; exact map_smul _ _ _ }

def coefficient (M : CoefficientCategory R X.FullSubcategory) : CoefficientCategory R C where
  obj := value R X M
  map := arrow R X upward M
  map_id P := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hP
    change M.map (𝟙 (op ⟨P.unop, hP.down⟩)) (x hP) = x hP
    rw [M.map_id]
    rfl
  map_comp {P Q T} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hT
    change M.map
      ((ObjectProperty.homMk f.unop : (⟨Q.unop, upward g.unop hT.down⟩ : X.FullSubcategory) ⟶
        ⟨P.unop, upward f.unop (upward g.unop hT.down)⟩).op ≫
      (ObjectProperty.homMk g.unop : (⟨T.unop, hT.down⟩ : X.FullSubcategory) ⟶
        ⟨Q.unop, upward g.unop hT.down⟩).op) _ = _
    rw [M.map_comp]
    rfl

def map {M N : CoefficientCategory R X.FullSubcategory} (α : M ⟶ N) :
    coefficient R X upward M ⟶ coefficient R X upward N where
  app P := ModuleCat.ofHom
    { toFun := fun x hP => α.app (op ⟨P.unop, hP.down⟩) (x hP)
      map_add' := by intros; funext hP; exact map_add _ _ _
      map_smul' := by intros; funext hP; exact map_smul _ _ _ }
  naturality {P Q} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hQ
    exact congrArg (fun t : M.obj (op ⟨P.unop, upward f.unop hQ.down⟩) ⟶
      N.obj (op ⟨Q.unop, hQ.down⟩) => t (x ⟨upward f.unop hQ.down⟩))
      (α.naturality (ObjectProperty.homMk f.unop :
        (⟨Q.unop, hQ.down⟩ : X.FullSubcategory) ⟶ ⟨P.unop, upward f.unop hQ.down⟩).op)

def functor : CoefficientCategory R X.FullSubcategory ⥤ CoefficientCategory R C where
  obj := coefficient R X upward
  map := map R X upward
  map_id M := by ext P x; rfl
  map_comp α β := by ext P x; rfl

instance functor_additive : (functor R X upward).Additive where
  map_add := by intros; rfl

instance functor_linear : (functor R X upward).Linear R where
  map_smul := by intros; rfl

def lift {M : CoefficientCategory R C} {N : CoefficientCategory R X.FullSubcategory}
    (α : X.ι.op ⋙ M ⟶ N) : M ⟶ coefficient R X upward N where
  app P := ModuleCat.ofHom
    { toFun := fun x hP => α.app (op ⟨P.unop, hP.down⟩) x
      map_add' := by intros; funext hP; exact map_add _ _ _
      map_smul' := by intros; funext hP; exact map_smul _ _ _ }
  naturality {P Q} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hQ
    exact congrArg (fun t : M.obj P ⟶ N.obj (op ⟨Q.unop, hQ.down⟩) => t x)
      (α.naturality (ObjectProperty.homMk f.unop :
        (⟨Q.unop, hQ.down⟩ : X.FullSubcategory) ⟶ ⟨P.unop, upward f.unop hQ.down⟩).op)

def restrict {M : CoefficientCategory R C} {N : CoefficientCategory R X.FullSubcategory}
    (α : M ⟶ coefficient R X upward N) : X.ι.op ⋙ M ⟶ N where
  app P := ModuleCat.ofHom
    { toFun := fun x => α.app (op P.unop.obj) x ⟨P.unop.property⟩
      map_add' x y := congrArg (fun t : value R X N (op P.unop.obj) => t ⟨P.unop.property⟩)
        ((α.app (op P.unop.obj)).hom.map_add x y)
      map_smul' r x := congrArg (fun t : value R X N (op P.unop.obj) => t ⟨P.unop.property⟩)
        ((α.app (op P.unop.obj)).hom.map_smul r x) }
  naturality {P Q} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun t : M.obj (op P.unop.obj) ⟶
      value R X N (op Q.unop.obj) => t x ⟨Q.unop.property⟩)
      (α.naturality f.unop.hom.op)

def homEquiv (M : CoefficientCategory R C) (N : CoefficientCategory R X.FullSubcategory) :
    (X.ι.op ⋙ M ⟶ N) ≃ (M ⟶ coefficient R X upward N) where
  toFun := lift R X upward
  invFun := restrict R X upward
  left_inv α := by ext P x; rfl
  right_inv α := by ext P x; rfl

/-- Restriction is left adjoint to extension by zero. -/
def adjunction : restrictionCoefficientFunctor R X.ι ⊣ functor R X upward :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R X upward
      homEquiv_naturality_left_symm := by intros; ext P x; rfl
      homEquiv_naturality_right := by intros; ext P x; rfl }

instance functor_preservesEpimorphisms : (functor R X upward).PreservesEpimorphisms where
  preserves {M N} α _ := by
    haveI : ∀ P, Epi (((functor R X upward).map α).app P) := by
      intro P
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro x
      classical
      have hs (hP : PLift (X P.unop)) :=
        (ModuleCat.epi_iff_surjective (α.app (op ⟨P.unop, hP.down⟩))).mp inferInstance (x hP)
      choose y hy using hs
      exact ⟨y, funext hy⟩
    exact NatTrans.epi_of_epi_app _

/-- All higher limits of the extension by zero agree with the higher
limits on the collection. -/
def higherLimitIso (M : CoefficientCategory R X.FullSubcategory) (n : ℕ) :
    higherLimit (coefficient R X upward M) n ≅ higherLimit M n := by
  let L := restrictionCoefficientFunctor R X.ι
  haveI : L.PreservesHomology := by
    dsimp [L, restrictionCoefficientFunctor]
    infer_instance
  exact (extAdjunctionIso R (L := L) (adjunction R X upward)
    (constantCoefficient R C) M n).symm

def unitMap (M : CoefficientCategory R C) :
    M ⟶ coefficient R X upward (X.ι.op ⋙ M) := lift R X upward (𝟙 _)

@[simp] theorem unitMap_apply (M : CoefficientCategory R C) (P : Cᵒᵖ)
    (x : M.obj P) (hP : PLift (X P.unop)) :
    (unitMap R X upward M).app P x hP = x := rfl

theorem unitMap_surjective (M : CoefficientCategory R C) (P : Cᵒᵖ) :
    Function.Surjective ((unitMap R X upward M).app P) := by
  classical
  intro x
  by_cases hP : X P.unop
  · refine ⟨x ⟨hP⟩, ?_⟩
    funext h
    rfl
  · refine ⟨0, ?_⟩
    funext h
    exact (hP h.down).elim

instance unitMap_epi (M : CoefficientCategory R C) : Epi (unitMap R X upward M) := by
  haveI : ∀ P, Epi ((unitMap R X upward M).app P) :=
    fun P => (ModuleCat.epi_iff_surjective _).mpr (unitMap_surjective R X upward M P)
  exact NatTrans.epi_of_epi_app _

theorem isZero_value_of_not (M : CoefficientCategory R X.FullSubcategory)
    (P : Cᵒᵖ) (hP : ¬ X P.unop) : IsZero (value R X M P) := by
  letI : Subsingleton (value R X M P) := ⟨fun f g => funext fun h => (hP h.down).elim⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- A coefficient already supported on the collection is its own extension
by zero. -/
def supportedIso (M : CoefficientCategory R C)
    (supported : ∀ P : C, ¬ X P → IsZero (M.obj (op P))) :
    M ≅ coefficient R X upward (X.ι.op ⋙ M) := by
  haveI : ∀ P, IsIso ((unitMap R X upward M).app P) := by
    intro P
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, unitMap_surjective R X upward M P⟩
    intro x y hxy
    classical
    by_cases hP : X P.unop
    · exact congrFun hxy ⟨hP⟩
    · exact (ModuleCat.subsingleton_of_isZero (supported P.unop hP)).elim x y
  haveI := NatIso.isIso_of_isIso_app (unitMap R X upward M)
  exact asIso (unitMap R X upward M)

/-- The supported-coefficient collection comparison, in every degree. -/
def supportedHigherLimitIso (M : CoefficientCategory R C)
    (supported : ∀ P : C, ¬ X P → IsZero (M.obj (op P))) (n : ℕ) :
    higherLimit M n ≅ higherLimit (X.ι.op ⋙ M) n :=
  Sharpness.higherLimitIso (supportedIso R X upward M supported) n ≪≫
    ZeroExtension.higherLimitIso R X upward (X.ι.op ⋙ M) n

end Sharpness.ZeroExtension
