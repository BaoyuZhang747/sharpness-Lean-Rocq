import Sharpness.Unconditional.NormalizerOrbitPointedSubgroups
import Sharpness.Unconditional.CentralizerConstruction
import Sharpness.Unconditional.NerveAdjunctionChains
import Sharpness.FusionMinimal
import Sharpness.FusionCentricClosure

/-! A genuine join contraction of the pointed normalized-subgroup enlargement
category. This concerns subgroups; the comparison with strict chains remains
a separate construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u vA uA

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] (F : FusionSystem S)

namespace NormalizerSubgroupExtension
variable {F} {P Q R T : Subgroup S} {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}

def join (a : F.NormalizerSubgroupExtension R T f) :
    F.NormalizerSubgroupExtension (P ⊔ R) (Q ⊔ T) f where
  carrier := a.carrier
  acting_le := a.acting_le
  subgroup_le := sup_le a.acting_le a.subgroup_le
  extension := a.extension
  onActing := a.onActing
  maps x hx := by
    let hD : P ⊔ R ≤ a.carrier := sup_le a.acting_le a.subgroup_le
    let g := F.inclusion hD ≫ a.extension
    have hm : ∀ y : (P ⊔ R : Subgroup S), (g.val y).val ∈ Q ⊔ T := by
      apply join_image_mem g.val ((Q ⊔ T).subgroupOf ⊤)
      · intro y
        change (a.extension.val ⟨y.val,a.acting_le y.property⟩).val ∈ Q ⊔ T
        rw [a.onActing y]
        exact Subgroup.mem_sup_left (f.val y).property
      · intro y
        exact Subgroup.mem_sup_right (a.maps ⟨y.val,a.subgroup_le y.property⟩ y.property)
    exact hm ⟨x.val,hx⟩

end NormalizerSubgroupExtension

variable [Finite S] (P : F.CentricOrbit)

def normalizerPointedSubgroupJoin : F.NormalizerPointedSubgroup P ⥤ F.NormalizerPointedSubgroup P where
  obj A := {
    centric := A.centric
    point := A.point
    subgroup := A.centric.obj.as.subgroup ⊔ A.subgroup
    subgroup_centric := F.centric_overgroup A.subgroup_centric le_sup_right
    normalizes := (le_sup_left : A.centric.obj.as.subgroup ≤ _).trans Subgroup.le_normalizer }
  map f := by
    apply homOfLE
    obtain ⟨g,hg,g₀,hg₀,⟨a⟩⟩ := leOfHom f
    exact ⟨g,hg,g₀,hg₀,⟨a.join⟩⟩

def normalizerPointedSubgroupUnit :
    𝟭 (F.NormalizerPointedSubgroup P) ⟶ F.normalizerPointedSubgroupJoin P where
  app A := homOfLE ⟨𝟙 _,Category.comp_id _,𝟙 _,F.toOrbit.map_id _,⟨{
    carrier := A.centric.obj.as.subgroup ⊔ A.subgroup
    acting_le := le_sup_left
    subgroup_le := le_sup_right
    extension := F.inclusion le_top
    onActing := fun _ => rfl
    maps := fun _ hx => Subgroup.mem_sup_right hx }⟩⟩

def normalizerPointedSubgroupBase : F.NormalizerPointedSubgroup P where
  centric := P
  point := Iso.refl _
  subgroup := P.obj.as.subgroup
  subgroup_centric := P.property
  normalizes := Subgroup.le_normalizer

def normalizerPointedSubgroupBaseToJoin :
    (Functor.const (F.NormalizerPointedSubgroup P)).obj (F.normalizerPointedSubgroupBase P) ⟶
      F.normalizerPointedSubgroupJoin P where
  app A := by
    let g := F.orbitRepresentative A.point.hom.hom
    refine homOfLE ⟨A.point.hom,Category.id_comp _,g,F.orbitRepresentative_map _,⟨?_⟩⟩
    exact {
      carrier := P.obj.as.subgroup
      acting_le := le_rfl
      subgroup_le := le_rfl
      extension := g ≫ F.inclusion le_top
      onActing := fun _ => rfl
      maps := fun x _ => Subgroup.mem_sup_left (g.val x).property }

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasCoproducts.{u} A]

def normalizerPointedSubgroupChainHomotopyEquiv (R : A) :
    HomotopyEquiv ((nerve (F.NormalizerPointedSubgroup P)).chainComplex R)
      ((nerve (Discrete PUnit.{u+1})).chainComplex R) where
  hom := SSet.chainComplexMap (nerveMap (Functor.star.{u} (F.NormalizerPointedSubgroup P))) R
  inv := SSet.chainComplexMap (nerveMap (Functor.fromPUnit (F.normalizerPointedSubgroupBase P))) R
  homotopyHomInvId := by
    have h := (nerveNaturalTransformationChainHomotopy (F.normalizerPointedSubgroupBaseToJoin P) R).trans
      (nerveNaturalTransformationChainHomotopy (F.normalizerPointedSubgroupUnit P) R).symm
    have hc : Functor.star.{u} (F.NormalizerPointedSubgroup P) ⋙
        Functor.fromPUnit (F.normalizerPointedSubgroupBase P) =
          (Functor.const (F.NormalizerPointedSubgroup P)).obj (F.normalizerPointedSubgroupBase P) := rfl
    have hmap : SSet.chainComplexMap (nerveMap
        ((Functor.const (F.NormalizerPointedSubgroup P)).obj (F.normalizerPointedSubgroupBase P))) R =
      SSet.chainComplexMap (nerveMap (Functor.star.{u} (F.NormalizerPointedSubgroup P))) R ≫
        SSet.chainComplexMap (nerveMap (Functor.fromPUnit (F.normalizerPointedSubgroupBase P))) R := by
      rw [← hc]
      exact ((SSet.chainComplexFunctor A).obj R).map_comp
        (nerveMap (Functor.star.{u} (F.NormalizerPointedSubgroup P)))
        (nerveMap (Functor.fromPUnit (F.normalizerPointedSubgroupBase P)))
    have hi : SSet.chainComplexMap (nerveMap (𝟭 (F.NormalizerPointedSubgroup P))) R = 𝟙 _ :=
      ((SSet.chainComplexFunctor A).obj R).map_id _
    simpa only [hmap,hi] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← ((SSet.chainComplexFunctor A).obj R).map_comp]
    have hc : Functor.fromPUnit (F.normalizerPointedSubgroupBase P) ⋙
        Functor.star.{u} (F.NormalizerPointedSubgroup P) = 𝟭 (Discrete PUnit.{u+1}) :=
      Functor.punit_ext' _ _
    change SSet.chainComplexMap (nerveMap
      (Functor.fromPUnit (F.normalizerPointedSubgroupBase P) ⋙
        Functor.star.{u} (F.NormalizerPointedSubgroup P))) R = _
    rw [hc]
    exact ((SSet.chainComplexFunctor A).obj R).map_id _)

theorem normalizerPointedSubgroupProjection_quasiIso [CategoryWithHomology A] (R : A) :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (F.NormalizerPointedSubgroup P))) R) :=
  (F.normalizerPointedSubgroupChainHomotopyEquiv P R).quasiIso_hom

end Sharpness.FusionSystem
