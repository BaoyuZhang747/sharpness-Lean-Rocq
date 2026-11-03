import Sharpness.Unconditional.NormalizerOrbitPointedPrefix
import Sharpness.Unconditional.NormalizerSubdivisionEvaluationPoint

/-! The actual singleton chain associated with a pointed normalized subgroup,
and arrows to it from literal surjective subgroup-image extensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

namespace NormalizerSubgroupExtension
variable {F} {P Q : Subgroup S} (τ : F.CentricChain) (I : F.CentricSubgroup)
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
  (a : F.NormalizerSubgroupExtension (τ.subgroup 0) I.val f)
  (hImage : (fun x : a.carrier => (a.extension.val x).val) ''
    {x | x.val ∈ τ.subgroup 0} = (I.val : Set S))

def toSingleton : F.NormalizerChainExtension τ (CentricChain.singleton I) f where
  indices := Fin.castLEOrderEmb (Nat.succ_le_succ (Nat.zero_le τ.length))
  carrier := a.carrier
  acting_le := a.acting_le
  chain_le := a.subgroup_le
  extension := a.extension
  onActing := a.onActing
  images i := by
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hImage

end NormalizerSubgroupExtension

variable (P : F.CentricOrbit)

def normalizerOrbitPointedSingleton (A : F.NormalizerPointedSubgroup P) :
    F.NormalizerOrbitPointed P := by
  let B : F.NormalizerOrbitPair := {
    centric := A.centric
    chain := CentricChain.singleton ⟨A.subgroup,A.subgroup_centric⟩
    normalizes := fun _ => A.normalizes }
  exact ⟨StructuredArrow.mk (Y := B) A.point.hom,A.point.isIso_hom⟩

theorem normalizerOrbitPointedFirst_singleton (A : F.NormalizerPointedSubgroup P) :
    (F.normalizerOrbitPointedFirst P).obj (F.normalizerOrbitPointedSingleton P A) = A := by
  have he : asIso A.point.hom = A.point := Iso.ext rfl
  change ({
    centric := A.centric
    point := asIso A.point.hom
    subgroup := A.subgroup
    subgroup_centric := A.subgroup_centric
    normalizes := A.normalizes } : F.NormalizerPointedSubgroup P) = A
  rw [he]

def normalizerOrbitPointedFirstBase (A : F.NormalizerPointedSubgroup P) :
    StructuredArrow A (F.normalizerOrbitPointedFirst P) :=
  StructuredArrow.mk (Y := F.normalizerOrbitPointedSingleton P A)
    (eqToHom (F.normalizerOrbitPointedFirst_singleton P A).symm)

def normalizerOrbitPointedToSingleton {X : F.NormalizerOrbitPointed P}
    (A : F.NormalizerPointedSubgroup P)
    (g : X.obj.right.centric.obj.as ⟶ A.centric.obj.as)
    (hg : X.obj.hom ≫ ObjectProperty.homMk (F.toOrbit.map g) = A.point.hom)
    (a : F.NormalizerSubgroupExtension (X.obj.right.chain.subgroup 0) A.subgroup g)
    (hImage : (fun x : a.carrier => (a.extension.val x).val) ''
      {x | x.val ∈ X.obj.right.chain.subgroup 0} = (A.subgroup : Set S)) :
    X ⟶ F.normalizerOrbitPointedSingleton P A :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (NormalizerOrbitPair.homMk g (a.toSingleton X.obj.right.chain
      ⟨A.subgroup,A.subgroup_centric⟩ hImage)) hg)

theorem normalizerOrbitPointedHom_subsingleton (X Y : F.NormalizerOrbitPointed P) :
    Subsingleton (X ⟶ Y) := by
  constructor
  intro f g
  apply ObjectProperty.hom_ext
  exact F.normalizerOrbitPointed_source_hom_ext P X Y.obj f.hom g.hom

end Sharpness.FusionSystem
