import Sharpness.CentricChains
import Mathlib.Order.Hom.Set

/-! Fusion conjugacy of actual strict centric chains. A conjugacy is
an increasing bijection of indices and an actual fusion isomorphism
of the top subgroups preserving every subgroup in the chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

def topSubgroup (σ : F.CentricChain) : Subgroup S := σ.subgroup (Fin.last σ.length)

def topRawObject (σ : F.CentricChain) : F.Object := ⟨σ.topSubgroup⟩

structure Conjugacy (σ τ : F.CentricChain) where
  indices : Fin (σ.length + 1) ≃o Fin (τ.length + 1)
  topIso : σ.topRawObject ≅ τ.topRawObject
  maps : ∀ (i : Fin (σ.length + 1)) (x : σ.topSubgroup),
    x.val ∈ σ.subgroup i ↔ (topIso.hom.val x).val ∈ τ.subgroup (indices i)

namespace Conjugacy
variable {σ τ υ : F.CentricChain}

def refl (σ : F.CentricChain) : Conjugacy σ σ where
  indices := OrderIso.refl _
  topIso := Iso.refl _
  maps _ _ := Iff.rfl

def symm (c : Conjugacy σ τ) : Conjugacy τ σ where
  indices := c.indices.symm
  topIso := c.topIso.symm
  maps i x := by
    have hx : c.topIso.hom.val (c.topIso.inv.val x) = x :=
      congrArg (fun f => f.val x) c.topIso.inv_hom_id
    have hm := c.maps (c.indices.symm i) (c.topIso.inv.val x)
    rw [hx, c.indices.apply_symm_apply] at hm
    exact hm.symm

def trans (c : Conjugacy σ τ) (d : Conjugacy τ υ) : Conjugacy σ υ where
  indices := c.indices.trans d.indices
  topIso := c.topIso.trans d.topIso
  maps i x := (c.maps i x).trans (d.maps (c.indices i) (c.topIso.hom.val x))

theorem length_eq (c : Conjugacy σ τ) : σ.length = τ.length := by
  have h := Fintype.card_congr c.indices.toEquiv
  simp only [Fintype.card_fin] at h
  omega

theorem indices_eq_cast (c : Conjugacy σ τ) :
    c.indices = Fin.castOrderIso (congrArg (fun n => n + 1) c.length_eq) :=
  Subsingleton.elim _ _

theorem subgroup_image (c : Conjugacy σ τ) (i : Fin (σ.length + 1)) :
    (fun x : σ.topSubgroup => (c.topIso.hom.val x).val) ''
        {x | x.val ∈ σ.subgroup i} =
      (τ.subgroup (c.indices i) : Set S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (c.maps i x).mp hx
  · intro hy
    have hytop : y ∈ τ.topSubgroup := τ.subgroup_mono (Fin.le_last _) hy
    let y' : τ.topSubgroup := ⟨y, hytop⟩
    let x : σ.topSubgroup := c.topIso.inv.val y'
    have hx : c.topIso.hom.val x = y' :=
      congrArg (fun f => f.val y') c.topIso.inv_hom_id
    refine ⟨x, (c.maps i x).mpr ?_, congrArg Subtype.val hx⟩
    rw [hx]
    exact hy

def ofTopIso (h : σ.length = τ.length) (e : σ.topRawObject ≅ τ.topRawObject)
    (hm : ∀ i : Fin (σ.length + 1),
      (fun x : σ.topSubgroup => (e.hom.val x).val) '' {x | x.val ∈ σ.subgroup i} =
        (τ.subgroup (Fin.cast (congrArg (fun n => n + 1) h) i) : Set S)) :
    Conjugacy σ τ where
  indices := Fin.castOrderIso (congrArg (fun n => n + 1) h)
  topIso := e
  maps i x := by
    have hh := congrArg (fun T : Set S => (e.hom.val x).val ∈ T) (hm i)
    constructor
    · intro hx
      exact Eq.mp hh ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, heq⟩ := Eq.mpr hh hx
      have hyx : y = x := F.injective e.hom.val e.hom.property (Subtype.ext heq)
      subst y
      exact hy

end Conjugacy

def Conjugate (σ τ : F.CentricChain) : Prop := Nonempty (Conjugacy σ τ)

instance conjugacySetoid : Setoid F.CentricChain where
  r := Conjugate
  iseqv := ⟨fun σ => ⟨Conjugacy.refl σ⟩,
    fun ⟨c⟩ => ⟨c.symm⟩, fun ⟨c⟩ ⟨d⟩ => ⟨c.trans d⟩⟩

theorem conjugate_length_eq {σ τ : F.CentricChain} (h : Conjugate σ τ) :
    σ.length = τ.length := h.some.length_eq

theorem conjugate_iff_topIso (σ τ : F.CentricChain) :
    Conjugate σ τ ↔ ∃ h : σ.length = τ.length,
      ∃ e : σ.topRawObject ≅ τ.topRawObject,
        ∀ i : Fin (σ.length + 1),
          (fun x : σ.topSubgroup => (e.hom.val x).val) '' {x | x.val ∈ σ.subgroup i} =
            (τ.subgroup (Fin.cast (congrArg (fun n => n + 1) h) i) : Set S) := by
  constructor
  · rintro ⟨c⟩
    refine ⟨c.length_eq, c.topIso, fun i => ?_⟩
    have hi : c.indices i = Fin.cast (congrArg (fun n => n + 1) c.length_eq) i :=
      congrArg (fun e : Fin (σ.length + 1) ≃o Fin (τ.length + 1) => e i) c.indices_eq_cast
    exact (c.subgroup_image i).trans (congrArg (fun j => (τ.subgroup j : Set S)) hi)
  · rintro ⟨h, e, hm⟩
    exact ⟨Conjugacy.ofTopIso h e hm⟩

end Sharpness.FusionSystem.CentricChain
