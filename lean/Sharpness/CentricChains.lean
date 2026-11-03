import Sharpness.CentricLinkingSystem
import Mathlib.Order.Fin.Basic

/-! Actual nonempty strict chains of F-centric subgroups, together with
their order-embedded subchains and their actual linking objects. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

structure CentricChain where
  length : ℕ
  entry : Fin (length + 1) → F.CentricSubgroup
  strict : StrictMono (fun i => (entry i).val)

namespace CentricChain
variable {F} (σ : F.CentricChain)

def subgroup (i : Fin (σ.length + 1)) : Subgroup S := (σ.entry i).val

theorem centric (i : Fin (σ.length + 1)) : F.IsCentric (σ.subgroup i) :=
  (σ.entry i).property

theorem subgroup_mono {i j : Fin (σ.length + 1)} (h : i ≤ j) :
    σ.subgroup i ≤ σ.subgroup j := σ.strict.monotone h

theorem subgroup_strict {i j : Fin (σ.length + 1)} (h : i < j) :
    σ.subgroup i < σ.subgroup j := σ.strict h

def linkingObject (L : F.CentricLinkingSystem) (i : Fin (σ.length + 1)) : L.Object :=
  ⟨σ.entry i⟩

def subchain (m : ℕ) (e : Fin (m + 1) ↪o Fin (σ.length + 1)) : F.CentricChain where
  length := m
  entry i := σ.entry (e i)
  strict := σ.strict.comp e.strictMono

@[simp] theorem subchain_subgroup (m : ℕ) (e : Fin (m + 1) ↪o Fin (σ.length + 1))
    (i : Fin (m + 1)) : (σ.subchain m e).subgroup i = σ.subgroup (e i) := rfl

@[simp] theorem subchain_linkingObject (L : F.CentricLinkingSystem) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) (i : Fin (m + 1)) :
    (σ.subchain m e).linkingObject L i = σ.linkingObject L (e i) := rfl

theorem subchain_refl : σ.subchain σ.length (OrderIso.refl _).toOrderEmbedding = σ := by
  cases σ
  rfl

theorem subchain_subchain (m k : ℕ) (e : Fin (m + 1) ↪o Fin (σ.length + 1))
    (d : Fin (k + 1) ↪o Fin (m + 1)) :
    (σ.subchain m e).subchain k d = σ.subchain k (d.trans e) := rfl

end CentricChain
end Sharpness.FusionSystem
