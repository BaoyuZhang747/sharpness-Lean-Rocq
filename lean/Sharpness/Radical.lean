import Sharpness.FusionQuotientKernel

/-! Radical subgroups, stated on the actual outer automorphism group
Aut_{O(F)}(P). The no-normal-p-subgroup condition is invariant under actual
fusion isomorphisms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

def HasTrivialNormalPSubgroups (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → IsPGroup p N → N = ⊥

theorem HasTrivialNormalPSubgroups.of_mulEquiv {p : ℕ}
    {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    (hG : HasTrivialNormalPSubgroups p G) : HasTrivialNormalPSubgroups p H := by
  intro N hN hp
  letI : N.Normal := hN
  have heq := hG (N.comap e.toMonoidHom) inferInstance
    (hp.comap_of_injective e.toMonoidHom e.injective)
  apply le_antisymm _ bot_le
  intro x hx
  have hm : e.symm x ∈ N.comap e.toMonoidHom := by
    change e (e.symm x) ∈ N
    simpa only [e.apply_symm_apply] using hx
  rw [heq] at hm
  have h1 : e.symm x = 1 := hm
  have h2 := congrArg e h1
  change x = 1
  simpa only [e.apply_symm_apply, map_one] using h2

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def IsRadical (p : ℕ) (P : Subgroup S) : Prop :=
  HasTrivialNormalPSubgroups p (Aut (F.toOrbit.obj ⟨P⟩))

theorem radical_of_orbitIso {p : ℕ} {P Q : F.Orbit} (e : P ≅ Q)
    (hP : F.IsRadical p P.as.subgroup) : F.IsRadical p Q.as.subgroup :=
  HasTrivialNormalPSubgroups.of_mulEquiv (Aut.autMulEquivOfIso e) hP

end FusionSystem
end Sharpness
