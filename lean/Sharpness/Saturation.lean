import Sharpness.NormalizerAction

/-! Concrete saturation hypotheses. These are definitions of the objects
to which the paper and cited theorems apply, not assumptions of sharpness. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def automorphismSubgroup (P : Subgroup S) : Subgroup (MulAut P) where
  carrier := {a | F.IsHom a.toMonoidHom}
  one_mem' := F.id_mem P
  mul_mem' ha hb := F.comp_mem _ _ hb ha
  inv_mem' {a} ha := F.inverse_mem a ha

def innerSylowSubgroup (_F : FusionSystem S) (P : Subgroup S) : Subgroup (MulAut P) :=
  P.normalizerMonoidHom.range

theorem innerSylowSubgroup_le (P : Subgroup S) :
    F.innerSylowSubgroup P ≤ F.automorphismSubgroup P := by
  rintro _ ⟨n, rfl⟩
  exact F.normalizerAut_allowed P n

def FullyNormalized (P : Subgroup S) : Prop :=
  ∀ (Q : Subgroup S) (e : P ≃* Q), F.IsHom e.toMonoidHom →
    Nat.card (Subgroup.normalizer (Q : Set S)) ≤ Nat.card (Subgroup.normalizer (P : Set S))

def FullyCentralized (P : Subgroup S) : Prop :=
  ∀ (Q : Subgroup S) (e : P ≃* Q), F.IsHom e.toMonoidHom →
    Nat.card (Subgroup.centralizer (Q : Set S)) ≤ Nat.card (Subgroup.centralizer (P : Set S))

/-- The usual extension domain N_e, written as a set to avoid choosing a
second copy of its subgroup structure. The axiom below specifies the
subgroup by exactly this carrier. -/
def extensionDomain (_F : FusionSystem S) {P Q : Subgroup S} (e : P ≃* Q) : Set S :=
  {s | ∃ n : Subgroup.normalizer (P : Set S), n.val = s ∧
    ∃ t : Subgroup.normalizer (Q : Set S),
      ∀ x : P, e (P.normalizerMonoidHom n x) = Q.normalizerMonoidHom t (e x)}

/-- AKO saturation axioms. For a p-group S, Aut_S(P) is already a p-group;
the prime-to-p relative index is exactly its Sylow condition in Aut_F(P).
The extension axiom is stated for the isomorphism onto the morphism image. -/
structure Saturated (p : ℕ) : Prop where
  fully_normalized : ∀ P, F.FullyNormalized P → F.FullyCentralized P ∧
    ¬ p ∣ (F.innerSylowSubgroup P).relIndex (F.automorphismSubgroup P)
  extension : ∀ {P Q : Subgroup S} (e : P ≃* Q), F.IsHom e.toMonoidHom →
    F.FullyCentralized Q → ∃ (N : Subgroup S) (hPN : P ≤ N),
      (N : Set S) = F.extensionDomain e ∧
      ∃ f : N →* (⊤ : Subgroup S), F.IsHom f ∧
        ∀ x : P, (f ⟨x.val, hPN x.property⟩).val = (e x).val

/-- The hypotheses under which the literature inputs are applicable. -/
structure LiteratureHypotheses (p : ℕ) (k : Type u) [Field k] : Prop where
  prime : p.Prime
  group_is_p : IsPGroup p S
  characteristic : CharP k p
  saturated : F.Saturated p

end Sharpness.FusionSystem
