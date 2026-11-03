import Sharpness.Unconditional.AtomicGroupOrbit
import Mathlib.GroupTheory.Sylow
import Mathlib.CategoryTheory.Equivalence

/-! The ordinary p-orbit category can be computed using just subgroups
of a chosen Sylow p-subgroup. Morphisms remain the ambient-group cosets. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.AtomicGroupOrbit
open CategoryTheory
variable {p : ℕ} {G : Type u} [Group G]

def conjugateObject (g : G) (P : Object p G) : Object p G :=
  ⟨P.subgroup.map (MulAut.conj g).toMonoidHom,
    P.isPGroup.map (MulAut.conj g).toMonoidHom⟩

/-- Conjugation gives an isomorphism in the actual coset orbit category. -/
def conjugateIso (g : G) (P : Object p G) :
    toOrbit.obj P ≅ toOrbit.obj (conjugateObject g P) where
  hom := toOrbit.map ⟨g⁻¹, by
    intro x hx
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩⟩
  inv := toOrbit.map ⟨g, by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy⟩
  hom_inv_id := by
    rw [← toOrbit.map_comp, ← toOrbit.map_id]
    congr 1
    apply Subtype.ext
    exact inv_mul_cancel g
  inv_hom_id := by
    rw [← toOrbit.map_comp, ← toOrbit.map_id]
    congr 1
    apply Subtype.ext
    exact mul_inv_cancel g

/-- The full p-orbit subcategory consisting of subgroups of `T`. -/
abbrev Below (T : Subgroup G) := ObjectProperty.FullSubcategory
  (fun P : Orbit (p := p) (G := G) => P.as.subgroup ≤ T)

def belowInclusion (T : Subgroup G) : Below (p := p) T ⥤ Orbit (p := p) (G := G) :=
  ObjectProperty.ι _

instance (T : Subgroup G) : (belowInclusion (p := p) T).Full :=
  inferInstanceAs (ObjectProperty.ι _).Full

instance (T : Subgroup G) : (belowInclusion (p := p) T).Faithful :=
  inferInstanceAs (ObjectProperty.ι _).Faithful

variable [Fact p.Prime] [Finite (Sylow p G)]

theorem exists_conjugate_le_sylow (T : Sylow p G) (P : Object p G) :
    ∃ g : G, (conjugateObject g P).subgroup ≤ T := by
  obtain ⟨U, hPU⟩ := P.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U T
  refine ⟨g, ?_⟩
  rw [← hg]
  exact Subgroup.map_mono hPU

instance belowInclusion_essSurj (T : Sylow p G) :
    (belowInclusion (p := p) (T : Subgroup G)).EssSurj where
  mem_essImage P := by
    obtain ⟨g, hg⟩ := exists_conjugate_le_sylow T P.as
    exact ⟨⟨toOrbit.obj (conjugateObject g P.as), hg⟩, ⟨(conjugateIso g P.as).symm⟩⟩

instance belowInclusion_isEquivalence (T : Sylow p G) :
    (belowInclusion (p := p) (T : Subgroup G)).IsEquivalence where

/-- Restriction to a Sylow subgroup is an equivalence of orbit categories. -/
def sylowEquivalence (T : Sylow p G) :
    Below (p := p) (T : Subgroup G) ≌ Orbit (p := p) (G := G) :=
  (belowInclusion (p := p) (T : Subgroup G)).asEquivalence

end Sharpness.AtomicGroupOrbit
