import Sharpness.Unconditional.GroupCohomologyMackeyDecompositionIso
import Sharpness.Unconditional.GroupCohomologyCosetTower
import Sharpness.Unconditional.GroupCohomologyTransferConstruction

/-! The actual finite coinduction trace regroups over double cosets.
The underlying right-coset bijection is constructed from the real intersection
subgroups and does not assume a partition or a Mackey identity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
open CategoryTheory QuotientGroup
open scoped BigOperators

variable {G : Type v} [Group G] (H K : Subgroup G)

/-- The double coset containing an actual right coset of H. -/
def rightCosetLabel : Quotient (rightRel H) → DoubleCoset.Quotient (H : Set G) K :=
  Quotient.lift (DoubleCoset.mk H K) (fun a b hab =>
    (DoubleCoset.eq H K a b).mpr
      ⟨b * a⁻¹, (rightRel_apply.mp hab), 1, K.one_mem, by simp⟩)

/-- A right coset in the intersection subgroup maps to its actual H-coset. -/
def rightCosetPiece (d : DoubleCoset.Quotient (H : Set G) K) :
    Quotient (rightRel (intersection H K d.out)) → Quotient (rightRel H) :=
  Quotient.map (fun k : K => d.out * (k : G)) (by
    intro a b hab
    apply rightRel_apply.mpr
    have hp : b * a⁻¹ ∈ intersection H K d.out := rightRel_apply.mp hab
    change d.out * ((b : G) * (a : G)⁻¹) * d.out⁻¹ ∈ H at hp
    simpa only [mul_inv_rev, mul_assoc] using hp)

theorem rightCosetPiece_injective (d : DoubleCoset.Quotient (H : Set G) K) :
    Function.Injective (rightCosetPiece H K d) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun a b hab => ?_
  apply Quotient.sound
  apply rightRel_apply.mpr
  change d.out * ((b : G) * (a : G)⁻¹) * d.out⁻¹ ∈ H
  have hp := rightRel_apply.mp (Quotient.exact hab)
  simpa only [mul_inv_rev, mul_assoc] using hp

@[simp] theorem rightCosetLabel_piece (d : DoubleCoset.Quotient (H : Set G) K)
    (a : Quotient (rightRel (intersection H K d.out))) :
    rightCosetLabel H K (rightCosetPiece H K d a) = d := by
  refine Quotient.inductionOn a fun a => ?_
  change DoubleCoset.mk H K (d.out * (a : G)) = d
  calc
    DoubleCoset.mk H K (d.out * (a : G)) = DoubleCoset.mk H K d.out :=
      ((DoubleCoset.eq H K d.out (d.out * (a : G))).mpr
        ⟨1, H.one_mem, a, a.2, by simp⟩).symm
    _ = d := DoubleCoset.out_eq' H K d

def rightCosetAssembly :
    (Σ d : DoubleCoset.Quotient (H : Set G) K,
      Quotient (rightRel (intersection H K d.out))) → Quotient (rightRel H) :=
  fun a => rightCosetPiece H K a.1 a.2

theorem rightCosetAssembly_bijective : Function.Bijective (rightCosetAssembly H K) := by
  constructor
  · rintro ⟨d, a⟩ ⟨e, b⟩ hab
    have hd : d = e := by
      simpa only [rightCosetAssembly, rightCosetLabel_piece] using
        congrArg (rightCosetLabel H K) hab
    subst e
    have ha : a = b := rightCosetPiece_injective H K d hab
    cases ha
    rfl
  · intro a
    refine Quotient.inductionOn a fun g => ?_
    obtain ⟨h, k, hg⟩ := exists_coordinates H K g
    let d := DoubleCoset.mk H K g
    refine ⟨⟨d, Quotient.mk'' k⟩, ?_⟩
    apply Quotient.sound
    apply rightRel_apply.mpr
    change g * (d.out * (k : G))⁻¹ ∈ H
    have he : g * (d.out * (k : G))⁻¹ = (h : G) := by
      calc
        g * (d.out * (k : G))⁻¹ =
            ((h : G) * d.out * k) * (d.out * (k : G))⁻¹ :=
          congrArg (fun z => z * (d.out * (k : G))⁻¹) hg
        _ = (h : G) := by group
    rw [he]
    exact h.2

/-- The disjoint decomposition H\G = coproduct over H\G/K of L_d\K. -/
def rightCosetDoubleEquiv :
    (Σ d : DoubleCoset.Quotient (H : Set G) K,
      Quotient (rightRel (intersection H K d.out))) ≃ Quotient (rightRel H) :=
  Equiv.ofBijective (rightCosetAssembly H K) (rightCosetAssembly_bijective H K)

theorem rightCosetDoubleEquiv_apply (d : DoubleCoset.Quotient (H : Set G) K)
    (a : Quotient (rightRel (intersection H K d.out))) :
    rightCosetDoubleEquiv H K ⟨d, a⟩ =
      (Quotient.mk'' (d.out * (a.out : G)) : Quotient (rightRel H)) := by
  change rightCosetPiece H K d a = _
  conv_lhs => rw [← Quotient.out_eq' a]
  rfl

/-- Actual coset-sum regrouping for every left-H-invariant function. -/
theorem rightCosetDouble_sum {B : Type w} [AddCommMonoid B]
    [Fintype (Quotient (rightRel H))]
    [Fintype (DoubleCoset.Quotient (H : Set G) K)]
    [∀ d : DoubleCoset.Quotient (H : Set G) K,
      Fintype (Quotient (rightRel (intersection H K d.out)))]
    (f : G → B) (hf : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    (∑ a : Quotient (rightRel H), f a.out) =
      ∑ d : DoubleCoset.Quotient (H : Set G) K,
        ∑ a : Quotient (rightRel (intersection H K d.out)), f (d.out * (a.out : G)) := by
  classical
  rw [← (rightCosetDoubleEquiv H K).sum_comp (fun a => f a.out), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply rightCosetInvariant_eq f hf
  exact (Quotient.out_eq' (rightCosetDoubleEquiv H K ⟨d, a⟩)).trans
    (rightCosetDoubleEquiv_apply H K d a)

variable {R : Type u} {A : Type w} [CommRing R] [AddCommGroup A] [Module R A]

/-- Projection from the actual product representation to a native coinduced piece. -/
def componentProjection (d : DoubleCoset.Quotient (H : Set G) K) :
    Rep.of (productRepresentation (R := R) (A := A) H K) ⟶
      Rep.coind (intersection H K d.out).subtype
        (Rep.trivial R (intersection H K d.out) A) :=
  Rep.ofHom ⟨LinearMap.proj d, fun _ => rfl⟩

def componentHom (d : DoubleCoset.Quotient (H : Set G) K) :
    Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)) ⟶
      Rep.coind (intersection H K d.out).subtype
        (Rep.trivial R (intersection H K d.out) A) :=
  (coinductionMackeyIso H K).hom ≫ componentProjection H K d

@[simp] theorem componentHom_apply (d : DoubleCoset.Quotient (H : Set G) K)
    (f : Source (R := R) (A := A) H) (k : K) :
    ((componentHom H K d).hom f).1 k = f.1 (d.out * k) := rfl

end Sharpness.OrdinaryCohomology.MackeyDecomposition

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
open CategoryTheory QuotientGroup
open scoped BigOperators

variable {R G A : Type u} [CommRing R] [Group G] [Finite G]
    [AddCommGroup A] [Module R A] (H K : Subgroup G)

local instance doubleCosetFintype : Fintype (DoubleCoset.Quotient (H : Set G) K) := by
  unfold DoubleCoset.Quotient
  exact Fintype.ofFinite _

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The original native trace is the sum of the original native traces
of the double-coset components. -/
theorem coinductionTrace_doubleCoset_apply (f : Source (R := R) (A := A) H) :
    (coinductionTrace H (Rep.trivial R G A)).hom f =
      ∑ d : DoubleCoset.Quotient (H : Set G) K,
        (coinductionTrace (intersection H K d.out) (Rep.trivial R K A)).hom
          ((componentHom H K d).hom f) := by
  rw [coinductionTrace_trivial_apply]
  rw [rightCosetDouble_sum H K f.1 (fun h g => f.2 h g)]
  apply Finset.sum_congr rfl
  intro d _
  rw [coinductionTrace_trivial_apply]
  rfl

/-- Equality of actual K-representation morphisms, before applying cohomology. -/
theorem coinductionTrace_doubleCoset :
    (Rep.resFunctor K.subtype).map (coinductionTrace H (Rep.trivial R G A)) =
      ∑ d : DoubleCoset.Quotient (H : Set G) K,
        componentHom H K d ≫
          coinductionTrace (intersection H K d.out) (Rep.trivial R K A) := by
  ext f
  change (coinductionTrace H (Rep.trivial R G A)).hom f = _
  simp only [Rep.sum_hom, Representation.IntertwiningMap.sum_apply,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply,
    Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_apply]
  exact coinductionTrace_doubleCoset_apply H K f

end Sharpness.OrdinaryCohomology.MackeyDecomposition
