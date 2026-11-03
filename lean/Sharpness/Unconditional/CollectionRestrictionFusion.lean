import Sharpness.Unconditional.CollectionRestrictionAtomic
import Sharpness.CollectionRestriction
import Sharpness.FusionMinimal
import Sharpness.HigherLimitsEquivalence

/-! Apply the proved atomic filtration to the actual centric fusion orbit
category. Conjugacy invariance is explicit: the historical collection
structure recorded only closure under inclusions. The quotient collection
satisfies this additional property by its proved transport theorem. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime]

namespace ComparisonCollection
variable {F p} (C : F.ComparisonCollection p)

def inCentric : ObjectProperty F.CentricOrbit := fun P => C.member P.obj.as.subgroup

/-- Flattening the two full-subcategory constructions preserves all maps. -/
def centricEquivalence : C.inCentric.FullSubcategory ≌ C.Orbit where
  functor :=
    { obj := fun P => ⟨P.obj.obj, P.property⟩
      map := fun f => ObjectProperty.homMk f.hom.hom }
  inverse :=
    { obj := fun P => ⟨⟨P.obj, C.centric _ P.property⟩, P.property⟩
      map := fun f => ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  unitIso := NatIso.ofComponents (fun P => Iso.refl P)
  counitIso := NatIso.ofComponents (fun P => Iso.refl P)

omit [Finite S] [Fact p.Prime] in
theorem inCentric_upward
    (conjugate : ∀ {P Q : F.Orbit}, (P ≅ Q) →
      C.member P.as.subgroup → C.member Q.as.subgroup)
    {P Q : F.CentricOrbit} (f : P ⟶ Q) (hP : C.inCentric P) : C.inCentric Q :=
  C.overgroup (conjugate (F.arrowImageIso f.hom) hP) (F.arrowImage_le f.hom)

end ComparisonCollection

variable (R : Type u) [CommRing R]

/-- Atomic vanishing at nonradical objects implies the full collection
restriction criterion for higher-limit vanishing. -/
theorem collectionRestriction_isZero_iff
    (atomic : ∀ Q : F.CentricOrbit, ¬ F.IsRadical p Q.obj.as.subgroup →
      ∀ A : CoefficientCategory R F.CentricOrbit,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (C : F.ComparisonCollection p)
    (conjugate : ∀ {P Q : F.Orbit}, (P ≅ Q) →
      C.member P.as.subgroup → C.member Q.as.subgroup)
    (M : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    IsZero (higherLimit M n) ↔ IsZero (higherLimit (C.toCentric.op ⋙ M) n) := by
  classical
  letI : Finite F.CentricOrbit := Finite.of_injective (fun P => P.obj)
    (fun P Q h => ObjectProperty.FullSubcategory.ext h)
  letI := Fintype.ofFinite F.CentricOrbit
  have hc := ZeroExtension.isZero_higherLimit_iff_restriction R
    (fun P : F.CentricOrbit => F.orbitOrder P.obj)
    (fun {P Q : F.CentricOrbit} (f : P ⟶ Q) => F.orbitOrder_mono f.hom)
    (fun {P Q : F.CentricOrbit} (f : P ⟶ Q) h => (ObjectProperty.isIso_hom_iff f).mp
      (F.orbit_isIso_of_equal_order f.hom h))
    C.inCentric (C.inCentric_upward conjugate)
    (fun Q hQ => atomic Q (fun hrad =>
      hQ (C.contains_centric_radical _ Q.property hrad))) M n
  let e := higherLimitEquivalenceIso R C.centricEquivalence (C.toCentric.op ⋙ M) n
  exact hc.trans ⟨fun h => IsZero.of_iso h e, fun h => IsZero.of_iso h e.symm⟩

theorem collectionRestriction_acyclic_iff
    (atomic : ∀ Q : F.CentricOrbit, ¬ F.IsRadical p Q.obj.as.subgroup →
      ∀ A : CoefficientCategory R F.CentricOrbit,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (C : F.ComparisonCollection p)
    (conjugate : ∀ {P Q : F.Orbit}, (P ≅ Q) →
      C.member P.as.subgroup → C.member Q.as.subgroup)
    (M : CoefficientCategory R F.CentricOrbit) :
    Acyclic M ↔ Acyclic (C.toCentric.op ⋙ M) := by
  constructor
  · intro h n hn
    exact (F.collectionRestriction_isZero_iff p R atomic C conjugate M n).mp (h n hn)
  · intro h n hn
    exact (F.collectionRestriction_isZero_iff p R atomic C conjugate M n).mpr (h n hn)

variable (hS : IsPGroup p S) (sat : F.Saturated p)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem quotientCollectionRestriction_acyclic_iff
    (atomic : ∀ Q : F.CentricOrbit, ¬ F.IsRadical p Q.obj.as.subgroup →
      ∀ A : CoefficientCategory R F.CentricOrbit,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (M : CoefficientCategory R F.CentricOrbit) :
    Acyclic M ↔ Acyclic
      ((F.quotientComparisonCollection p hS sat hZ I).toCentric.op ⋙ M) :=
  F.collectionRestriction_acyclic_iff p R atomic
    (F.quotientComparisonCollection p hS sat hZ I)
    (fun e hP => F.quotientCollection_conjugate hZ p hS sat I hP
      (F.groupEquivOfOrbitIso e) (F.groupEquivOfOrbitIso_allowed e)) M

end Sharpness.FusionSystem
