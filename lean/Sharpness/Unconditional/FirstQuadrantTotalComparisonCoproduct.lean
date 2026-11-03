import Sharpness.CoproductChainsMaps
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Exact coproducts for the column maps used in first-quadrant total comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- Quasi-isomorphisms of short complexes in a functor category may be checked objectwise. -/
theorem shortComplex_quasiIso_of_app {J : Type u} [Category.{u} J]
    {S T : ShortComplex (J ⥤ ModuleCat.{u} R)} (f : S ⟶ T)
    (hf : ∀ j, ShortComplex.QuasiIso (((evaluation J (ModuleCat R)).obj j).mapShortComplex.map f)) :
    ShortComplex.QuasiIso f := by
  rw [ShortComplex.quasiIso_iff, NatTrans.isIso_iff_isIso_app]
  intro j
  let F := (evaluation J (ModuleCat.{u} R)).obj j
  letI := hf j
  have h : F.map (ShortComplex.homologyMap f) =
      (S.mapHomologyIso F).inv ≫
        ShortComplex.homologyMap (F.mapShortComplex.map f) ≫ (T.mapHomologyIso F).hom := by
    rw [ShortComplex.mapHomologyIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  change IsIso (F.map (ShortComplex.homologyMap f))
  rw [h]
  infer_instance

/-- Exact coproducts preserve objectwise quasi-isomorphisms of short complexes. -/
theorem shortComplex_coproduct_quasiIso {ι : Type u}
    {S T : ShortComplex (Discrete ι ⥤ ModuleCat.{u} R)} (f : S ⟶ T)
    (hf : ∀ i, ShortComplex.QuasiIso
      (((evaluation (Discrete ι) (ModuleCat R)).obj i).mapShortComplex.map f)) :
    ShortComplex.QuasiIso ((colim (J := Discrete ι) (C := ModuleCat R)).mapShortComplex.map f) := by
  letI := shortComplex_quasiIso_of_app f hf
  infer_instance

/-- The existing explicit direct sum carries its categorical coproduct cocone. -/
def directSumCocone {ι : Type u} (M : ι → ModuleCat.{u} R) :
    Cocone (Discrete.functor M) where
  pt := moduleDirectSum M
  ι := Discrete.natTrans (fun i => moduleDirectSumInclusion M i.as)

def directSumIsColimit {ι : Type u} (M : ι → ModuleCat.{u} R) :
    IsColimit (directSumCocone M) where
  desc s := moduleDirectSumDesc M (fun i => s.ι.app ⟨i⟩)
  fac s j := moduleDirectSumInclusion_desc M (fun i => s.ι.app ⟨i⟩) j.as
  uniq s m hm := by
    apply moduleDirectSum_hom_ext
    intro i
    exact (hm ⟨i⟩).trans (moduleDirectSumInclusion_desc M (fun j => s.ι.app ⟨j⟩) i).symm

def directSumColimitIso {ι : Type u} (M : ι → ModuleCat.{u} R) :
    moduleDirectSum M ≅ colimit (Discrete.functor M) :=
  (directSumIsColimit M).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
theorem directSumColimitIso_inclusion {ι : Type u} (M : ι → ModuleCat.{u} R) (i : ι) :
    moduleDirectSumInclusion M i ≫ (directSumColimitIso M).hom =
      colimit.ι (Discrete.functor M) ⟨i⟩ :=
  (directSumIsColimit M).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨i⟩

/-- Regard a family of complexes as one complex in a discrete functor category. -/
def familyComplex {ι : Type u} (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (Discrete ι ⥤ ModuleCat.{u} R) ℕ where
  X n := Discrete.functor (fun i => (K i).X n)
  d n m := Discrete.natTrans (fun i => (K i.as).d n m)
  shape n m h := by apply NatTrans.ext; funext i; exact (K i.as).shape n m h
  d_comp_d' i j k _ _ := by apply NatTrans.ext; funext a; exact (K a.as).d_comp_d i j k

def familyComplexMap {ι : Type u} {K L : ι → ChainComplex (ModuleCat.{u} R) ℕ}
    (f : ∀ i, K i ⟶ L i) : familyComplex K ⟶ familyComplex L where
  f n := Discrete.natTrans (fun i => (f i.as).f n)
  comm' n m _ := by apply NatTrans.ext; funext i; exact (f i.as).comm n m

theorem familyComplexMap_quasiIso {ι : Type u}
    {K L : ι → ChainComplex (ModuleCat.{u} R) ℕ} (f : ∀ i, K i ⟶ L i)
    [∀ i, QuasiIso (f i)] : QuasiIso (familyComplexMap f) := by
  constructor
  intro n
  rw [quasiIsoAt_iff]
  apply shortComplex_quasiIso_of_app
  intro i
  exact (quasiIsoAt_iff (f i.as) n).mp inferInstance

abbrev colimitFamilyComplex {ι : Type u} (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((colim (J := Discrete ι) (C := ModuleCat R)).mapHomologicalComplex _).obj (familyComplex K)

def coproductChainsColimitIso {ι : Type u} (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) :
    coproductChains K ≅ colimitFamilyComplex K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => directSumColimitIso (fun i => (K i).X n)) (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      apply moduleDirectSum_hom_ext
      intro a
      simp only [coproductChains, ChainComplex.of_d]
      change moduleDirectSumInclusion (fun i => (K i).X (j+1)) a ≫
          ((directSumColimitIso (fun i => (K i).X (j+1))).hom ≫
            colim.map (Discrete.natTrans
              (F := Discrete.functor (fun i => (K i).X (j+1)))
              (G := Discrete.functor (fun i => (K i).X j))
              (fun i : Discrete ι => (K i.as).d (j+1) j))) =
        moduleDirectSumInclusion (fun i => (K i).X (j+1)) a ≫
          (coproductChainsDifferential K j ≫ (directSumColimitIso (fun i => (K i).X j)).hom)
      rw [← Category.assoc, directSumColimitIso_inclusion,
        ← Category.assoc, coproductChainsDifferential_inclusion,
        Category.assoc, directSumColimitIso_inclusion]
      exact ι_colimMap (Discrete.natTrans
        (F := Discrete.functor (fun i => (K i).X (j+1)))
        (G := Discrete.functor (fun i => (K i).X j))
        (fun i : Discrete ι => (K i.as).d (j+1) j)) ⟨a⟩)

theorem coproductChainsColimitIso_naturality {ι : Type u}
    {K L : ι → ChainComplex (ModuleCat.{u} R) ℕ} (f : ∀ i, K i ⟶ L i) :
    coproductChainsMap K L id f ≫ (coproductChainsColimitIso L).hom =
      (coproductChainsColimitIso K).hom ≫
        ((colim (J := Discrete ι) (C := ModuleCat R)).mapHomologicalComplex _).map
          (familyComplexMap f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply moduleDirectSum_hom_ext
  intro i
  have h : moduleDirectSumInclusion (fun i => (K i).X n) i ≫
        (coproductChainsMap K L id f).f n =
      (f i).f n ≫ moduleDirectSumInclusion (fun i => (L i).X n) i :=
    congrArg (fun a => a.f n) (coproductChainsMap_inclusion K L id f i)
  change moduleDirectSumInclusion (fun i => (K i).X n) i ≫
      ((coproductChainsMap K L id f).f n ≫ (directSumColimitIso (fun i => (L i).X n)).hom) =
    moduleDirectSumInclusion (fun i => (K i).X n) i ≫
      ((directSumColimitIso (fun i => (K i).X n)).hom ≫
        colim.map (Discrete.natTrans
          (F := Discrete.functor (fun i => (K i).X n))
          (G := Discrete.functor (fun i => (L i).X n))
          (fun i : Discrete ι => (f i.as).f n)))
  rw [← Category.assoc, h, Category.assoc, directSumColimitIso_inclusion,
    ← Category.assoc, directSumColimitIso_inclusion]
  exact (ι_colimMap (Discrete.natTrans
    (F := Discrete.functor (fun i => (K i).X n))
    (G := Discrete.functor (fun i => (L i).X n))
    (fun i : Discrete ι => (f i.as).f n)) ⟨i⟩).symm

/-- Arbitrary direct sums of native chain quasi-isomorphisms are quasi-isomorphisms. -/
theorem coproductChainsMap_quasiIso {ι : Type u}
    {K L : ι → ChainComplex (ModuleCat.{u} R) ℕ} (f : ∀ i, K i ⟶ L i)
    [∀ i, QuasiIso (f i)] : QuasiIso (coproductChainsMap K L id f) := by
  letI := familyComplexMap_quasiIso f
  haveI : QuasiIso (coproductChainsMap K L id f ≫ (coproductChainsColimitIso L).hom) := by
    rw [coproductChainsColimitIso_naturality]
    infer_instance
  exact quasiIso_of_comp_right
    (coproductChainsMap K L id f) (coproductChainsColimitIso L).hom

end Sharpness.TotalComparison
