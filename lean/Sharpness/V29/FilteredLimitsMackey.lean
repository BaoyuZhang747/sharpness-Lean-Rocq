import Sharpness.V29.FilteredLimits
import Sharpness.ArbitraryCoefficients
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
The directed system of all full Mackey subfunctors with finitely generated
values, its pointwise colimit, and Lemma 2.6(ii) through the filtered-colimit
comparison.  No Noetherian or saturation assumption is used.
-/
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.MackeyModule
open CategoryTheory CategoryTheory.Limits Opposite

variable {R C : Type u} [CommRing R] [Category.{u} C]
  {B : MackeyShape C} (M : MackeyModule.{u,u,u} R C B)

/-- All finitely generated-valued full Mackey subfunctors, ordered by
pointwise inclusion. -/
def FGSubfunctor := {N : M.Subfunctor // ∀ P, (N.obj P).FG}

instance : PartialOrder M.FGSubfunctor where
  le N K := ∀ P, N.val.obj P ≤ K.val.obj P
  le_refl N P := le_rfl
  le_trans N K L h₁ h₂ P := (h₁ P).trans (h₂ P)
  le_antisymm N K h₁ h₂ := by
    apply Subtype.ext
    have heq : N.val.obj = K.val.obj := funext fun P => le_antisymm (h₁ P) (h₂ P)
    obtain ⟨⟨objN, pullN, pushN⟩, fgN⟩ := N
    obtain ⟨⟨objK, pullK, pushK⟩, fgK⟩ := K
    dsimp only at heq
    cases heq
    rfl

/-- The zero full subfunctor supplies the empty case of the directed system. -/
def zeroFGSubfunctor : M.FGSubfunctor :=
  ⟨{ obj := fun _ => ⊥
     pull_closed := by
       intro P Q f x hx
       simp only [Submodule.mem_bot] at hx ⊢
       rw [hx, map_zero]
     push_closed := by
       intro P Q f x hx
       simp only [Submodule.mem_bot] at hx ⊢
       rw [hx, map_zero] }, fun _ => Submodule.fg_bot⟩

instance : Nonempty M.FGSubfunctor := ⟨M.zeroFGSubfunctor⟩

/-- The pointwise sum is still a full Mackey subfunctor and has finitely
generated values. -/
def sumFGSubfunctor (N K : M.FGSubfunctor) : M.FGSubfunctor :=
  ⟨{ obj := fun P => N.val.obj P ⊔ K.val.obj P
     pull_closed := by
       intro P Q f x hx
       obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
       rw [map_add]
       exact Submodule.mem_sup.mpr
         ⟨M.pull f y, N.val.pull_closed f hy, M.pull f z, K.val.pull_closed f hz, rfl⟩
     push_closed := by
       intro P Q f x hx
       obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
       rw [map_add]
       exact Submodule.mem_sup.mpr
         ⟨M.push f y, N.val.push_closed f hy, M.push f z, K.val.push_closed f hz, rfl⟩ },
    fun P => (N.property P).sup (K.property P)⟩

instance : IsDirectedOrder M.FGSubfunctor where
  directed N K := ⟨M.sumFGSubfunctor N K, fun _ => le_sup_left, fun _ => le_sup_right⟩

instance : IsFiltered M.FGSubfunctor := inferInstance

variable [Finite C] [∀ P Q : C, Finite (P ⟶ Q)]

set_option maxHeartbeats 1000000 in
/-- Lemma 2.6(i) puts every element in a member of this actual system. -/
theorem exists_mem_fgSubfunctor (P : C) (x : M.Value P) :
    ∃ N : M.FGSubfunctor, x ∈ N.val.obj P := by
  let X : Finset (Σ P : C, M.Value P) := {⟨P, x⟩}
  let N : M.Subfunctor := M.finiteGeneratedSubfunctor X
  have hfg : ∀ T, (N.obj T).FG := fun T => M.finiteGeneratedValue_fg X T
  exact ⟨⟨N, hfg⟩, M.mem_singleton_finiteGeneratedValue P x⟩

/-- The pointwise module diagram has the actual inclusion maps. -/
def fgValueDiagram (P : C) : M.FGSubfunctor ⥤ ModuleCat.{u} R where
  obj N := ModuleCat.of R (N.val.obj P)
  map f := ModuleCat.ofHom (Submodule.inclusion (leOfHom f P))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def fgValueCocone (P : C) : Cocone (M.fgValueDiagram P) where
  pt := ModuleCat.of R (M.Value P)
  ι :=
    { app N := ModuleCat.ofHom (N.val.obj P).subtype
      naturality _ _ _ := by ext x; rfl }

/-- The pointwise inclusions intertwine every restriction of the full Mackey
functor, before passage to any subcategory. -/
theorem fgValueCocone_pull (N : M.FGSubfunctor) {P Q : C} (f : P ⟶ Q)
    (x : (M.submodule N.val).Value Q) :
    (M.fgValueCocone P).ι.app N ((M.submodule N.val).pull f x) =
      M.pull f ((M.fgValueCocone Q).ι.app N x) := rfl

/-- The same inclusions intertwine every transfer, hence also the
conjugation maps of the full Mackey functor. -/
theorem fgValueCocone_push (N : M.FGSubfunctor) {P Q : C} (f : P ⟶ Q)
    (x : (M.submodule N.val).Value P) :
    (M.fgValueCocone Q).ι.app N ((M.submodule N.val).push f x) =
      M.push f ((M.fgValueCocone P).ι.app N x) := rfl

/-- Its pointwise colimit is precisely the original module value. -/
def fgValueIsColimit (P : C) : IsColimit (M.fgValueCocone P) := by
  apply isColimitOfReflects (forget (ModuleCat.{u} R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨N, hx⟩ := M.exists_mem_fgSubfunctor P x
    exact ⟨N, ⟨x, hx⟩, rfl⟩
  · intro N x y hxy
    exact ⟨N, 𝟙 N, congrArg (fun x => x) (Subtype.ext hxy)⟩

end Sharpness.MackeyModule

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  {R : Type u} [CommRing R]
  (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)

local instance : Finite F.CentricOrbit :=
  Finite.of_injective (fun P => P.obj) (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance (P Q : F.CentricOrbit) : Finite (P ⟶ Q) :=
  Finite.of_injective (fun f : P ⟶ Q => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

/-- The contravariant coefficients of the full Mackey subfunctors, restricted
only after construction to the centric orbit category. -/
def fgCentricDiagram : M.FGSubfunctor ⥤ CoefficientCategory R F.CentricOrbit where
  obj N := F.centricCoefficient (M.submodule N.val)
  map f :=
    { app P := ModuleCat.ofHom (Submodule.inclusion (leOfHom f P.unop.obj))
      naturality _ _ _ := by ext x; rfl }
  map_id _ := by ext P x; rfl
  map_comp _ _ := by ext P x; rfl

def fgCentricCocone : Cocone (F.fgCentricDiagram M) where
  pt := F.centricCoefficient M
  ι :=
    { app N := F.subCoefficientInclusion M N.val
      naturality _ _ _ := by ext P x; rfl }

/-- The coefficient colimit is pointwise and respects the actual restriction
maps; the inclusions also respect transfers since each index is full. -/
def fgCentricIsColimit : IsColimit (F.fgCentricCocone M) := by
  apply evaluationJointlyReflectsColimits
  intro P
  exact M.fgValueIsColimit P.unop.obj

/-- The direct-limit comparison specialised to the system of full Mackey
subfunctors. -/
def fgCentricHigherLimitIso (n : ℕ) :
    colimit (F.fgCentricDiagram M ⋙ higherLimitFunctor R F.CentricOrbit n) ≅
      higherLimit (F.centricCoefficient M) n :=
  V29.filteredColimitHigherLimitIso (F.fgCentricDiagram M) n ≪≫
    (higherLimitFunctor R F.CentricOrbit n).mapIso
      ((colimit.isColimit _).coconePointUniqueUpToIso (F.fgCentricIsColimit M))

@[reassoc]
theorem fgCentricHigherLimitIso_ι (n : ℕ) (N : M.FGSubfunctor) :
    colimit.ι (F.fgCentricDiagram M ⋙ higherLimitFunctor R F.CentricOrbit n) N ≫
        (F.fgCentricHigherLimitIso M n).hom =
      (higherLimitFunctor R F.CentricOrbit n).map (F.subCoefficientInclusion M N.val) := by
  simp only [fgCentricHigherLimitIso, Iso.trans_hom,
    V29.filteredColimitHigherLimitIso_ι_assoc, Functor.mapIso_hom, ← Functor.map_comp,
    colimit.comp_coconePointUniqueUpToIso_hom]
  rfl

/-- Manuscript Lemma 2.6(ii), including degree zero, obtained from the actual
filtered direct limit and its canonical higher-limit comparison. -/
theorem higherLimit_isZero_of_fg_subfunctors_v29 (n : ℕ)
    (h : ∀ N : M.Subfunctor, (∀ P, (N.obj P).FG) →
      IsZero (higherLimit (F.centricCoefficient (M.submodule N)) n)) :
    IsZero (higherLimit (F.centricCoefficient M) n) := by
  let H := higherLimitFunctor R F.CentricOrbit n
  have hz : IsZero (colimit (F.fgCentricDiagram M ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    exact (h N.val N.property).eq_of_src _ _
  exact IsZero.of_iso hz (F.fgCentricHigherLimitIso M n).symm

end Sharpness.FusionSystem
