(** The actual category cochain-replacement total, its functorial maps and
    the literal cochain projections to every value of the original diagram. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalDiagramInjectives CategoryInjectiveResolutionComparison
  CategoryFiberVanishing BarComplex BarNaturality BarResolutionComparison.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps CategoryCochainReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarComplex DiazParkBarNaturality
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps.
Local Open Scope ring_scope.

Section ReplacementTotal.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition cochain_replacement_total : cochain_complex R :=
  total_complex (cochain_replacement_bicomplex K).

Definition replacement_projection_at (c : C) n :
    {linear cochain_term cochain_replacement_total n -> fobj (diagram_term K n) c} :=
  (@DiazParkBarResolutionComparison.bar_evaluation R C (diagram_term K n) 0%N c tt \o
    (@zero_column_at R (cochain_replacement_bicomplex K) n) : {linear _ -> _}).

Arguments replacement_projection_at c {n}.

Lemma replacement_projection_d (c : C) n (a : cochain_term cochain_replacement_total n) :
    module_hom_fun (component (diagram_d K n) c) (replacement_projection_at c a) =
    replacement_projection_at c (cochain_d cochain_replacement_total n a).
Proof.
have h := @zero_column_d R (cochain_replacement_bicomplex K) n a.
exact (f_equal (fun v => v c tt) h).
Qed.

Definition replacement_projection (c : C) :
    cochain_map cochain_replacement_total (diagram_evaluation_complex K c) :=
  @CochainMap R cochain_replacement_total (diagram_evaluation_complex K c)
    (fun n => (@replacement_projection_at c n : {linear _ -> _}))
    (replacement_projection_d c).

Theorem replacement_projection_formula (c : C) n (a : cochain_term cochain_replacement_total n) :
    cochain_map_at (replacement_projection c) n a = a 0%N n Logic.eq_refl c tt.
Proof. reflexivity. Qed.
End ReplacementTotal.

Section Maps.
Variable R : pzRingType.
Variable C : category.
Variables K L : @diagram_complex R (opposite C).
Variable f : diagram_cochain_map K L.

Definition cochain_replacement_total_map :
    cochain_map (cochain_replacement_total K) (cochain_replacement_total L) :=
  total_cochain_map (cochain_replacement_map f).

Theorem replacement_projection_naturality (c : C) n (a : cochain_term (cochain_replacement_total K) n) :
    replacement_projection_at L c n (cochain_map_at cochain_replacement_total_map n a) =
    module_hom_fun (component (diagram_cochain_map_at f n) c) (replacement_projection_at K c n a).
Proof. reflexivity. Qed.
End Maps.
