(** Actual inverse bicomplex maps between dual replacement chains and category cochains. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear.
From DiazParkV16b Require Import SimplicialSetYoneda BisimplicialChains SimplicialReplacement
  ChainTotalDual FirstQuadrantCochainBicomplex CategoryCochainReplacement
  CategoryCochainReplacementSimplicial SimplicialReplacementDualTerms SimplicialReplacementDualDifferentials.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPSimplicialYoneda DPBisimplicialChains DPSimplicialReplacement DPChainTotalDual
  DPFirstQuadrantCochain DPCategoryCochainReplacementSimplicial DPSimplicialReplacementDualTerms
  DPSimplicialReplacementDualDifferentials.

Module DPSimplicialReplacementDualBicomplex.
Section Comparison.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.
Let K := dual_bicomplex A (bisimplicial_bicomplex R (replacement F)).
Let B := cochain_replacement_bicomplex (dual_diagram F A).

Definition from_bar_bicomplex : bicomplex_map B K :=
  @BicomplexMap R B K
    (fun p q => module_hom_to_linear (@from_bar_hom R C F A p q))
    (fun p q => @from_bar_horizontal R C F A p q)
    (fun p q => @from_bar_vertical R C F A p q).

Lemma to_bar_horizontal p q (f : bicomplex_term K p q) :
  horizontal B p q (@to_bar R C F A p q f) = @to_bar R C F A p.+1 q (horizontal K p q f).
Proof.
apply (can_inj (@to_from_bar R C F A p.+1 q)).
change (from_bar (horizontal B p q (@to_bar R C F A p q f)) =
  from_bar (@to_bar R C F A p.+1 q (horizontal K p q f))).
rewrite -from_bar_horizontal !from_to_bar; reflexivity.
Qed.
Lemma to_bar_vertical p q (f : bicomplex_term K p q) :
  vertical B p q (@to_bar R C F A p q f) = @to_bar R C F A p q.+1 (vertical K p q f).
Proof.
apply (can_inj (@to_from_bar R C F A p q.+1)).
change (from_bar (vertical B p q (@to_bar R C F A p q f)) =
  from_bar (@to_bar R C F A p q.+1 (vertical K p q f))).
rewrite -from_bar_vertical !from_to_bar; reflexivity.
Qed.
Definition to_bar_bicomplex : bicomplex_map K B :=
  @BicomplexMap R K B
    (fun p q => module_hom_to_linear (@to_bar_hom R C F A p q)) to_bar_horizontal to_bar_vertical.

Lemma bicomplex_comparison_left p q (f : bicomplex_term K p q) :
  bicomplex_map_at from_bar_bicomplex p q (bicomplex_map_at to_bar_bicomplex p q f)=f.
Proof. exact: from_to_bar. Qed.
Lemma bicomplex_comparison_right p q (f : bicomplex_term B p q) :
  bicomplex_map_at to_bar_bicomplex p q (bicomplex_map_at from_bar_bicomplex p q f)=f.
Proof. exact: to_from_bar. Qed.
End Comparison.
End DPSimplicialReplacementDualBicomplex.
