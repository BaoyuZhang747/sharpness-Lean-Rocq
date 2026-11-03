(** Actual objectwise Hom-dual chains of a covariant simplicial-set diagram. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalDiagramInjectives.
From DiazParkV16b Require Import ChainComplex ChainDualCochain LinearMapSpace SimplicialSet
  SimplicialSetYoneda SimplicialChains SimplicialChainsMaps CategoryCochainReplacement CategoryCochainReplacementTotal.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPChainComplex DPChainDualCochain DPLinearMapSpace
  DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPCategoryCochainReplacementSimplicial.
Section Diagram.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.

Definition dual_degree (q : nat) : module_diagram R (opposite C).
Proof.
refine (@Build_functor (opposite C) (module_category R)
  (fun c => cochain_term (@dual_complex R A (chains R (fobj F c))) q)
  (fun c d f => module_hom_of_linear (cochain_map_at (@dual_map R A _ _ (chain_map_of R (fmap F f))) q)) _ _).
- move=> c; apply module_hom_ext => a; apply ext => x.
  change (evaluate a (map_at R (fmap F (identity c)) q x) = evaluate a x).
  by rewrite fmap_id map_identity.
- move=> c d e f g; apply module_hom_ext => a; apply ext => x.
  change (evaluate a (map_at R (fmap F (@compose C e d c g f)) q x) =
    evaluate a (map_at R (fmap F f) q (map_at R (fmap F g) q x))).
  by rewrite fmap_compose map_composition.
Defined.

Definition dual_differential q : nat_trans (dual_degree q) (dual_degree q.+1).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) (dual_degree q) (dual_degree q.+1)
  (fun c => module_hom_of_linear (cochain_d (@dual_complex R A (chains R (fobj F c))) q)) _).
move=> c d f; apply module_hom_ext => a.
exact (@cochain_map_commutes R _ _ (@dual_map R A _ _ (chain_map_of R (fmap F f))) q a).
Defined.

Definition dual_diagram : @diagram_complex R (opposite C) :=
  @DiagramComplex R (opposite C) dual_degree dual_differential
    (fun q c => @cochain_d2 R (@dual_complex R A (chains R (fobj F c))) q).

Lemma dual_degree_map_evaluate q c d (f : hom C c d)
  (a : fobj (dual_degree q) d) x :
  evaluate (module_hom_fun (fmap (dual_degree q) f) a) x = evaluate a (map_at R (fmap F f) q x).
Proof. reflexivity. Qed.
Lemma dual_differential_evaluate q c (a : fobj (dual_degree q) c) x :
  evaluate (module_hom_fun (component (dual_differential q) c) a) x =
    evaluate a (chain_d (chains R (fobj F c)) q x).
Proof. reflexivity. Qed.

Definition simplicial_cochain_replacement := cochain_replacement_total dual_diagram.
Lemma simplicial_replacement_projection_formula c q (a : cochain_term simplicial_cochain_replacement q) :
  cochain_map_at (replacement_projection dual_diagram c) q a = a 0%N q Logic.eq_refl c tt.
Proof. reflexivity. Qed.
End Diagram.
End DPCategoryCochainReplacementSimplicial.
