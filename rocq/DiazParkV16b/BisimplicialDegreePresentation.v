(** Literal model generators and their universal property for each bidegree. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  BarFreeModule BarResolutionHom.
From DiazParkV16b Require Import ModelwisePresentation BisimplicialSet BisimplicialRepresentable
  BisimplicialRepresentableYoneda BisimplicialChainDiagrams.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkBarResolutionHom DPModelwisePresentation
  DPBisimplicialSet DPBisimplicialRepresentable DPBisimplicialRepresentableYoneda DPBisimplicialChainDiagrams.
Local Open Scope ring_scope.

Module DPBisimplicialDegreePresentation.
Lemma characteristic_generator p q :
  characteristic (representable p q) (representable_generator p q) = nat_id (representable p q).
Proof.
have h := @characteristic_evaluate (representable p q) p q (nat_id (representable p q)).
exact h.
Qed.

Section Presentation.
Variable R : pzRingType.
Variables p q : nat.
Definition degree_model (_ : unit) : bisimplicial_category := representable p q.
Definition degree_generator : fobj (bisimplex_degree R p q) (representable p q) :=
  free_basis R (representable_generator p q).

Variable F : module_diagram R bisimplicial_category.
Variable v : fobj F (representable p q).

Definition degree_lift : nat_trans (bisimplex_degree R p q) F.
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (bisimplex_degree R p q) F
  (fun X => module_hom_of_linear (free_lift (fun x : bisimplex X p q =>
    module_hom_fun (fmap F (characteristic X x)) v))) _).
move=> X Y a; apply free_module_hom_ext => x.
change (free_lift (fun y => module_hom_fun (fmap F (characteristic Y y)) v)
  (free_map R (bisimplex_component a p q) (free_basis R x)) =
  module_hom_fun (fmap F a) (free_lift (fun y => module_hom_fun (fmap F (characteristic X y)) v) (free_basis R x))).
rewrite free_map_basis !free_lift_basis -characteristic_natural fmap_compose; reflexivity.
Defined.

Lemma degree_lift_generator : module_hom_fun (component degree_lift (representable p q)) degree_generator = v.
Proof.
change (free_lift (fun x => module_hom_fun (fmap F (characteristic (representable p q) x)) v)
  (free_basis R (representable_generator p q)) = v).
rewrite free_lift_basis characteristic_generator fmap_id; reflexivity.
Qed.

Lemma degree_lift_unique (a : nat_trans (bisimplex_degree R p q) F) :
  module_hom_fun (component a (representable p q)) degree_generator = v -> a = degree_lift.
Proof.
move=> hv; apply nat_trans_ext => X; apply free_module_hom_ext => x.
have h := f_equal (fun t : module_hom (fobj (bisimplex_degree R p q) (representable p q)) (fobj F X) => t degree_generator)
  (naturality a (characteristic X x)).
change (module_hom_fun (component a X) (free_map R (bisimplex_component (characteristic X x) p q) degree_generator) =
  module_hom_fun (fmap F (characteristic X x)) (module_hom_fun (component a (representable p q)) degree_generator)) in h.
rewrite hv /degree_generator free_map_basis in h.
change (module_hom_fun (component a X) (free_basis R (evaluate X (characteristic X x))) =
  module_hom_fun (fmap F (characteristic X x)) v) in h.
rewrite evaluate_characteristic in h.
change (module_hom_fun (component a X) (free_basis R x) =
  free_lift (fun y => module_hom_fun (fmap F (characteristic X y)) v) (free_basis R x)).
by rewrite free_lift_basis.
Qed.
End Presentation.

Definition degree_presentation (R : pzRingType) p q :
  model_presentation (degree_model p q) (bisimplex_degree R p q).
Proof.
refine (@ModelPresentation R bisimplicial_category unit (degree_model p q) (bisimplex_degree R p q)
  (fun _ => degree_generator R p q) (fun F v => degree_lift (v tt)) _ _).
- move=> F v []; exact: degree_lift_generator.
- move=> F a b h.
  transitivity (degree_lift (module_hom_fun (component b (representable p q)) (degree_generator R p q))).
  + apply degree_lift_unique; exact (h tt).
  + symmetry; apply degree_lift_unique; reflexivity.
Defined.

Definition diagonal_presentation (R : pzRingType) n :
  model_presentation (degree_model n n) (diagonal_degree R n) := degree_presentation R n n.
End DPBisimplicialDegreePresentation.
