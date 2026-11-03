(** Genuine natural diagrams of downward chain complexes and homotopies. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear.
From DiazParkV16b Require Import ChainComplex ChainHomologyMaps.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomologyMaps.
Local Open Scope ring_scope.

Module DPModelwiseChainDiagram.
Section Diagrams.
Variable R : pzRingType.
Variable C : category.
Definition diagram_apply (P Q : module_diagram R C) (f : nat_trans P Q) (X : C) :
  fobj P X -> fobj Q X := module_hom_fun (component f X).
Arguments diagram_apply {P Q} f X x.
Record chain_diagram := ChainDiagram {
  diagram_degree : nat -> module_diagram R C;
  diagram_d : forall n, nat_trans (diagram_degree n.+1) (diagram_degree n);
  diagram_d_squared : forall n X (x : fobj (diagram_degree n.+2) X),
    diagram_apply (diagram_d n) X (diagram_apply (diagram_d n.+1) X x) = 0
}.
Arguments diagram_d_squared c n X x : clear implicits.

Definition evaluated_chain (P : chain_diagram) (X : C) : chain_complex R :=
  @ChainComplex R (fun n => fobj (diagram_degree P n) X)
    (fun n => module_hom_to_linear (component (diagram_d P n) X))
    (fun n => diagram_d_squared P n X).

Definition evaluated_chain_map (P : chain_diagram) (X Y : C) (f : hom C X Y) :
  chain_map (evaluated_chain P X) (evaluated_chain P Y).
Proof.
refine (@ChainMap R (evaluated_chain P X) (evaluated_chain P Y)
  (fun n => module_hom_to_linear (fmap (diagram_degree P n) f)) _).
move=> n x; exact (f_equal (fun a : module_hom (fobj (diagram_degree P n.+1) X)
  (fobj (diagram_degree P n) Y) => a x) (naturality (diagram_d P n) f)).
Defined.

Record chain_diagram_map (P Q : chain_diagram) := ChainDiagramMap {
  diagram_map_degree : forall n, nat_trans (diagram_degree P n) (diagram_degree Q n);
  diagram_map_d : forall n X (x : fobj (diagram_degree P n.+1) X),
    diagram_apply (diagram_d Q n) X (diagram_apply (diagram_map_degree n.+1) X x) =
    diagram_apply (diagram_map_degree n) X (diagram_apply (diagram_d P n) X x)
}.
Arguments diagram_map_d {P Q} c n X x.

Definition evaluated_diagram_map (P Q : chain_diagram) (f : chain_diagram_map P Q) (X : C) :
  chain_map (evaluated_chain P X) (evaluated_chain Q X) :=
  @ChainMap R (evaluated_chain P X) (evaluated_chain Q X)
    (fun n => module_hom_to_linear (component (diagram_map_degree f n) X))
    (fun n => diagram_map_d f n X).

Definition diagram_identity (P : chain_diagram) : chain_diagram_map P P.
Proof. refine (@ChainDiagramMap P P (fun n => nat_id (diagram_degree P n)) _); by move=> n X x. Defined.

Definition diagram_composition (P Q T : chain_diagram)
  (f : chain_diagram_map P Q) (g : chain_diagram_map Q T) : chain_diagram_map P T.
Proof.
refine (@ChainDiagramMap P T (fun n => nat_comp (diagram_map_degree f n) (diagram_map_degree g n)) _).
move=> n X x; change (diagram_apply (diagram_d T n) X
  (diagram_apply (diagram_map_degree g n.+1) X (diagram_apply (diagram_map_degree f n.+1) X x)) =
  diagram_apply (diagram_map_degree g n) X (diagram_apply (diagram_map_degree f n) X
    (diagram_apply (diagram_d P n) X x))).
by rewrite !diagram_map_d.
Defined.

Record chain_diagram_homotopy (P Q : chain_diagram) (f g : chain_diagram_map P Q) := ChainDiagramHomotopy {
  diagram_homotopy_degree : forall n, nat_trans (diagram_degree P n) (diagram_degree Q n.+1);
  diagram_homotopy_zero : forall X (x : fobj (diagram_degree P 0%N) X),
    diagram_apply (diagram_d Q 0%N) X (diagram_apply (diagram_homotopy_degree 0%N) X x) =
      diagram_apply (diagram_map_degree f 0%N) X x - diagram_apply (diagram_map_degree g 0%N) X x;
  diagram_homotopy_succ : forall n X (x : fobj (diagram_degree P n.+1) X),
    diagram_apply (diagram_d Q n.+1) X (diagram_apply (diagram_homotopy_degree n.+1) X x) +
    diagram_apply (diagram_homotopy_degree n) X (diagram_apply (diagram_d P n) X x) =
      diagram_apply (diagram_map_degree f n.+1) X x - diagram_apply (diagram_map_degree g n.+1) X x
}.
Arguments diagram_homotopy_zero {P Q f g} c X x.
Arguments diagram_homotopy_succ {P Q f g} c n X x.

Definition evaluated_diagram_homotopy (P Q : chain_diagram) (f g : chain_diagram_map P Q)
  (h : chain_diagram_homotopy f g) (X : C) :
  chain_homotopy (evaluated_diagram_map f X) (evaluated_diagram_map g X) :=
  @ChainHomotopy R (evaluated_chain P X) (evaluated_chain Q X)
    (evaluated_diagram_map f X) (evaluated_diagram_map g X)
    (fun n => module_hom_to_linear (component (diagram_homotopy_degree h n) X))
    (diagram_homotopy_zero h X) (fun n => diagram_homotopy_succ h n X).

Theorem evaluated_homology_homotopy (P Q : chain_diagram) (f g : chain_diagram_map P Q)
  (h : chain_diagram_homotopy f g) (X : C) n q :
  homology_map (evaluated_diagram_map f X) n q = homology_map (evaluated_diagram_map g X) n q.
Proof. exact: (homology_map_homotopy (evaluated_diagram_homotopy h X)). Qed.
End Diagrams.
Arguments diagram_apply {R C P Q} f X x.
Arguments diagram_d_squared {R C} c n X x.
Arguments diagram_map_d {R C P Q} c n X x.
Arguments diagram_homotopy_zero {R C P Q f g} c X x.
Arguments diagram_homotopy_succ {R C P Q f g} c n X x.
End DPModelwiseChainDiagram.
