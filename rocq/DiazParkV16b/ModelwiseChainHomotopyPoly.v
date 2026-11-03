(** Natural homotopies constructed recursively from actual modelwise exactness. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules.
From DiazParkV16b Require Import ModelwiseChainDiagram ModelwisePresentation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPModelwiseChainDiagram DPModelwisePresentation.
Local Open Scope ring_scope.

Module DPModelwiseChainHomotopyPoly.

(** Pointwise operations are polymorphic; the large category of models is not tied to the universe of any fixed small indexing category. *)
Definition local_module_zero {R:pzRingType} (U V:lmodType R) : module_hom U V.
Proof. exists (fun _=>0); move=>r x y; by rewrite scaler0 add0r. Defined.
Definition local_module_sub {R:pzRingType} {U V:lmodType R} (a b:module_hom U V) : module_hom U V.
Proof.
exists (fun x=>a x-b x); move=>r x y.
rewrite !module_hom_linear scalerBr; by rewrite opprD addrACA.
Defined.
Definition diagram_zero {R:pzRingType} {C:category} (F G:module_diagram R C) : nat_trans F G.
Proof.
refine (@Build_nat_trans C (module_category R) F G (fun x=>local_module_zero (fobj F x) (fobj G x)) _).
move=>x y f; apply module_hom_ext=>v; symmetry; exact: module_hom_zero.
Defined.
Definition diagram_sub {R:pzRingType} {C:category} {F G:module_diagram R C} (a b:nat_trans F G) : nat_trans F G.
Proof.
refine (@Build_nat_trans C (module_category R) F G (fun x=>local_module_sub (component a x) (component b x)) _).
move=>x y f; apply module_hom_ext=>v.
have ha:=f_equal (fun k:module_hom (fobj F x) (fobj G y)=>k v) (naturality a f).
have hb:=f_equal (fun k:module_hom (fobj F x) (fobj G y)=>k v) (naturality b f).
change (module_hom_fun (component a y) (module_hom_fun (fmap F f) v)-module_hom_fun (component b y) (module_hom_fun (fmap F f) v)=
 module_hom_fun (fmap G f) (module_hom_fun (component a x) v-module_hom_fun (component b x) v)).
rewrite module_hom_sub; exact (f_equal2 (fun x y=>x-y) ha hb).
Defined.

Section Homotopy.
Variable R : pzRingType.
Variable C : category.
Variables P Q : chain_diagram R C.
Variables f g : chain_diagram_map P Q.
Variable I : nat -> Type.
Variable models : forall n, I n -> C.
Arguments models _ _ : clear implicits.
Variable pres : forall n, model_presentation (models n) (diagram_degree P n).
Variable hzero : diagram_map_degree f 0%N = diagram_map_degree g 0%N.
Variable hpos : forall n (i : I n.+1) (x : fobj (diagram_degree Q n.+1) (models n.+1 i)),
  diagram_apply (diagram_d Q n) (models n.+1 i) x = 0 ->
  exists y, diagram_apply (diagram_d Q n.+1) (models n.+1 i) y = x.

Definition difference n := diagram_sub (diagram_map_degree f n) (diagram_map_degree g n).
Lemma difference_apply n X x : diagram_apply (difference n) X x =
  diagram_apply (diagram_map_degree f n) X x - diagram_apply (diagram_map_degree g n) X x.
Proof. reflexivity. Qed.
Lemma difference_d n X x :
  diagram_apply (diagram_d Q n) X (diagram_apply (difference n.+1) X x) =
  diagram_apply (difference n) X (diagram_apply (diagram_d P n) X x).
Proof. rewrite !difference_apply /diagram_apply module_hom_sub; exact (f_equal2 (fun a b => a-b) (diagram_map_d f n X x) (diagram_map_d g n X x)). Qed.

Definition remainder n (h : nat_trans (diagram_degree P n) (diagram_degree Q n.+1)) :=
  diagram_sub (difference n.+1) (nat_comp (diagram_d P n) h).
Lemma remainder_apply n h X x : diagram_apply (remainder h) X x =
  diagram_apply (difference n.+1) X x - diagram_apply h X (diagram_apply (diagram_d P n) X x).
Proof. reflexivity. Qed.

Record homotopy_step n := HomotopyStep {
  step_map : nat_trans (diagram_degree P n) (diagram_degree Q n.+1);
  step_cycle : forall X (x : fobj (diagram_degree P n.+1) X),
    diagram_apply (diagram_d Q n) X (diagram_apply (remainder step_map) X x) = 0
}.
Arguments step_cycle {n} h X x.

Definition zero_step : homotopy_step 0%N.
Proof.
refine (@HomotopyStep 0%N (diagram_zero _ _) _).
move=> X x; rewrite remainder_apply.
change (diagram_apply (diagram_d Q 0%N) X (diagram_apply (difference 1%N) X x - 0) = 0).
rewrite subr0 difference_d difference_apply hzero subrr; reflexivity.
Defined.

Lemma step_preimage n (h : homotopy_step n) (i : I n.+1) :
  exists y, diagram_apply (diagram_d Q n.+1) (models n.+1 i) y =
    diagram_apply (remainder (step_map h)) (models n.+1 i) (model_generator (pres n.+1) i).
Proof. apply (@hpos n i); exact: step_cycle. Qed.

Definition lifted_step n (h : homotopy_step n) :
  nat_trans (diagram_degree P n.+1) (diagram_degree Q n.+2) :=
  @lift_along R C (I n.+1) (models n.+1) (diagram_degree P n.+1) (pres n.+1)
    (diagram_degree Q n.+2) (diagram_degree Q n.+1) (diagram_d Q n.+1)
    (remainder (step_map h)) (@step_preimage n h).

Lemma lifted_step_d n (h : homotopy_step n) X x :
  diagram_apply (diagram_d Q n.+1) X (diagram_apply (lifted_step h) X x) =
    diagram_apply (remainder (step_map h)) X x.
Proof. exact: lift_along_apply. Qed.

Definition successor_step n (h : homotopy_step n) : homotopy_step n.+1.
Proof.
refine (@HomotopyStep n.+1 (lifted_step h) _).
move=> X x; rewrite remainder_apply /diagram_apply module_hom_sub.
change (diagram_apply (diagram_d Q n.+1) X (diagram_apply (difference n.+2) X x) -
  diagram_apply (diagram_d Q n.+1) X (diagram_apply (lifted_step h) X (diagram_apply (diagram_d P n.+1) X x)) = 0).
rewrite difference_d lifted_step_d remainder_apply diagram_d_squared.
rewrite /diagram_apply module_hom_zero subr0 subrr; reflexivity.
Defined.

Fixpoint constructed_step n : homotopy_step n :=
  match n as k return homotopy_step k with
  | 0%N => zero_step
  | k.+1 => successor_step (constructed_step k)
  end.
Definition homotopy_degree n := step_map (constructed_step n).

Lemma homotopy_degree_zero X x :
  diagram_apply (diagram_d Q 0%N) X (diagram_apply (homotopy_degree 0%N) X x) =
    diagram_apply (diagram_map_degree f 0%N) X x - diagram_apply (diagram_map_degree g 0%N) X x.
Proof. rewrite hzero subrr; exact: module_hom_zero. Qed.

Lemma homotopy_degree_succ n X x :
  diagram_apply (diagram_d Q n.+1) X (diagram_apply (homotopy_degree n.+1) X x) +
  diagram_apply (homotopy_degree n) X (diagram_apply (diagram_d P n) X x) =
    diagram_apply (diagram_map_degree f n.+1) X x - diagram_apply (diagram_map_degree g n.+1) X x.
Proof.
change (diagram_apply (diagram_d Q n.+1) X (diagram_apply (lifted_step (constructed_step n)) X x) +
  diagram_apply (step_map (constructed_step n)) X (diagram_apply (diagram_d P n) X x) =
  diagram_apply (diagram_map_degree f n.+1) X x - diagram_apply (diagram_map_degree g n.+1) X x).
by rewrite lifted_step_d remainder_apply subrK difference_apply.
Qed.

Definition modelwise_chain_homotopy : chain_diagram_homotopy f g :=
  @ChainDiagramHomotopy R C P Q f g homotopy_degree homotopy_degree_zero homotopy_degree_succ.
End Homotopy.
End DPModelwiseChainHomotopyPoly.
