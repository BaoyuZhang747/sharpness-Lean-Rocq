(** Subtraction of actual natural linear maps. *)
From mathcomp Require Import all_ssreflect ssralg.
From DiazPark Require Import Category CategoryModules.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition module_sub_hom {R : pzRingType} {U V : lmodType R}
    (a b : module_hom U V) : module_hom U V.
Proof.
  exists (fun v => a v - b v). intros r u v.
  rewrite !module_hom_linear scalerBr. by rewrite opprD addrACA.
Defined.

Definition diagram_sub {R : pzRingType} {C : category}
    {F G : module_diagram R C} (a b : nat_trans F G) : nat_trans F G.
Proof.
  refine (@Build_nat_trans C (module_category R) F G
    (fun x => module_sub_hom (component a x) (component b x)) _).
  intros x y f. apply module_hom_ext. intro v.
  pose proof (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k v)
    (naturality a f)) as ha.
  pose proof (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k v)
    (naturality b f)) as hb.
  change (module_hom_fun (component a y) (module_hom_fun (fmap F f) v) -
    module_hom_fun (component b y) (module_hom_fun (fmap F f) v) =
    module_hom_fun (fmap G f)
      (module_hom_fun (component a x) v - module_hom_fun (component b x) v)).
  rewrite module_hom_sub. exact (f_equal2 (fun x y => x - y) ha hb).
Defined.

Lemma diagram_sub_coordinate {R : pzRingType} {C : category}
    {F G : module_diagram R C} (a b : nat_trans F G) x v :
    module_hom_fun (component (diagram_sub a b) x) v =
      module_hom_fun (component a x) v - module_hom_fun (component b x) v.
Proof. reflexivity. Qed.
