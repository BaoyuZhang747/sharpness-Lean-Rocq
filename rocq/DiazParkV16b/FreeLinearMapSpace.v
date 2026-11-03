(** Evaluation on generators identifies Hom(R[X],A) with all X-indexed A-values. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts BarFreeModule.
From DiazParkV16b Require Import LinearMapSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPLinearMapSpace.
Local Open Scope ring_scope.

Module DPFreeLinearMapSpace.
Section FreeHom.
Variable R : comPzRingType.
Variable X : Type.
Variable A : lmodType R.
Definition functions : lmodType R := module_product_type (fun _ : X => A).
Definition free_hom : lmodType R := linear_maps (free_module R X) A.

Definition on_generators (f : free_hom) : functions := fun x => evaluate f (free_basis R x).
Lemma on_generators_linear : linear on_generators.
Proof. move=> r f g; apply functional_extensionality_dep => x; reflexivity. Qed.
HB.instance Definition _ := GRing.isLinear.Build R free_hom functions _
  on_generators on_generators_linear.

Definition extend (f : functions) : free_hom :=
  of_linear (free_lift f : {linear free_module R X -> A}).

Lemma extend_generators (f : functions) x : evaluate (extend f) (free_basis R x) = f x.
Proof. exact: free_lift_basis. Qed.

Lemma extend_linear : linear extend.
Proof.
move=> r f g; apply ext => a.
apply (free_lift_ext
  (g := as_linear (extend (r *: f + g)))
  (h := as_linear (r *: extend f + extend g))).
move=> x; change (evaluate (extend (r *: f + g)) (free_basis R x) =
  r *: evaluate (extend f) (free_basis R x) + evaluate (extend g) (free_basis R x)).
by rewrite !extend_generators.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R functions free_hom _ extend extend_linear.

Lemma generators_extend (f : functions) : on_generators (extend f) = f.
Proof. apply functional_extensionality_dep => x; exact: extend_generators. Qed.

Lemma extend_on_generators (f : free_hom) : extend (on_generators f) = f.
Proof.
apply ext => a; apply (free_lift_ext (g := as_linear (extend (on_generators f)))
  (h := as_linear f)).
move=> x; change (evaluate (extend (on_generators f)) (free_basis R x) =
  evaluate f (free_basis R x)).
by rewrite extend_generators.
Qed.

Definition generators_iso : @isomorphism (module_category R) free_hom functions.
Proof.
refine (@Build_isomorphism (module_category R) free_hom functions
  (module_hom_of_linear (on_generators : {linear free_hom -> functions}))
  (module_hom_of_linear (extend : {linear functions -> free_hom})) _ _).
- apply module_hom_ext => f; exact: extend_on_generators.
- apply module_hom_ext => f; exact: generators_extend.
Defined.
End FreeHom.
End DPFreeLinearMapSpace.
