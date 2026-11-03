(** Actual one-object functors attached to group homomorphisms. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryIsomorphism.
From DiazParkV16b Require Import GroupCohomologyBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology.
Local Open Scope group_scope.

Module DPGroupCohomologyFunctor.

Definition group_functor (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) :
    functor (group_category G) (group_category H).
Proof.
refine (@Build_functor (group_category G) (group_category H)
  (fun x => x) (fun x y a => f a) _ _).
- move=> x; exact: morph1.
- move=> x y z a b; apply: morphM; by rewrite inE.
Defined.

Definition group_hom_identity (G : finGroupType) :
    {morphism [set: G] >-> G} := [morphism of idm [set: G]].

Definition group_hom_comp (G H K : finGroupType)
    (f : {morphism [set: G] >-> H}) (g : {morphism [set: H] >-> K}) :
    {morphism [set: G] >-> K}.
Proof.
apply: (Morphism (mfun := fun x => g (f x))).
move=> x y _ _; rewrite !morphM ?inE //.
Defined.

Lemma group_functor_identity (G : finGroupType) :
  group_functor (group_hom_identity G) = functor_id (group_category G).
Proof.
apply (@functor_extensionality _ _
  (group_functor (group_hom_identity G)) (functor_id (group_category G))
  Logic.eq_refl); reflexivity.
Qed.

Lemma group_functor_composition (G H K : finGroupType)
    (f : {morphism [set: G] >-> H}) (g : {morphism [set: H] >-> K}) :
  group_functor (group_hom_comp f g) =
    functor_comp (group_functor f) (group_functor g).
Proof.
apply (@functor_extensionality _ _
  (group_functor (group_hom_comp f g))
  (functor_comp (group_functor f) (group_functor g)) Logic.eq_refl); reflexivity.
Qed.

Definition group_conjugation (G : finGroupType) (a : G) :
    {morphism [set: G] >-> G} := [morphism of conjgm [set: G] a].

Lemma group_conjugation_apply (G : finGroupType) (a x : G) :
  group_conjugation a x = x ^ a.
Proof. reflexivity. Qed.

(** The natural transformation is constructed from the actual conjugating
    group element. No cohomological invariance is assumed. *)
Definition inner_nat_trans (G : finGroupType) (a : G) :
    nat_trans (functor_id (group_category G))
      (group_functor (group_conjugation a)).
Proof.
refine (@Build_nat_trans (group_category G) (group_category G)
  (functor_id (group_category G)) (group_functor (group_conjugation a))
  (fun _ => a) _).
move=> x y f; change (f * a = a * (f ^ a)).
by rewrite /conjg !mulgA mulgV mul1g.
Defined.

End DPGroupCohomologyFunctor.
