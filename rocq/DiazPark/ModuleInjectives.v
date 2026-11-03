(** The categorical extension property for arbitrary modules, and its
    coordinatewise product construction. No finiteness or nonzero-ring
    hypothesis is imposed. Existence of enough injectives is separate. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryInjectives CategoryModules
  CategoryModuleProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ModuleInjectivity.
Variable R : pzRingType.

Definition module_element_hom (U : lmodType R) (x : U) :
    module_hom [the lmodType R of R^o] U.
Proof.
  exists (fun a : R => a *: x). intros a b c.
  change ((a * (b : R) + (c : R)) *: x =
    a *: ((b : R) *: x) + (c : R) *: x).
  by rewrite scalerDl scalerA.
Defined.

Lemma module_monomorphism_iff (U V : lmodType R) (m : module_hom U V) :
    @monomorphism (module_category R) U V m <-> injective m.
Proof.
  split.
  - intros hm x y e.
    assert (module_hom_comp (module_element_hom x) m =
      module_hom_comp (module_element_hom y) m) as h.
    { apply module_hom_ext. intro a.
      change (m ((a : R) *: x) = m ((a : R) *: y)).
      by rewrite !module_hom_scale e. }
    pose proof (hm _ _ _ h) as q.
    pose proof (f_equal (fun k : module_hom [the lmodType R of R^o] U => k 1) q) as e1.
    change (1 *: x = 1 *: y) in e1. by rewrite !scale1r in e1.
  - intros hm W f g e. apply module_hom_ext. intro x. apply hm.
    exact (f_equal (fun k : module_hom W V => k x) e).
Qed.

Definition module_injective (I : lmodType R) : Prop :=
  forall (U V : lmodType R) (m : module_hom U V), injective m ->
    forall f : module_hom U I,
    exists g : module_hom V I, forall x, g (m x) = f x.

Lemma module_injective_iff (I : lmodType R) :
    module_injective I <-> injective_object (module_category R) I.
Proof.
  split.
  - intros h U V m hm f.
    destruct (h U V m ((proj1 (module_monomorphism_iff m)) hm) f) as [g hg].
    exists g. apply module_hom_ext. exact hg.
  - intros h U V m hm f.
    destruct (h U V m ((proj2 (module_monomorphism_iff m)) hm) f) as [g hg].
    exists g. intro x. exact (f_equal (fun k : module_hom U I => k x) hg).
Qed.

Lemma module_injective_retract (I J : lmodType R)
    (s : module_hom I J) (r : module_hom J I)
    (sr : forall x, r (s x) = x) :
    module_injective J -> module_injective I.
Proof.
  intro hJ. apply module_injective_iff.
  apply (@injective_retract (module_category R) I J s r).
  - apply module_hom_ext. exact sr.
  - apply module_injective_iff. exact hJ.
Qed.

Lemma module_injective_splits (I V : lmodType R)
    (m : module_hom I V) (hm : injective m) :
    module_injective I ->
    exists r : module_hom V I, forall x, r (m x) = x.
Proof. intro hI. exact (hI I V m hm (module_hom_id I)). Qed.

Theorem module_product_injective (A : Type) (I : A -> lmodType R) :
    (forall a, module_injective (I a)) ->
    module_injective (module_product_type I).
Proof.
  intros hI U V m hm f.
  pose (hf := fun a => hI a U V m hm
    (module_hom_comp f (module_product_projection I a))).
  pose (g := fun a => proj1_sig (constructive_indefinite_description (hf a))).
  exists (module_product_lift g). intro x.
  apply functional_extensionality_dep. intro a.
  exact (proj2_sig (constructive_indefinite_description (hf a)) x).
Qed.

End ModuleInjectivity.

Arguments module_injective {R} I.
