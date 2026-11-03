(** Elementary transport of exactness through actual module isomorphisms. *)
From mathcomp Require Import all_ssreflect ssralg.
From DiazPark Require Import Category CategoryModules.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma module_iso_hom_inv_apply {R : pzRingType} {U V : lmodType R}
    (e : @isomorphism (module_category R) U V) (x : U) :
    module_hom_fun (iso_inv e) (module_hom_fun (iso_hom e) x) = x.
Proof. exact (f_equal (fun h : module_hom U U => h x) (iso_hom_inv e)). Qed.

Lemma module_iso_inv_hom_apply {R : pzRingType} {U V : lmodType R}
    (e : @isomorphism (module_category R) U V) (x : V) :
    module_hom_fun (iso_hom e) (module_hom_fun (iso_inv e) x) = x.
Proof. exact (f_equal (fun h : module_hom V V => h x) (iso_inv_hom e)). Qed.

Lemma module_iso_hom_injective {R : pzRingType} {U V : lmodType R}
    (e : @isomorphism (module_category R) U V) :
    injective (module_hom_fun (iso_hom e)).
Proof.
  intros x y h. rewrite <- (module_iso_hom_inv_apply e x),
    <- (module_iso_hom_inv_apply e y). exact (f_equal (module_hom_fun (iso_inv e)) h).
Qed.

Section Transport.
Variable R : pzRingType.
Variables U V W U' V' W' : lmodType R.
Variables (eU : @isomorphism (module_category R) U U')
  (eV : @isomorphism (module_category R) V V')
  (eW : @isomorphism (module_category R) W W').
Variables (f : module_hom U V) (g : module_hom V W)
  (f' : module_hom U' V') (g' : module_hom V' W').
Hypothesis hf : forall x,
  module_hom_fun (iso_hom eV) (f x) = f' (module_hom_fun (iso_hom eU) x).
Hypothesis hg : forall y,
  module_hom_fun (iso_hom eW) (g y) = g' (module_hom_fun (iso_hom eV) y).

Theorem module_exact_iso_transport
    (he : forall y, g' y = 0 <-> exists x, f' x = y) (y : V) :
    g y = 0 <-> exists x, f x = y.
Proof.
  split.
  - intro hy.
    assert (g' (module_hom_fun (iso_hom eV) y) = 0) as hy'.
    { rewrite -hg hy. apply module_hom_zero. }
    destruct ((proj1 (he _)) hy') as [x hx].
    exists (module_hom_fun (iso_inv eU) x).
    apply (@module_iso_hom_injective R V V' eV).
    rewrite hf module_iso_inv_hom_apply. exact hx.
  - intros [x <-]. apply (@module_iso_hom_injective R W W' eW).
    rewrite hg module_hom_zero hf.
    apply (proj2 (he _)). exists (module_hom_fun (iso_hom eU) x). reflexivity.
Qed.
End Transport.
