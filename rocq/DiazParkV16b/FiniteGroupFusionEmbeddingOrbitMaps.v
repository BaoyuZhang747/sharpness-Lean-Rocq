(** Literal subgroup and raw-map transport along a pair of inverse group
    morphisms.  This is independent of fusion or cohomology assumptions. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionConjugacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPFusionGroupIsomorphismMaps.
Section Maps.
Variables N T : finGroupType.
Variable e : {morphism [set: N] >-> T}.
Variable r : {morphism [set: T] >-> N}.
Hypothesis er : cancel e r.
Hypothesis re : cancel r e.

Definition subgroup (P : {group N}) : {group T} := (e @* P)%G.
Definition inverse_subgroup (Q : {group T}) : {group N} := (r @* Q)%G.

Lemma subgroup_mem (P : {group N}) x : x \in P -> e x \in subgroup P.
Proof. move=> hx; exact (mem_morphim e (in_setT x) hx). Qed.

Lemma subgroup_repr (P : {group N}) y : y \in subgroup P -> r y \in P.
Proof. move/morphimP=> [x _ hx ->]; by rewrite er. Qed.

Lemma subgroup_inverse P : inverse_subgroup (subgroup P) = P.
Proof.
apply val_inj; apply/setP=> x; apply/idP/idP.
- move/morphimP=> [y _ /morphimP[z _ hz ->] ->]; by rewrite er.
- move=> hx; rewrite -(er x); exact (mem_morphim r (in_setT _) (subgroup_mem hx)).
Qed.

Lemma inverse_subgroupK Q : subgroup (inverse_subgroup Q) = Q.
Proof.
apply val_inj; apply/setP=> x; apply/idP/idP.
- move/morphimP=> [y _ /morphimP[z _ hz ->] ->]; by rewrite re.
- move=> hx; rewrite -(re x); exact (mem_morphim e (in_setT _) (mem_morphim r (in_setT _) hx)).
Qed.

Lemma subgroup_injective : injective subgroup.
Proof. exact (can_inj subgroup_inverse). Qed.

Lemma e_injm : 'injm e.
Proof. apply/injmP=> x y _ _ h; exact (can_inj er h). Qed.

Lemma r_injm : 'injm r.
Proof. apply/injmP=> x y _ _ h; exact (can_inj re h). Qed.

Lemma subgroup_top : subgroup [set: N]%G = [set: T]%G.
Proof.
apply val_inj; apply/setP=> x; rewrite inE; apply/morphimP.
by exists (r x); rewrite ?inE // re.
Qed.

Lemma subgroup_centralizer (P : {group N}) : subgroup 'C(P)%G = 'C(subgroup P)%G.
Proof.
apply val_inj; have h := injm_cent e_injm (subsetT P).
have ht : e @* [set: N] = [set: T] := congr1 val subgroup_top.
by rewrite ht !setTI in h.
Qed.

Definition map_function (P Q : {group N}) (f : DPFusion.map P Q) (y : T) := e (f (r y)).

Lemma map_function_morphic (P Q : {group N}) (f : DPFusion.map P Q) :
  {in subgroup P &, {morph map_function f : x y / x*y}}.
Proof.
move=> x y hx hy; rewrite /map_function (morphM r (in_setT _) (in_setT _)).
rewrite map_mul ?subgroup_repr //; exact (morphM e (in_setT _) (in_setT _)).
Qed.

Canonical map_morphism (P Q : {group N}) (f : DPFusion.map P Q) :=
  Morphism (map_function_morphic f).

Lemma map_morphism_injm (P Q : {group N}) (f : DPFusion.map P Q) : 'injm (map_morphism f).
Proof.
apply/injmP=> x y hx hy h; apply (can_inj re).
apply (map_injective (f := f) (subgroup_repr hx) (subgroup_repr hy)).
exact (can_inj er h).
Qed.

Lemma map_morphism_range (P Q : {group N}) (f : DPFusion.map P Q) :
  map_morphism f @* subgroup P \subset subgroup Q.
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
exact (subgroup_mem (map_into f (subgroup_repr hx))).
Qed.

Definition map (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusion.map (subgroup P) (subgroup Q) :=
  of_morphism (map_morphism_injm f) (map_morphism_range f).

Lemma mapE (P Q : {group N}) (f : DPFusion.map P Q) y :
  y \in subgroup P -> map f y = e (f (r y)).
Proof. exact: of_morphism_in. Qed.

Lemma map_imageE (P Q : {group N}) (f : DPFusion.map P Q) x :
  x \in P -> map f (e x) = e (f x).
Proof. move=> hx; by rewrite mapE ?subgroup_mem // er. Qed.

Lemma map_identity P : map (identity P) = identity (subgroup P).
Proof.
apply map_ext=> y hy; rewrite mapE // !identity_in ?subgroup_repr //; exact: re.
Qed.

Lemma map_compose (P Q U : {group N}) (f : DPFusion.map P Q) (g : DPFusion.map Q U) :
  map (compose f g) = compose (map f) (map g).
Proof.
apply map_ext=> y hy.
rewrite (compose_in (map f) (map g) hy) (mapE (compose f g) hy)
  (mapE g (map_into (map f) hy)) (mapE f hy) er.
by rewrite compose_in ?subgroup_repr.
Qed.

Lemma map_injective (P Q : {group N}) : injective (@map P Q).
Proof.
move=> f g h; apply map_ext=> x hx; apply (can_inj er).
have hh := congr1 (fun k : DPFusion.map (subgroup P) (subgroup Q) => k (e x)) h.
by rewrite !map_imageE // in hh.
Qed.

Lemma map_image (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusion.image (map f) = subgroup (DPFusion.image f).
Proof.
apply val_inj; apply/setP=> y; apply/idP/idP.
- move/morphimP=> [x hx _ ->].
  change (is_true (map f x \in subgroup (DPFusion.image f))).
  rewrite mapE //.
  exact (subgroup_mem (image_mem f (subgroup_repr hx))).
- move/morphimP=> [x _ /morphimP[z hz _ ->] ->].
  change (is_true (e (f z) \in DPFusion.image (map f))).
  rewrite -(map_imageE f hz); exact (image_mem (map f) (subgroup_mem hz)).
Qed.
End Maps.
End DPFusionGroupIsomorphismMaps.
