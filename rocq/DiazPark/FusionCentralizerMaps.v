From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSubgroup.
Section Reindex.
Variable S : finGroupType.
Definition reindex (P Q P' Q' : {group S}) (eP : P = P') (eQ : Q = Q')
    (f : DPFusion.map P Q) : DPFusion.map P' Q'.
Proof. by subst P' Q'. Defined.

Lemma reindexE (P Q P' Q' : {group S}) (eP : P = P') (eQ : Q = Q')
    (f : DPFusion.map P Q) x : reindex eP eQ f x = f x.
Proof. by subst P' Q'. Qed.

Lemma reindex_allowed (F : DPFusionSystem.system S)
    (P Q P' Q' : {group S}) (eP : P = P') (eQ : Q = Q')
    (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.allowed F (reindex eP eQ f).
Proof. by subst P' Q'. Qed.
End Reindex.

Section SubgroupMaps.
Variable S : finGroupType.
Variable C : {group S}.
Local Notation T := [subg C]%type.

Definition ambient (P : {group T}) : {group S} := (sgval @* P)%G.

Lemma ambient_sub (P : {group T}) : ambient P \subset C.
Proof.
apply/subsetP=> _ /morphimP[x _ _ ->].
exact: subgP x.
Qed.

Lemma ambient_mem (P : {group T}) (x : T) : x \in P -> val x \in ambient P.
Proof. by move=> Px; apply: mem_morphim; rewrite ?inE. Qed.

Lemma ambient_repr (P : {group T}) x : x \in ambient P -> subg C x \in P.
Proof. by case/morphimP=> y _ Py ->; rewrite sgvalK. Qed.

Lemma ambient_subgK (P : {group T}) x : x \in ambient P -> val (subg C x) = x.
Proof. move=> Px; exact: subgK (subsetP (ambient_sub P) x Px). Qed.

Lemma ambient_injective : injective ambient.
Proof.
move=> P Q e; apply: val_inj; apply/setP=> x; apply/idP/idP=> hx.
- have h := ambient_mem hx; rewrite e in h.
  by have := ambient_repr h; rewrite sgvalK.
- have h := ambient_mem hx; rewrite -e in h.
  by have := ambient_repr h; rewrite sgvalK.
Qed.

Lemma ambient_image (P Q : {group T}) (f : DPFusion.map P Q) :
  ambient (DPFusion.image f) = (sgval @* (DPFusion.map_morphism f @* P))%G.
Proof. by []. Qed.

Definition lift_function (P Q : {group T}) (f : DPFusion.map P Q) (x : S) : S :=
  val (f (subg C x)).

Lemma lift_functionE (P Q : {group T}) (f : DPFusion.map P Q) (x : T) :
  lift_function f (val x) = val (f x).
Proof. by rewrite /lift_function sgvalK. Qed.

Lemma lift_function_morph (P Q : {group T}) (f : DPFusion.map P Q) :
  {in ambient P &, {morph lift_function f : x y / x * y}}.
Proof.
move=> _ _ /morphimP[x _ Px ->] /morphimP[y _ Py ->].
change (lift_function f (val (x * y)) = lift_function f (val x) * lift_function f (val y)).
by rewrite !lift_functionE DPFusion.map_mul.
Qed.

Canonical lift_morphism (P Q : {group T}) (f : DPFusion.map P Q) :=
  Morphism (lift_function_morph f).

Lemma lift_morphism_injective (P Q : {group T}) (f : DPFusion.map P Q) :
  'injm (lift_morphism f).
Proof.
apply/injmP=> _ _ /morphimP[x _ Px ->] /morphimP[y _ Py ->].
change (lift_function f (val x) = lift_function f (val y) -> val x = val y).
rewrite !lift_functionE => e; congr (val _).
exact: (DPFusion.map_injective (f := f) Px Py (val_inj e)).
Qed.

Lemma lift_morphism_range (P Q : {group T}) (f : DPFusion.map P Q) :
  lift_morphism f @* ambient P \subset ambient Q.
Proof.
apply/subsetP=> _ /morphimP[x Px _ ->].
rewrite /lift_morphism /= /lift_function.
apply: ambient_mem; exact: DPFusion.map_into (ambient_repr Px).
Qed.

Definition lift (P Q : {group T}) (f : DPFusion.map P Q) :
    DPFusion.map (ambient P) (ambient Q) :=
  DPFusion.of_morphism (lift_morphism_injective f) (lift_morphism_range f).

Lemma liftE (P Q : {group T}) (f : DPFusion.map P Q) (x : T) :
  x \in P -> lift f (val x) = val (f x).
Proof.
move=> Px; rewrite DPFusion.of_morphism_in ?ambient_mem //.
exact: lift_functionE.
Qed.

Lemma lift_image (P Q : {group T}) (f : DPFusion.map P Q) :
  DPFusion.image (lift f) = ambient (DPFusion.image f).
Proof.
apply: val_inj; apply/setP=> z; apply/idP/idP.
- case/morphimP=> x Px _ ->; case/morphimP: Px=> y _ Py ->.
  change (lift f (val y) \in ambient (DPFusion.image f)).
  rewrite liftE //; apply: ambient_mem; exact: DPFusion.image_mem Py.
- case/morphimP=> x _ /morphimP[y Py _ ->] ->.
  change (val (f y) \in DPFusion.image (lift f)).
  rewrite -(liftE f Py); exact: DPFusion.image_mem (ambient_mem Py).
Qed.

Lemma ambient_join (P Q : {group T}) : ambient (P <*> Q)%G = (ambient P <*> ambient Q)%G.
Proof.
apply: val_inj; change (sgval @* (P <*> Q) = sgval @* P <*> sgval @* Q).
by rewrite morphimY ?subsetT.
Qed.

Definition lower_function (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q))
    (x : T) : T := subg C (f (val x)).

Lemma lower_functionE (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q))
    (x : T) : x \in P -> val (lower_function f x) = f (val x).
Proof.
move=> Px; apply: subgK.
exact: subsetP (ambient_sub Q) _ (DPFusion.map_into f (ambient_mem Px)).
Qed.

Lemma lower_function_morph (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :
  {in P &, {morph lower_function f : x y / x * y}}.
Proof.
move=> x y Px Py; apply: val_inj.
change (val (lower_function f (x * y)) = val (lower_function f x) * val (lower_function f y)).
rewrite !lower_functionE ?groupM //.
exact: (DPFusion.map_mul f (ambient_mem Px) (ambient_mem Py)).
Qed.

Canonical lower_morphism (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :=
  Morphism (lower_function_morph f).

Lemma lower_morphism_injective (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :
  'injm (lower_morphism f).
Proof.
apply/injmP=> x y Px Py e; apply: val_inj.
have h := congr1 (fun z : T => val z) e.
change (val (lower_function f x) = val (lower_function f y)) in h.
rewrite !lower_functionE // in h.
exact: (DPFusion.map_injective (f := f) (ambient_mem Px) (ambient_mem Py) h).
Qed.

Lemma lower_morphism_range (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :
  lower_morphism f @* P \subset Q.
Proof.
apply/subsetP=> _ /morphimP[x Px _ ->].
change (subg C (f (val x)) \in Q).
exact: ambient_repr (DPFusion.map_into f (ambient_mem Px)).
Qed.

Definition lower (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :
    DPFusion.map P Q :=
  DPFusion.of_morphism (lower_morphism_injective f) (lower_morphism_range f).

Lemma lowerE (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q))
    (x : T) : x \in P -> val (lower f x) = f (val x).
Proof.
move=> Px; rewrite DPFusion.of_morphism_in //.
exact: lower_functionE.
Qed.

End SubgroupMaps.
End DPFusionSubgroup.
