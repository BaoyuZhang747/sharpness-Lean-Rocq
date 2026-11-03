From mathcomp Require Import all_ssreflect all_fingroup.

(** Actual injective subgroup maps.  Outside-domain values are normalized to
    the group identity, so equality is exactly equality on the source. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusion.

Section Maps.
Variable S : finGroupType.

Definition injective_on (P : {set S}) (f : S -> S) :=
  [forall x in P, forall y in P, (f x == f y) ==> (x == y)].

Lemma injective_onP (P : {set S}) (f : S -> S) :
  reflect {in P &, injective f} (injective_on P f).
Proof.
apply: (iffP forall_inP) => [h x y Px Py hxy | h x Px].
  apply/eqP; apply: (implyP (forall_inP (h x Px) y Py)).
  exact/eqP.
apply/forall_inP => y Py; apply/implyP => /eqP hxy.
by apply/eqP; apply: h hxy.
Qed.

Definition normalized_on (P : {set S}) (f : S -> S) :=
  [forall x, (x \notin P) ==> (f x == 1)].

Definition map_valid (P Q : {group S}) (f : {ffun S -> S}) :=
  [&& morphic P f, injective_on P f, f @: P \subset Q & normalized_on P f].

Definition map (P Q : {group S}) := {f : {ffun S -> S} | map_valid P Q f}.

Definition map_fun P Q (f : map P Q) : S -> S := val f.
#[global] Coercion map_fun : map >-> Funclass.

Lemma map_morphic P Q (f : map P Q) : morphic P f.
Proof. by have /and4P[h _ _ _] := valP f. Qed.

Lemma map_injective P Q (f : map P Q) : {in P &, injective f}.
Proof. by have /and4P[_ /injective_onP h _ _] := valP f. Qed.

Lemma map_range P Q (f : map P Q) : f @: P \subset Q.
Proof. by have /and4P[_ _ h _] := valP f. Qed.

Lemma map_outside P Q (f : map P Q) x : x \notin P -> f x = 1.
Proof.
move=> nxP; have /and4P[_ _ _ /forallP h] := valP f.
by apply/eqP; apply: (implyP (h x)).
Qed.

Lemma map_ext P Q (f g : map P Q) : {in P, f =1 g} -> f = g.
Proof.
move=> h; apply: val_inj; apply/ffunP=> x.
change (f x = g x).
case Px: (x \in P); first exact: h Px.
by rewrite !map_outside // Px.
Qed.

Definition map_morphism P Q (f : map P Q) : {morphism P >-> S} :=
  [morphism of morphm (map_morphic f)].

Lemma map_morphismE P Q (f : map P Q) x : map_morphism f x = f x.
Proof. by []. Qed.

Lemma map_mul P Q (f : map P Q) : {in P &, {morph f : x y / x * y}}.
Proof. exact: (morphicP (map_morphic f)). Qed.

Lemma map_one P Q (f : map P Q) : f 1 = 1.
Proof. exact: (morph1 (map_morphism f)). Qed.

Lemma map_injm P Q (f : map P Q) : 'injm (map_morphism f).
Proof. apply/injmP; exact: map_injective. Qed.

Lemma map_into P Q (f : map P Q) x : x \in P -> f x \in Q.
Proof.
move=> Px; apply: (subsetP (map_range f)).
by apply/imsetP; exists x.
Qed.

Definition normalize (P : {set S}) (f : S -> S) :=
  [ffun x => if x \in P then f x else 1].

Lemma normalize_in (P : {set S}) (f : S -> S) x :
  x \in P -> normalize P f x = f x.
Proof. by move=> Px; rewrite /normalize ffunE Px. Qed.

Lemma normalize_out (P : {set S}) (f : S -> S) x :
  x \notin P -> normalize P f x = 1.
Proof. by move=> /negbTE Px; rewrite /normalize ffunE Px. Qed.

Lemma normalize_valid (P Q : {group S}) (f : {morphism P >-> S}) :
  'injm f -> f @* P \subset Q -> map_valid P Q (normalize P f).
Proof.
move=> injf fQ; apply/and4P; split.
- apply/morphicP=> x y Px Py.
  by rewrite !normalize_in ?groupM // morphM.
- apply/injective_onP=> x y Px Py.
  rewrite !normalize_in //; exact: (injmP injf x y Px Py).
- apply/subsetP=> y /imsetP[x Px ->].
  rewrite normalize_in //; apply: (subsetP fQ).
  by apply: mem_morphim.
- apply/forallP=> x; apply/implyP=> nxP.
  by rewrite normalize_out.
Qed.

Definition of_morphism (P Q : {group S}) (f : {morphism P >-> S})
    (injf : 'injm f) (fQ : f @* P \subset Q) : map P Q :=
  Sub (normalize P f) (normalize_valid injf fQ).

Lemma of_morphism_in (P Q : {group S}) (f : {morphism P >-> S})
    (injf : 'injm f) (fQ : f @* P \subset Q) :
  {in P, of_morphism injf fQ =1 f}.
Proof. exact: normalize_in. Qed.

Lemma of_morphism_image (P Q : {group S}) (f : {morphism P >-> S})
    (injf : 'injm f) (fQ : f @* P \subset Q) :
  map_morphism (of_morphism injf fQ) @* P = f @* P.
Proof. apply: eq_morphim; exact: of_morphism_in. Qed.

Definition inclusion (P Q : {group S}) (sPQ : P \subset Q) : map P Q.
Proof.
apply: (@of_morphism P Q [morphism of idm P] (injm_idm P)).
by rewrite morphim_idm.
Defined.

Lemma inclusion_in (P Q : {group S}) (sPQ : P \subset Q) x :
  x \in P -> inclusion sPQ x = x.
Proof. exact: normalize_in. Qed.

Definition identity (P : {group S}) : map P P := inclusion (subxx P).

Lemma identity_in (P : {group S}) x : x \in P -> identity P x = x.
Proof. exact: inclusion_in. Qed.

Definition conjugation (P Q : {group S}) (s : S)
    (sPQ : P :^ s \subset Q) : map P Q.
Proof.
apply: (@of_morphism P Q [morphism of conjgm P s] (injm_conj P s)).
by rewrite morphim_conj setIid.
Defined.

Lemma conjugation_in (P Q : {group S}) (s : S)
    (sPQ : P :^ s \subset Q) x :
  x \in P -> conjugation sPQ x = x ^ s.
Proof. exact: normalize_in. Qed.

Definition compose (P Q R : {group S}) (f : map P Q) (g : map Q R) : map P R.
Proof.
assert (hM : {in P &, {morph g \o f : x y / x * y}}).
{
  move=> x y Px Py; rewrite /= map_mul // map_mul //.
  - exact: map_into Px.
  - exact: map_into Py.
}
pose h := @Morphism S S P (g \o f) hM.
assert (injh : 'injm h).
{
  apply/injmP=> x y Px Py hxy.
  apply: (map_injective (f := f) Px Py).
  apply: (map_injective (f := g) _ _ hxy); exact: map_into.
}
assert (hR : h @* P \subset R).
{
  apply/subsetP=> y /morphimP[x Px _ ->].
  apply: map_into; exact: map_into Px.
}
exact: of_morphism injh hR.
Defined.

Lemma compose_in (P Q R : {group S}) (f : map P Q) (g : map Q R) x :
  x \in P -> compose f g x = g (f x).
Proof. exact: normalize_in. Qed.

Lemma identity_compose (P Q : {group S}) (f : map P Q) :
  compose (identity P) f = f.
Proof.
apply: map_ext=> x Px.
by rewrite compose_in // identity_in.
Qed.

Lemma compose_identity (P Q : {group S}) (f : map P Q) :
  compose f (identity Q) = f.
Proof.
apply: map_ext=> x Px.
by rewrite compose_in // identity_in ?map_into.
Qed.

Lemma compose_assoc (P Q R T : {group S})
    (f : map P Q) (g : map Q R) (h : map R T) :
  compose (compose f g) h = compose f (compose g h).
Proof.
apply: map_ext=> x Px.
by rewrite !compose_in // ?map_into.
Qed.

Definition image (P Q : {group S}) (f : map P Q) : {group S} :=
  (map_morphism f @* P)%G.

Lemma image_sub (P Q : {group S}) (f : map P Q) : image f \subset Q.
Proof. rewrite /image /= morphimEdom; exact: map_range. Qed.

Lemma morphism_roundtrip (P Q : {group S}) (f : map P Q) :
  of_morphism (map_injm f) (image_sub f) = f.
Proof. apply: map_ext; exact: of_morphism_in. Qed.

Lemma image_mem (P Q : {group S}) (f : map P Q) x :
  x \in P -> f x \in image f.
Proof. by move=> Px; apply: mem_morphim. Qed.

Definition corestrict (P Q R : {group S}) (f : map P Q)
    (sIR : image f \subset R) : map P R :=
  of_morphism (map_injm f) sIR.

Lemma corestrict_in (P Q R : {group S}) (f : map P Q)
    (sIR : image f \subset R) : {in P, corestrict sIR =1 f}.
Proof. exact: normalize_in. Qed.

Definition restrict (P Q A : {group S}) (f : map P Q)
    (sAP : A \subset P) : map A Q.
Proof.
pose h := [morphism of restrm sAP (map_morphism f)].
assert (injh : 'injm h).
{ apply: injm_restrm; exact: map_injm. }
assert (hQ : h @* A \subset Q).
{
  rewrite /h im_restrm.
  exact: subset_trans (morphimS (map_morphism f) sAP) (image_sub f).
}
exact: of_morphism injh hQ.
Defined.

Lemma restrict_in (P Q A : {group S}) (f : map P Q)
    (sAP : A \subset P) : {in A, restrict f sAP =1 f}.
Proof. exact: normalize_in. Qed.

Definition to_image (P Q : {group S}) (f : map P Q) : map P (image f) :=
  corestrict (subxx (image f)).

Lemma to_image_in (P Q : {group S}) (f : map P Q) : {in P, to_image f =1 f}.
Proof. exact: corestrict_in. Qed.

Lemma image_factorization (P Q : {group S}) (f : map P Q) :
  compose (to_image f) (inclusion (image_sub f)) = f.
Proof.
apply: map_ext=> x Px.
by rewrite compose_in // inclusion_in ?map_into // to_image_in.
Qed.

Definition inverse (P Q : {group S}) (f : map P Q) : map (image f) P.
Proof.
apply: (@of_morphism (image f) P
  [morphism of invm (map_injm f)] (injm_invm (map_injm f))).
by rewrite im_invm.
Defined.

Lemma inverse_in (P Q : {group S}) (f : map P Q) x :
  x \in image f -> inverse f x = invm (map_injm f) x.
Proof. exact: normalize_in. Qed.

Lemma inverse_cancel (P Q : {group S}) (f : map P Q) x :
  x \in P -> inverse f (f x) = x.
Proof.
move=> Px; rewrite inverse_in ?image_mem //.
exact: invmE Px.
Qed.

Lemma inverse_cancel_right (P Q : {group S}) (f : map P Q) x :
  x \in image f -> f (inverse f x) = x.
Proof.
move=> Ix; rewrite inverse_in //.
exact: invmK Ix.
Qed.

Lemma to_image_inverse (P Q : {group S}) (f : map P Q) :
  compose (to_image f) (inverse f) = identity P.
Proof.
apply: map_ext=> x Px.
by rewrite compose_in // to_image_in // inverse_cancel // identity_in.
Qed.

Lemma inverse_to_image (P Q : {group S}) (f : map P Q) :
  compose (inverse f) (to_image f) = identity (image f).
Proof.
apply: map_ext=> x Ix; rewrite compose_in // to_image_in ?map_into //.
by rewrite inverse_cancel_right // identity_in.
Qed.

End Maps.

End DPFusion.
