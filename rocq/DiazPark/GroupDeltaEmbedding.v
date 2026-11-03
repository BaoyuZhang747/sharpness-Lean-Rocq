From mathcomp Require Import all_ssreflect fingroup perm morphism automorphism.
From mathcomp Require Import quotient cyclic pgroup sylow gproduct.
From DiazPark Require Import GroupInfrastructure GroupQuotientInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Section PointwiseHom.
Variables dT rT : finGroupType.
Variable Z : {group rT}.
Hypothesis abZ : abelian Z.

Definition pointwise_hom_set : {set {dffun forall x : dT, rT}} :=
  [set f : {dffun forall x : dT, rT} | [forall x, f x \in Z] &&
    [forall x, [forall y, f (x * y) == f x * f y]]].

Lemma pointwise_hom_group_set : group_set pointwise_hom_set.
Proof.
apply/group_setP; split.
- rewrite inE; apply/andP; split; apply/forallP=> x.
    by rewrite oneg_ffun group1.
  by apply/forallP=> y; rewrite !oneg_ffun mul1g eqxx.
- move=> f g; rewrite !inE => /andP[/forallP fZ /forallP fM]
    /andP[/forallP gZ /forallP gM].
  apply/andP; split; apply/forallP=> x.
    by rewrite mulg_ffun groupM.
  apply/forallP=> y; apply/eqP.
  rewrite !mulg_ffun (eqP (forallP (fM x) y)) (eqP (forallP (gM x) y)).
  have c : commute (f y) (g x) := centsP abZ _ (fZ y) _ (gZ x).
  by rewrite -!mulgA; congr (_ * _); rewrite !mulgA c.
Qed.

Definition pointwise_hom_group : {group {dffun forall x : dT, rT}} :=
  Group pointwise_hom_group_set.

Lemma pointwise_hom_values f :
  f \in pointwise_hom_group -> forall x, f x \in Z.
Proof. by rewrite inE => /andP[/forallP]. Qed.

Lemma pointwise_hom_morph f :
  f \in pointwise_hom_group -> {morph f : x y / x * y}.
Proof.
rewrite inE => /andP[_ /forallP h] x y.
exact: (eqP (forallP (h x) y)).
Qed.

Lemma pointwise_hom_abelian : abelian pointwise_hom_group.
Proof.
apply/centsP=> f hf g hg; apply/ffunP=> x; rewrite !mulg_ffun.
exact: (centsP abZ _ (pointwise_hom_values hf x) _ (pointwise_hom_values hg x)).
Qed.

Lemma pointwise_hom_sub_product :
  pointwise_hom_group \subset setXn (fun _ : dT => Z).
Proof.
apply/subsetP=> f hf; apply/setXnP=> x.
exact: pointwise_hom_values hf x.
Qed.

Lemma constant_product_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group (setXn (fun _ : dT => Z)).
Proof.
move=> piZ; rewrite /pgroup in piZ *.
rewrite cardsXn big_const iter_muln cardT muln1 pnatX.
by rewrite piZ.
Qed.

Lemma pointwise_hom_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group pointwise_hom_group.
Proof.
move=> piZ; exact: pgroupS pointwise_hom_sub_product (constant_product_pgroup piZ).
Qed.
End PointwiseHom.

Section CentralDisplacement.
Variable gT : finGroupType.
Variables P Z : {group gT}.
Variable A : {group {perm gT}}.
Hypotheses (sZP : Z \subset P) (cZP : Z \subset 'C(P)).
Hypothesis sAP : A \subset Aut P.
Hypothesis fixesZ : forall a, a \in A -> {in Z, a =1 id}.
Hypothesis displacementZ :
  forall a, a \in A -> forall x, x \in P -> x^-1 * a x \in Z.

Definition central_displacement (a : {perm gT}) x := x^-1 * a x.

Lemma central_displacement_morph a (aA : a \in A) :
  {in P &, {morph central_displacement a : x y / x * y}}.
Proof.
move=> x y xP yP.
have aAut : a \in Aut P := subsetP sAP a aA.
have dc : commute (x^-1 * a x) y^-1.
  exact: (centsP cZP _ (displacementZ aA xP) _ (groupVr yP)).
rewrite /central_displacement invMg (morphicP (Aut_morphic aAut)) //.
by rewrite -!mulgA [x^-1 * (a x * a y)]mulgA [y^-1 * (_ * a y)]mulgA
  -dc -!mulgA.
Qed.

Canonical central_displacement_morphism a (aA : a \in A) :=
  Morphism (central_displacement_morph aA).

Lemma central_displacement_fix a (aA : a \in A) z (zZ : z \in Z) :
  central_displacement a z = 1.
Proof. by rewrite /central_displacement (fixesZ aA zZ) mulVg. Qed.

Lemma central_displacement_comp a b (aA : a \in A) (bA : b \in A) x (xP : x \in P) :
  central_displacement (a * b) x =
  central_displacement a x * central_displacement b x.
Proof.
have bAut : b \in Aut P := subsetP sAP b bA.
have dZ := displacementZ aA xP.
have dP : central_displacement a x \in P := subsetP sZP _ dZ.
have ax : a x = x * central_displacement a x.
  by rewrite /central_displacement mulgA mulgV mul1g.
have dc : commute (central_displacement a x) (central_displacement b x).
  exact: (centsP cZP _ dZ _ (subsetP sZP _ (displacementZ bA xP))).
rewrite /central_displacement permM {1}ax (morphicP (Aut_morphic bAut)) //.
rewrite (fixesZ bA dZ) mulgA.
exact: (esym dc).
Qed.

Lemma central_displacement_kernel a (aA : a \in A) :
  'ker (coset Z) \subset 'ker (central_displacement_morphism aA).
Proof.
rewrite ker_coset; apply/subsetP=> z zZ.
apply/morphpreP; split; first exact: subsetP sZP z zZ.
by apply/set1P; rewrite /= /central_displacement (fixesZ aA zZ) mulVg.
Qed.

Lemma central_displacement_normal : Z <| P.
Proof.
have cPZ : P \subset 'C(Z) by rewrite centsC.
by rewrite /normal sZP (subset_trans cPZ (cent_sub Z)).
Qed.

Definition quotient_displacement a (aA : a \in A) :
    {morphism P / Z >-> gT} :=
  factm_morphism (central_displacement_kernel aA)
    (normal_norm central_displacement_normal).

Lemma quotient_displacementE a (aA : a \in A) x (xP : x \in P) :
  quotient_displacement aA (coset Z x) = central_displacement a x.
Proof. exact: factmE. Qed.

Lemma quotient_displacement_values a (aA : a \in A) q :
  q \in P / Z -> quotient_displacement aA q \in Z.
Proof.
case/morphimP=> x _ xP ->.
by rewrite quotient_displacementE // /central_displacement; exact: (displacementZ aA xP).
Qed.

Definition delta_function (a : {perm gT}) :
    {dffun forall q : [subg P / Z], gT} :=
  [ffun q : [subg P / Z] => central_displacement a (repr (val q))].

Lemma quotient_representative_in_group (q : [subg P / Z]) : repr (val q) \in P.
Proof.
have hr : repr (val q) \in coset Z @*^-1 (P / Z).
  apply/morphpreP; split; first exact: repr_coset_norm.
  change (coset Z (repr (val q)) \in P / Z).
  by rewrite coset_reprK; exact: valP q.
by move: hr; rewrite quotientGK // central_displacement_normal.
Qed.

Lemma delta_functionE a (aA : a \in A) (q : [subg P / Z]) :
  delta_function a q = quotient_displacement aA (val q).
Proof.
rewrite /delta_function ffunE -(quotient_displacementE aA
  (quotient_representative_in_group q)).
by rewrite coset_reprK.
Qed.

Lemma delta_function_coset a (aA : a \in A) x (xP : x \in P) :
  delta_function a (Sub (coset Z x) (mem_quotient Z xP)) = central_displacement a x.
Proof. by rewrite delta_functionE quotient_displacementE. Qed.

Lemma delta_function_morph : {in A &, {morph delta_function : a b / a * b}}.
Proof.
move=> a b aA bA; apply/ffunP=> q.
rewrite mulg_ffun /delta_function !ffunE.
exact: (central_displacement_comp aA bA (quotient_representative_in_group q)).
Qed.

Canonical delta_morphism := Morphism delta_function_morph.

Lemma central_displacement_abelian : abelian Z.
Proof. exact: subset_trans cZP (centS sZP). Qed.

Lemma delta_function_in_hom a (aA : a \in A) :
  delta_function a \in pointwise_hom_group [the finGroupType of [subg P / Z]%type]
    central_displacement_abelian.
Proof.
rewrite inE; apply/andP; split; apply/forallP=> q.
  rewrite delta_functionE; exact: quotient_displacement_values (valP q).
apply/forallP=> r; apply/eqP; rewrite !delta_functionE /=.
exact: (morphM (quotient_displacement aA) (valP q) (valP r)).
Qed.

Lemma delta_embedding_injective : 'injm delta_morphism.
Proof.
apply/injmP=> a b aA bA hab.
apply: (eq_Aut (subsetP sAP a aA) (subsetP sAP b bA)).
move=> x xP.
have h := congr1 (fun f : {dffun forall q : [subg P / Z], gT} =>
  f (Sub (coset Z x) (mem_quotient Z xP))) hab.
rewrite !delta_function_coset // /central_displacement in h.
have h' := congr1 (fun z => x * z) h.
by rewrite !mulgA mulgV !mul1g in h'.
Qed.

Lemma delta_embedding_image :
  delta_morphism @* A \subset
  pointwise_hom_group [the finGroupType of [subg P / Z]%type] central_displacement_abelian.
Proof.
apply/subsetP=> _ /morphimP[a aA _ ->].
exact: delta_function_in_hom aA.
Qed.

Lemma delta_embedding_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group A.
Proof.
move=> piZ.
have piHom := pointwise_hom_pgroup
  [the finGroupType of [subg P / Z]%type] central_displacement_abelian piZ.
have piIm := pgroupS delta_embedding_image piHom.
by move: piIm; rewrite (injm_pgroup delta_embedding_injective).
Qed.

End CentralDisplacement.
