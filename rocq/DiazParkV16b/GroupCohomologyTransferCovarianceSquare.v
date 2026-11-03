(** Transfer covariance for explicitly named commuting subgroup isomorphisms. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyHomogeneousExtension
  GroupCohomologyHomogeneousRestriction GroupCohomologyTransferNative
  GroupCohomologyTransferCovarianceMaps GroupCohomologyTransferCovariance
  GroupCohomologyOrbitCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousExtension DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferCovarianceMaps
  DPGroupCohomologyTransferCovariance DPGroupCohomologyOrbitCoefficient.
Local Open Scope group_scope.

Module DPGroupCohomologyTransferCovarianceSquare.
Section NamedImages.
Variable R : comPzRingType.
Variables G K : finGroupType.
Variables P Q : {group G}.
Hypothesis hPQ : P \subset Q.
Variable e : {morphism Q >-> K}.
Hypothesis he : 'injm e.
Variables P' Q' : {group K}.
Hypothesis hP'Q' : P' \subset Q'.
Variables (eP : {morphism [set: [subg P]] >-> [subg P']})
  (eQ : {morphism [set: [subg Q]] >-> [subg Q']}).
Hypotheses (hP' : (e @* P)%G = P') (hQ' : (e @* Q)%G = Q').
Hypotheses (hEP : forall x : [subg P], val (eP x) = e (val x))
  (hEQ : forall x : [subg Q], val (eQ x) = e (val x)).
Variable A : lmodType R.

Theorem transfer_covariance_named n :
  module_hom_comp (pull A eP n) (transfer A hPQ n) =
    module_hom_comp (transfer A hP'Q' n) (pull A eQ n).
Proof.
subst P'; subst Q'.
have ep : eP = lower_hom hPQ e.
  apply group_morphism_ext=> x; apply val_inj; exact: hEP.
have eq : eQ = upper_hom e.
  apply group_morphism_ext=> x; apply val_inj; exact: hEQ.
rewrite ep eq.
exact: transfer_covariance_image.
Qed.
End NamedImages.

Section Square.
Variable R : comPzRingType.
Variables G K : finGroupType.
Variables P Q : {group G}.
Hypothesis hPQ : P \subset Q.
Variables P' Q' : {group K}.
Hypothesis hP'Q' : P' \subset Q'.
Variables (eP : {morphism [set: [subg P]] >-> [subg P']})
  (eQ : {morphism [set: [subg Q]] >-> [subg Q']}).
Hypotheses (heP : bijective eP) (heQ : bijective eQ).
Hypothesis hcomm : forall x : [subg P],
  val (eQ (subgroup_nested_hom hPQ x)) = val (eP x).

Definition ambient_value := subgroup_hom_vertex_extension eQ.

Lemma ambient_value_subgroup (x : [subg Q]) :
  ambient_value (val x) = val (eQ x).
Proof. exact: subgroup_hom_vertex_extension_subgroup. Qed.

Definition ambient_morphism : {morphism Q >-> K}.
Proof.
apply: (Morphism (mfun := ambient_value))=> x y hx hy.
have ht := subgroup_hom_vertex_extension_equivariant eQ (Sub x hx) y.
change (ambient_value (x * y) = val (eQ (Sub x hx)) * ambient_value y) in ht.
by rewrite ht -(ambient_value_subgroup (Sub x hx)).
Defined.

Lemma ambient_morphism_upper (x : [subg Q]) :
  ambient_morphism (val x) = val (eQ x).
Proof. exact: ambient_value_subgroup. Qed.

Lemma ambient_morphism_lower (x : [subg P]) :
  ambient_morphism (val x) = val (eP x).
Proof.
have ht := ambient_morphism_upper (subgroup_nested_hom hPQ x).
rewrite subgroup_nested_hom_val hcomm in ht; exact ht.
Qed.

Lemma ambient_morphism_injm : 'injm ambient_morphism.
Proof.
apply/injmP=> x y hx hy hxy.
have hexy : eQ (Sub x hx) = eQ (Sub y hy).
  apply val_inj; rewrite -!ambient_morphism_upper; exact hxy.
have heq := bij_inj heQ hexy.
exact (congr1 (fun z : [subg Q] => val z) heq).
Qed.

Lemma ambient_image_upper : (ambient_morphism @* Q)%G = Q'.
Proof.
apply val_inj; apply/setP=> y; apply/idP/idP.
- move/morphimP=> [x hx _ ->].
  rewrite (ambient_morphism_upper (Sub x hx)); exact: valP.
- move=> hy; have [i _ hi] := heQ.
  pose x := i (Sub y hy); have hx : eQ x = Sub y hy := hi _.
  apply/morphimP; exists (val x); [exact: valP | exact: valP |].
  rewrite ambient_morphism_upper hx; reflexivity.
Qed.

Lemma ambient_image_lower : (ambient_morphism @* P)%G = P'.
Proof.
apply val_inj; apply/setP=> y; apply/idP/idP.
- move/morphimP=> [x hx hPx ->].
  rewrite (ambient_morphism_lower (Sub x hPx)); exact: valP.
- move=> hy; have [i _ hi] := heP.
  pose x := i (Sub y hy); have hx : eP x = Sub y hy := hi _.
  apply/morphimP; exists (val x).
  + exact: subsetP hPQ _ (valP x).
  + exact: valP.
  + rewrite ambient_morphism_lower hx; reflexivity.
Qed.

Variable A : lmodType R.

Theorem transfer_isomorphism_square n :
  module_hom_comp (pull A eP n) (transfer A hPQ n) =
    module_hom_comp (transfer A hP'Q' n) (pull A eQ n).
Proof.
exact (@transfer_covariance_named R G K P Q hPQ ambient_morphism
  ambient_morphism_injm P' Q' hP'Q' eP eQ ambient_image_lower ambient_image_upper
  (fun x => esym (ambient_morphism_lower x))
  (fun x => esym (ambient_morphism_upper x)) A n).
Qed.

End Square.
End DPGroupCohomologyTransferCovarianceSquare.
