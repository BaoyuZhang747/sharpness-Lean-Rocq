From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionReceptivity FusionCentralizerMaps FusionCentralizer
  FusionCentralizerReceptive.
Import DPFusion DPFusionSubgroup DPFusionCentralizer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerCompression.
Section Compression.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.

Lemma inverse_image (A B : {group S}) (f : DPFusion.map A B) :
  DPFusion.image (DPFusion.inverse f) = A.
Proof.
apply: val_inj; change (DPFusion.map_morphism (DPFusion.inverse f) @* DPFusion.image f = A).
by rewrite /DPFusion.inverse DPFusion.of_morphism_image im_invm.
Qed.

Lemma restricted_image (A B D : {group S}) (f : DPFusion.map A B) (sDA : D \subset A) :
  DPFusion.image (DPFusion.restrict f sDA) = (DPFusion.map_morphism f @* D)%G.
Proof.
apply: val_inj; change (DPFusion.map_morphism (DPFusion.restrict f sDA) @* D = DPFusion.map_morphism f @* D).
by rewrite /DPFusion.restrict DPFusion.of_morphism_image im_restrm.
Qed.

Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.
Variables (P : {group T}) (B : {group S}).
Variable theta : DPFusion.map (joint P) B.
Hypothesis htheta : DPFusionSystem.allowed F theta.
Hypothesis onto : DPFusion.image theta = B.

Definition imageE := DPFusion.image (DPFusion.restrict theta (joint_right P)).

Lemma imageE_eq : imageE = (DPFusion.map_morphism theta @* E)%G.
Proof. exact: restricted_image. Qed.

Lemma image_joint_centralizes : B \subset 'C(imageE).
Proof.
have h := morphim_cents (DPFusion.map_morphism theta)
  (DPFusionCentralizerReceptive.joint_sub abE P).
change (is_true (DPFusion.image theta \subset 'C(DPFusion.map_morphism theta @* E))) in h.
have ee := congr1 (fun A : {group S} => (A : {set S})) imageE_eq.
by rewrite onto -ee in h.
Qed.

Lemma inverse_E_centralizer_extension :
  exists g : DPFusion.map 'C(imageE)%G C,
    DPFusionSystem.allowed F g /\ {in E, forall e, g (theta e) = e}.
Proof.
pose e0 := DPFusion.restrict theta (joint_right P).
pose delta := DPFusion.inverse e0.
have hd : DPFusionSystem.allowed F delta :=
  DPFusionSystem.inverse_closed (DPFusionSystem.restriction_allowed (joint_right P) htheta).
have [eta [heta hext]] := DPFusionSaturation.saturation_extension sat hd (inverse_image e0) hE.
pose g := DPFusionReceptivity.centralizer_extension (inverse_image e0) hext.
have hg : DPFusionSystem.allowed F g.
  apply: DPFusionSystem.corestriction_allowed.
  exact: DPFusionSystem.restriction_allowed _ heta.
exists g; split=> //; move=> e Ee.
have Ce : theta e \in 'C(imageE).
  exact: (subsetP image_joint_centralizes _ (DPFusion.map_into theta (subsetP (joint_right P) e Ee))).
have Ie : theta e \in imageE.
  have h := DPFusion.image_mem e0 Ee.
  by rewrite /e0 DPFusion.restrict_in in h.
rewrite /g DPFusionReceptivity.centralizer_extensionE // hext //.
change (DPFusion.inverse e0 (theta e) = e).
rewrite -(DPFusion.restrict_in theta (joint_right P) Ee).
exact: DPFusion.inverse_cancel.
Qed.

End Compression.
End DPFusionCentralizerCompression.






