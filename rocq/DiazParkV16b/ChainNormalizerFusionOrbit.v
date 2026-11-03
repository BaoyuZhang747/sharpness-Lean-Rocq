(** Actual orbit maps for the chain-normalizer fusion system.  The collection
    consists of subgroups whose ambient images are F-centric; it is not
    identified with all centric objects of the local fusion system. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionCentralizerMaps FusionSubsystemOrbit FusionSubsystemFaithful
  FusionCentricBasics.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainNormalizer
  ChainNormalizerFusionModel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPFusionOrbit DPLinkingChains DPNormalizerChain
  DPChainNormalizerFusionModel.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPChainNormalizerFusionOrbit.
Section Orbit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].
Local Notation H := (local_system L c).
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.

Definition ambient_orbit_functor : functor (orbit_category H) (orbit_category F) :=
  @DPFusionSubsystem.orbit_functor S F (normalizer c) H
    (@local_ambient_allowed S F L c p sat).

Lemma ambient_orbit_class (P Q : {group N}) (f : DPFusionSystem.arrow H P Q) :
  fmap ambient_orbit_functor (orbit_class f) =
  orbit_class (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) f).
Proof. exact: DPFusionSubsystem.orbit_map_class. Qed.

Lemma ambient_orbit_faithful (P Q : {group N}) :
  injective (@fmap _ _ ambient_orbit_functor P Q).
Proof. exact: DPFusionSubsystemFaithful.orbit_map_injective. Qed.

Lemma ambient_centralizer (P : {group N}) :
  (ambient 'C(P)%G : {set S}) = normalizer c :&: 'C(ambient P).
Proof.
change (sgval @* 'C(P) = normalizer c :&: 'C(sgval @* P)).
by rewrite (injm_cent (injm_sgval _) (subsetT P)) im_sgval.
Qed.

Lemma ambient_conjugate (P Q : {group N}) :
  DPFusionSystem.conjugate H P Q ->
  DPFusionSystem.conjugate F (ambient P) (ambient Q).
Proof.
exact (@DPFusionSubsystem.ambient_conjugate S F (normalizer c) H
  (@local_ambient_allowed S F L c p sat) P Q).
Qed.

Lemma ambient_centric_local_centric (P : {group N}) :
  DPFusionSystem.centric F (ambient P) -> DPFusionSystem.centric H P.
Proof.
move=> hP; apply/forallP=> Q; apply/implyP=> hPQ.
have hc : 'C(ambient Q) \subset ambient Q :=
  implyP (forallP hP (ambient Q)) (ambient_conjugate hPQ).
apply/subsetP=> x Cx.
have hx : val x \in ambient 'C(Q)%G := ambient_mem Cx.
rewrite ambient_centralizer in hx.
have h := ambient_repr (subsetP hc _ (setIP hx).2).
by rewrite sgvalK in h.
Qed.

Definition ambient_centric (P : {group N}) := DPFusionSystem.centric F (ambient P).
Definition collection_object := {P : {group N} | ambient_centric P}.

Lemma ambient_centric_conjugate (P Q : {group N}) :
  DPFusionSystem.conjugate H P Q -> ambient_centric P -> ambient_centric Q.
Proof.
move=> hPQ; exact: DPFusionCentricBasics.centric_conjugate (ambient_conjugate hPQ).
Qed.

Lemma ambient_centric_overgroup (P Q : {group N}) :
  P \subset Q -> ambient_centric P -> ambient_centric Q.
Proof.
move=> hPQ; apply: DPFusionCentricBasics.centric_overgroup.
exact: morphimS hPQ.
Qed.

Definition collection_category : category.
Proof.
refine (@Build_category collection_object
  (fun P Q => orbit_hom H (val P) (val Q))
  (fun P => orbit_identity H (val P))
  (fun P Q R f g => @orbit_compose _ H (val P) (val Q) (val R) f g) _ _ _).
- move=> P Q f; exact: (@Category.compose_id_left (orbit_category H) (val P) (val Q) f).
- move=> P Q f; exact: (@Category.compose_id_right (orbit_category H) (val P) (val Q) f).
- move=> P Q R T f g h.
  exact: (@Category.compose_assoc (orbit_category H) (val P) (val Q) (val R) (val T) f g h).
Defined.

Definition collection_local_object (P : collection_object) : centric_object H :=
  Sub (val P) (ambient_centric_local_centric (valP P)).

Definition collection_local_functor : functor collection_category (centric_orbit_category H).
Proof.
refine (@Build_functor collection_category (centric_orbit_category H)
  collection_local_object (fun P Q f => f) _ _); by [].
Defined.

Definition collection_ambient_object (P : collection_object) : centric_object F :=
  Sub (ambient (val P)) (valP P).

Definition collection_ambient_functor : functor collection_category (centric_orbit_category F).
Proof.
refine (@Build_functor collection_category (centric_orbit_category F)
  collection_ambient_object (fun P Q f => fmap ambient_orbit_functor f) _ _).
- move=> P; exact (fmap_id ambient_orbit_functor (val P)).
- move=> P Q R f g; exact (fmap_compose ambient_orbit_functor f g).
Defined.

Lemma collection_ambient_class (P Q : collection_object)
    (f : DPFusionSystem.arrow H (val P) (val Q)) :
  fmap collection_ambient_functor (orbit_class f) =
  orbit_class (DPFusionSubsystem.ambient_arrow (@local_ambient_allowed S F L c p sat) f).
Proof. exact: ambient_orbit_class. Qed.

Lemma collection_ambient_faithful (P Q : collection_object) :
  injective (@fmap _ _ collection_ambient_functor P Q).
Proof. exact: ambient_orbit_faithful. Qed.

Lemma collection_local_full (P Q : collection_object)
    (f : hom (centric_orbit_category H)
      (collection_local_object P) (collection_local_object Q)) :
  exists g : hom collection_category P Q, fmap collection_local_functor g = f.
Proof. by exists f. Qed.

Lemma collection_local_faithful (P Q : collection_object) :
  injective (@fmap _ _ collection_local_functor P Q).
Proof. by move=> f g. Qed.

End Orbit.
End DPChainNormalizerFusionOrbit.
