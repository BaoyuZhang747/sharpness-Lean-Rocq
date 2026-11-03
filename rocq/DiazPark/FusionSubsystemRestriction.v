From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionCentralizerMaps
  FusionSubsystemOrbit FusionMackeyShape FusionStableElements MackeyPair MackeyPairDiagrams.
Import DPFusion DPFusionSubgroup DPFusionSubsystem DPFusionStable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFusionSubsystemRestriction.
Section Subgroups.
Variable S : finGroupType.
Variable C : {group S}.
Local Notation T := [subg C]%type.

Lemma ambient_top : ambient [set: T]%G = C.
Proof. apply val_inj. exact (im_sgval C). Qed.

Lemma ambient_subset (P Q : {group T}) : P \subset Q -> ambient P \subset ambient Q.
Proof. exact (@morphimS _ _ _ sgval P Q). Qed.

Lemma ambient_subgroup_exists (P : {group S}) : P \subset C ->
    exists Q : {group T}, ambient Q = P.
Proof.
  intro hP. exists (subg C @* P)%G. apply val_inj. exact (subgmK hP).
Qed.

Lemma ambient_centralizer_witness (P : {group T}) :
    ~~ ('C(P) \subset P) ->
    ~~ (ambient [set: T]%G :&: 'C(ambient P) \subset ambient P).
Proof.
  move=> /subsetPn[x hxC hxP]. apply/subsetPn. exists (val x).
  - apply/setIP. split. exact (ambient_mem (in_setT x)).
    apply/centP. intros y hy. have hyP := ambient_repr hy.
    have he := ambient_subgK hy.
    have hcomm := (centP hxC) (subg C y) hyP.
    change ((x * subg C y)%g = (subg C y * x)%g) in hcomm.
    have hv := congr1 (fun z : T => val z) hcomm.
    change ((val x * val (subg C y))%g = (val (subg C y) * val x)%g) in hv.
    by rewrite he in hv.
  - apply/negP. intro hx. have hp := ambient_repr hx.
    rewrite sgvalK in hp. exact (negP hxP hp).
Qed.

End Subgroups.

Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (lift f).
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Definition restricted_pair := pair_restrict M (orbit_functor hH).

Lemma ambient_inclusion (P Q : {group T}) (h : P \subset Q) :
    ambient_arrow hH (inclusion H h) = inclusion F (ambient_subset h).
Proof.
  apply DPFusionSystem.arrow_ext. intros x hx.
  have hxp := ambient_repr hx. have he := ambient_subgK hx.
  rewrite -he. change (lift (DPFusion.inclusion h) (val (subg C x)) =
    DPFusion.inclusion (ambient_subset h) (val (subg C x))).
  by rewrite liftE // !DPFusion.inclusion_in ?ambient_mem.
Qed.

Lemma restricted_top_formula (P : {group T}) (x : pair_value restricted_pair [set: T]%G) :
    restrict_top restricted_pair P x =
    pair_pull M (DPFusionOrbit.orbit_class (inclusion F (ambient_subset (subsetT P)))) x.
Proof.
  change (pair_pull M (orbit_map hH (DPFusionOrbit.orbit_class (inclusion H (subsetT P)))) x =
    pair_pull M (DPFusionOrbit.orbit_class (inclusion F (ambient_subset (subsetT P)))) x).
  by rewrite orbit_map_class ambient_inclusion.
Qed.

End Restriction.
End DPFusionSubsystemRestriction.
