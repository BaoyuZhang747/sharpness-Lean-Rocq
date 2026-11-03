(** The actual native cohomology pull/push pair on the fusion orbit category.
    This construction has no assumed transfer, functoriality or inner law. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  FusionMaps FusionSystems FusionOrbit FusionOrbitRanks MackeyPair.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPushBase
  GroupCohomologyMackeyPushIso GroupCohomologyMackeyPushComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion GRing.Theory DPGroupCohomologyOrbitCoefficient DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyPushIso DPGroupCohomologyMackeyPushComposition.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologyMackeyPair.
Section Pair.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation V := (@DPGroupCohomologyOrbitCoefficient.value S R A n).
Local Notation OC := (DPFusionOrbit.orbit_category F).

Lemma raw_push_target_inner (P Q : {group S}) (a b : DPFusionSystem.arrow F P Q) :
  DPFusionOrbit.target_inner a b -> raw_push A n b = raw_push A n a.
Proof.
move=> /exists_inP[r Qr /forall_inP hr].
have Nr : r \in 'N(Q) := subsetP (normG Q) r Qr.
have hQQ : (Q :^ r)%g \subset Q by rewrite (normP Nr).
pose c : DPFusionSystem.arrow F Q Q := Sub (DPFusion.conjugation hQQ)
  (DPFusionSystem.conjugation_closed F hQQ).
have hc : DPFusionOrbit.target_inner (DPFusionSystem.arrow_identity F Q) c.
  apply/exists_inP; exists r => //; apply/forall_inP => x Qx; apply/eqP.
  change (DPFusion.conjugation hQQ x = (DPFusion.identity Q x ^ r)%g).
  by rewrite DPFusion.conjugation_in // DPFusion.identity_in.
have hb : b = DPFusionSystem.arrow_compose a c.
  apply DPFusionSystem.arrow_ext => x Px.
  have he := eqP (hr x Px).
  change (DPFusion.map_fun (val b) x = (DPFusion.map_fun (val a) x ^ r)%g) in he.
  change (DPFusion.map_fun (val b) x =
    DPFusion.compose (val a) (DPFusion.conjugation hQQ) x).
  by rewrite DPFusion.compose_in // DPFusion.conjugation_in ?DPFusion.map_into.
rewrite hb raw_push_compose (raw_push_inner A n hc).
apply module_hom_ext => z; reflexivity.
Qed.

Definition orbit_push (P Q : {group S}) (a : DPFusionOrbit.orbit_hom F P Q) :
    module_hom (V P) (V Q) := raw_push A n (repr a).

Lemma orbit_push_class (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
  orbit_push (DPFusionOrbit.orbit_class a) = raw_push A n a.
Proof. symmetry; exact: raw_push_target_inner (DPFusionOrbit.representative_related a). Qed.

Lemma orbit_push_identity (P : {group S}) :
  orbit_push (DPFusionOrbit.orbit_identity F P) = module_hom_id (V P).
Proof. rewrite /DPFusionOrbit.orbit_identity orbit_push_class; exact: raw_push_identity. Qed.

Lemma orbit_push_compose (P Q T : {group S})
    (a : DPFusionOrbit.orbit_hom F P Q) (b : DPFusionOrbit.orbit_hom F Q T) :
  orbit_push (DPFusionOrbit.orbit_compose a b) = module_hom_comp (orbit_push a) (orbit_push b).
Proof.
move: a; apply: quotW => a; move: b; apply: quotW => b.
rewrite DPFusionOrbit.orbit_compose_class !orbit_push_class; exact: raw_push_compose.
Qed.

Lemma orbit_push_pull_equal_rank (P Q : {group S}) (hcard : #|P| = #|Q|)
    (a : DPFusionOrbit.orbit_hom F P Q) (z : V Q) :
  module_hom_fun (orbit_push a) (module_hom_fun (orbit_pull A n a) z) = z.
Proof.
change (module_hom_fun (raw_push A n (repr a))
    (module_hom_fun (raw_pull A n (repr a)) z) = z).
rewrite raw_push_pull_index (DPFusionRanks.raw_equal_rank_image (repr a) hcard).
by rewrite indexgg mulr1n.
Qed.

Lemma orbit_pull_push_iso (P Q : {group S}) (e : @isomorphism OC P Q) (z : V Q) :
  module_hom_fun (orbit_pull A n (iso_hom e)) z = module_hom_fun (orbit_push (iso_inv e)) z.
Proof.
have hcard : #|P| = #|Q|.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    [exact: DPFusionRanks.orbit_rank_le (iso_hom e) |
     exact: DPFusionRanks.orbit_rank_le (iso_inv e)].
have he := congr1 (fun u => module_hom_fun u
    (module_hom_fun (orbit_pull A n (iso_hom e)) z))
  (orbit_push_compose (iso_hom e) (iso_inv e)).
have hi : DPFusionOrbit.orbit_compose (iso_hom e) (iso_inv e) =
    DPFusionOrbit.orbit_identity F P := iso_hom_inv e.
rewrite hi orbit_push_identity in he.
change (module_hom_fun (orbit_pull A n (iso_hom e)) z =
  module_hom_fun (orbit_push (iso_inv e))
    (module_hom_fun (orbit_push (iso_hom e))
      (module_hom_fun (orbit_pull A n (iso_hom e)) z))) in he.
by rewrite orbit_push_pull_equal_rank // in he.
Qed.

Definition native_cohomology_pair : mackey_pair R OC.
Proof.
refine (@MackeyPair R OC V
  (fun P Q a => module_hom_to_linear (orbit_pull A n a))
  (fun P Q a => module_hom_to_linear (orbit_push a)) _ _ _ _ _).
- move=> P z; change (module_hom_fun (orbit_pull A n (DPFusionOrbit.orbit_identity F P)) z = z).
  by rewrite orbit_pull_identity.
- move=> P z; change (module_hom_fun (orbit_push (DPFusionOrbit.orbit_identity F P)) z = z).
  by rewrite orbit_push_identity.
- move=> P Q T a b z.
  change (module_hom_fun (orbit_pull A n (DPFusionOrbit.orbit_compose a b)) z =
    module_hom_fun (orbit_pull A n a) (module_hom_fun (orbit_pull A n b) z)).
  by rewrite orbit_pull_compose.
- move=> P Q T a b z.
  change (module_hom_fun (orbit_push (DPFusionOrbit.orbit_compose a b)) z =
    module_hom_fun (orbit_push b) (module_hom_fun (orbit_push a) z)).
  by rewrite orbit_push_compose.
- move=> P Q e z; exact: orbit_pull_push_iso.
Defined.

Lemma native_pair_value (P : {group S}) : pair_value native_cohomology_pair P = V P.
Proof. reflexivity. Qed.

Lemma native_pair_pull_class (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) z :
  pair_pull native_cohomology_pair (DPFusionOrbit.orbit_class a) z =
    module_hom_fun (raw_pull A n a) z.
Proof. change (module_hom_fun (orbit_pull A n (DPFusionOrbit.orbit_class a)) z = module_hom_fun (raw_pull A n a) z).
  by rewrite orbit_pull_class. Qed.

Lemma native_pair_push_class (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) z :
  pair_push native_cohomology_pair (DPFusionOrbit.orbit_class a) z =
    module_hom_fun (raw_push A n a) z.
Proof. change (module_hom_fun (orbit_push (DPFusionOrbit.orbit_class a)) z = module_hom_fun (raw_push A n a) z).
  by rewrite orbit_push_class. Qed.

End Pair.
End DPGroupCohomologyMackeyPair.

