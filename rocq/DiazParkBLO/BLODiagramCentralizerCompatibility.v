(** Exact interfaces relating the constructed centraliser linking system
    to its ambient linking system and to the enlarged full subcategory. *)
From mathcomp Require Import all_boot all_fingroup center abelian pgroup boolp.
From DiazPark Require Import Category CategoryReindex FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem.
From DiazParkBLO Require Import BLODiagram BLODiagramCentralizerBase
  BLODiagramCenterElements BLODiagramCentralizerSystem.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPFusionOrbit DPFusionCentralizerCoverProjection
  DPBLODiagram DPBLOCentralizerBase DPBLOCentralizerSystem DPBLOCenterElements.
Local Open Scope group_scope.

Module DPBLOCentralizerCompatibility.
Section Compatibility.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation Obj := (centric_object CF).
Local Notation co := (@centralizer_point S F p pS sat B).
Local Notation ao := (@ambient_object S F p pS sat B).
Local Notation CL := (@centralizer_linking_system S F L p pS sat B).
Local Notation J := (@centralizer_inclusion S F L p pS sat B).

Definition hom_of_fixes (P Q : Obj) (f : DPCentricLinking.linking_hom L (ao P) (ao Q))
    (hf : {in E, val (DPCentricLinking.linking_projection L f) =1 id}) :
    DPCentricLinking.linking_hom CL P Q.
Proof.
refine (@Arrow S F L E (co P) (co Q) f _).
apply DPFusionSystem.arrow_ext=> x hx.
rewrite DPFusion.compose_in // !alpha_to_carrierE // !centralizer_point_alphaE //.
exact: hf hx.
Defined.

Lemma hom_of_fixes_underlying (P Q : Obj)
    (f : DPCentricLinking.linking_hom L (ao P) (ao Q))
    (hf : {in E, val (DPCentricLinking.linking_projection L f) =1 id}) :
    underlying_hom (hom_of_fixes hf) = f.
Proof. reflexivity. Qed.

Lemma hom_fixing_exact (P Q : Obj) (f : DPCentricLinking.linking_hom L (ao P) (ao Q)) :
    (exists g : DPCentricLinking.linking_hom CL P Q, underlying_hom g = f) <->
    {in E, val (DPCentricLinking.linking_projection L f) =1 id}.
Proof.
split.
- move=> [g <-]; exact: centralizer_hom_fixes.
- move=> hf; exists (hom_of_fixes hf); reflexivity.
Qed.

Lemma centralizer_category_reindexed :
    DPCentricLinking.linking_category CL = reindexed_category (enlarged_category L E) co.
Proof. reflexivity. Qed.

Lemma centralizer_inclusion_reindexed : J = reindex_inclusion (enlarged_category L E) co.
Proof. reflexivity. Qed.

Definition ambient_functor : functor (DPCentricLinking.linking_category CL)
    (DPCentricLinking.linking_category L) := functor_comp J (forgetful L E).

Lemma ambient_functor_object P : fobj ambient_functor P = ao P.
Proof. reflexivity. Qed.
Lemma ambient_functor_arrow P Q (f : DPCentricLinking.linking_hom CL P Q) :
    fmap ambient_functor f = underlying_hom f.
Proof. reflexivity. Qed.

Lemma ambient_functor_distinguished (P : Obj) (x : [subg (val P)]) :
    fmap ambient_functor (DPCentricLinking.distinguished CL x) =
    @DPCentricLinking.distinguished S F L (ao P) (subgroup_up x).
Proof. exact: centralizer_distinguished_underlying. Qed.

Lemma ambient_projection (P Q : Obj) (f : DPCentricLinking.linking_hom CL P Q) :
    DPFusionSubgroup.lift (val (DPCentricLinking.linking_projection CL f)) =
    val (DPCentricLinking.linking_projection L (fmap ambient_functor f)).
Proof. exact: centralizer_projection_lift. Qed.
End Compatibility.
End DPBLOCentralizerCompatibility.
