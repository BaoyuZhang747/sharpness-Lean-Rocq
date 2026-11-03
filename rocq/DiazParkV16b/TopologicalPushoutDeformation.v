(** Genuine deformation descent through a topological attaching quotient. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalHomotopyInterval TopologicalCoproductHomotopy
  TopologicalPushoutCarrier TopologicalPushoutUniversal TopologicalParametrizedPushout.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalHomotopyInterval
  DPTopologicalCoproductHomotopy DPTopologicalPushoutCarrier
  DPTopologicalPushoutUniversal DPTopologicalParametrizedPushout.

Module DPTopologicalPushoutDeformation.
Section Deformation.
Variable Real : realType.
Variables A N X : topologicalType.
Variables (m : hom topological_category A N) (r : hom topological_category N A).
Variable hr : forall a, r (m a) = a.
Variable H : continuous_homotopy Real (continuous_identity N) (continuous_compose r m).
Variable hfix : forall t a, homotopy_map H (t,m a) = m a.
Variable j : hom topological_category A X.

Lemma retraction_commutes : compose m (compose r j) = compose j (@identity topological_category X).
Proof. apply: topological_hom_ext => a; change (j (r (m a)) = j a); by rewrite hr. Qed.

Definition pushout_retraction : hom topological_category (attaching_space m j) X :=
  attaching_desc_map retraction_commutes.

Lemma pushout_retraction_left n : pushout_retraction (attaching_left m j n) = j (r n).
Proof.
exact (congr1 (fun f : hom topological_category N X => f n)
  (attaching_desc_left retraction_commutes)).
Qed.
Lemma pushout_retraction_right x : pushout_retraction (attaching_right m j x) = x.
Proof.
exact (congr1 (fun f : hom topological_category X X => f x)
  (attaching_desc_right retraction_commutes)).
Qed.

Definition deformation_left : continuousType (N * unit_interval_space Real)%type (attaching_space m j).
Proof.
refine (@continuous_map _ _ (fun p => attaching_left m j (homotopy_map H (p.2,p.1))) _).
move=> p; apply: (@continuous_comp _ N (attaching_space m j)
  (fun q => homotopy_map H (q.2,q.1)) (attaching_left m j) p).
- apply: (@continuous_comp _ [the topologicalType of (unit_interval_space Real * N)%type]
    N (fun q => (q.2,q.1)) (homotopy_map H) p).
  + exact: product_swap_continuous.
  + exact: cts_fun.
- exact: attaching_left_continuous.
Defined.

Definition deformation_right : continuousType (X * unit_interval_space Real)%type (attaching_space m j).
Proof.
refine (@continuous_map _ _ (fun p => attaching_right m j p.1) _).
move=> p; apply: (@continuous_comp _ X (attaching_space m j) fst (attaching_right m j) p);
  [exact: cvg_fst | exact: attaching_right_continuous].
Defined.

Lemma deformation_commutes a t : deformation_left (m a,t) = deformation_right (j a,t).
Proof.
change (attaching_left m j (homotopy_map H (t,m a)) = attaching_right m j (j a)).
rewrite hfix; exact (congr1 (fun f : hom topological_category A (attaching_space m j) => f a)
  (attaching_commutes m j)).
Qed.

Definition pushout_deformation_parameter :=
  @parametrized_desc A N X (unit_interval_space Real) (attaching_space m j) m j
    deformation_left deformation_right deformation_commutes
    (@unit_interval_locally_compact Real) (@unit_interval_hausdorff Real).

Definition pushout_deformation_map : continuousType
    (unit_interval_space Real * attaching_space m j)%type (attaching_space m j).
Proof.
refine (@continuous_map _ _ (fun p => pushout_deformation_parameter (p.2,p.1)) _).
move=> p; apply: (@continuous_comp _ [the topologicalType of (attaching_space m j * unit_interval_space Real)%type]
  (attaching_space m j) (fun q => (q.2,q.1)) pushout_deformation_parameter p);
  [exact: product_swap_continuous | exact: cts_fun].
Defined.

Lemma pushout_deformation_left t n :
  pushout_deformation_map (t,attaching_left m j n) = attaching_left m j (homotopy_map H (t,n)).
Proof. exact: parametrized_desc_left. Qed.
Lemma pushout_deformation_right t x :
  pushout_deformation_map (t,attaching_right m j x) = attaching_right m j x.
Proof. exact: parametrized_desc_right. Qed.

Definition pushout_deformation : continuous_homotopy Real
  (continuous_identity (attaching_space m j))
  (continuous_compose pushout_retraction (attaching_right_map m j)).
Proof.
refine (@ContinuousHomotopy Real _ _ _ _ pushout_deformation_map _ _).
- move=> z; case: (attaching_cases z) => [[n <-]|[x <-]].
  + by rewrite pushout_deformation_left homotopy_start.
  + exact: pushout_deformation_right.
- move=> z; case: (attaching_cases z) => [[n <-]|[x <-]].
  + rewrite pushout_deformation_left homotopy_end.
    change (attaching_left m j (m (r n)) = attaching_right m j (pushout_retraction (attaching_left m j n))).
    rewrite pushout_retraction_left.
    exact (congr1 (fun f : hom topological_category A (attaching_space m j) => f (r n))
      (attaching_commutes m j)).
  + rewrite pushout_deformation_right.
    change (attaching_right m j x = attaching_right m j (pushout_retraction (attaching_right m j x))).
    by rewrite pushout_retraction_right.
Defined.

Lemma pushout_deformation_fixed t x :
  homotopy_map pushout_deformation (t,attaching_right m j x) = attaching_right m j x.
Proof. exact: pushout_deformation_right. Qed.

End Deformation.
End DPTopologicalPushoutDeformation.
