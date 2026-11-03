From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit MackeyStructures.
Import DPFusion.

(** Actual full double-coset spans for the fusion orbit category.
    With right conjugation x^t = t^-1*x*t and a double coset H*t*K,
    the apex is H intersect K^(t^-1). The right leg conjugates by t.
    No normality, saturation, centricity, or Mackey identity is assumed. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionMackey.

Section DoubleCosets.
Variable S : finGroupType.
Variables H K T : {group S}.

Definition double_coset (t : S) : {set S} := (H :* t) * K.

Lemma double_cosetP t x :
    reflect (exists h k, h \in H /\ k \in K /\ x = h * t * k)
      (x \in double_coset t).
Proof.
apply: (iffP mulsgP).
- move=> [a k /rcosetP[h Hh ->] Kk ->].
  by exists h, k.
- move=> [h [k [Hh [Kk ->]]]].
  exists (h * t) k => //; apply/rcosetP; by exists h.
Qed.

Definition double_coset_index := {X : {set S} | X \in double_coset @: T}.

Lemma double_coset_representative_exists (i : double_coset_index) :
    exists t : S, (t \in T) && (double_coset t == val i).
Proof.
have /imsetP[t Tt ht] := valP i.
by exists t; rewrite Tt -ht eqxx.
Qed.

Definition double_coset_representative (i : double_coset_index) : S :=
  xchoose (double_coset_representative_exists i).

Lemma double_coset_representative_mem (i : double_coset_index) :
    double_coset_representative i \in T.
Proof. exact: (andP (xchooseP (double_coset_representative_exists i))).1. Qed.

Lemma double_coset_representative_set (i : double_coset_index) :
    double_coset (double_coset_representative i) = val i.
Proof. apply/eqP; exact: (andP (xchooseP (double_coset_representative_exists i))).2. Qed.

End DoubleCosets.

Section InclusionSpans.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables H K : {group S}.

Definition inclusion_apex (t : S) : {group S} := (H :&: K :^ t^-1)%G.

Lemma inclusion_apex_left t : inclusion_apex t \subset H.
Proof. exact: subsetIl. Qed.

Lemma inclusion_apex_right t : inclusion_apex t :^ t \subset K.
Proof. rewrite sub_conjg; exact: subsetIr. Qed.

Definition inclusion_left (t : S) : DPFusionSystem.arrow F (inclusion_apex t) H :=
  Sub (DPFusion.inclusion (inclusion_apex_left t))
    (DPFusionSystem.inclusion_allowed F (inclusion_apex_left t)).

Definition inclusion_right (t : S) : DPFusionSystem.arrow F (inclusion_apex t) K :=
  Sub (DPFusion.conjugation (inclusion_apex_right t))
    (DPFusionSystem.conjugation_closed F (inclusion_apex_right t)).

Definition inclusion_span (t : S) :
    @mackey_span (DPFusionOrbit.orbit_category F) H K :=
  @MackeySpan (DPFusionOrbit.orbit_category F) H K (inclusion_apex t)
    (DPFusionOrbit.orbit_class (inclusion_left t))
    (DPFusionOrbit.orbit_class (inclusion_right t)).

Definition inclusion_term (T : {group S}) (i : double_coset_index H K T) :=
  inclusion_span (double_coset_representative i).

End InclusionSpans.

Section ImageFactorization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition inclusion_arrow (P Q : {group S}) (hPQ : P \subset Q) :
    DPFusionSystem.arrow F P Q :=
  Sub (DPFusion.inclusion hPQ) (DPFusionSystem.inclusion_allowed F hPQ).

Definition image_arrow (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    DPFusionSystem.arrow F P (DPFusion.image (val f)) :=
  Sub (DPFusion.to_image (val f)) (DPFusionSystem.image_closed (valP f)).

Definition inverse_arrow (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    DPFusionSystem.arrow F (DPFusion.image (val f)) P :=
  Sub (DPFusion.inverse (val f)) (DPFusionSystem.inverse_closed (valP f)).

Definition orbit_image_iso (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    @isomorphism (DPFusionOrbit.orbit_category F) P (DPFusion.image (val f)).
Proof.
refine (@Build_isomorphism (DPFusionOrbit.orbit_category F) P (DPFusion.image (val f))
  (DPFusionOrbit.orbit_class (image_arrow f))
  (DPFusionOrbit.orbit_class (inverse_arrow f)) _ _).
- cbn [Category.compose Category.identity DPFusionOrbit.orbit_category].
  rewrite DPFusionOrbit.orbit_compose_class.
  apply: congr1; apply: val_inj; exact: DPFusion.to_image_inverse.
- cbn [Category.compose Category.identity DPFusionOrbit.orbit_category].
  rewrite DPFusionOrbit.orbit_compose_class.
  apply: congr1; apply: val_inj; exact: DPFusion.inverse_to_image.
Defined.

Lemma orbit_image_factorization (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    Category.compose (iso_hom (orbit_image_iso f))
      (DPFusionOrbit.orbit_class (inclusion_arrow (DPFusion.image_sub (val f)))) =
    DPFusionOrbit.orbit_class f.
Proof.
cbn [Category.compose DPFusionOrbit.orbit_category orbit_image_iso iso_hom].
rewrite DPFusionOrbit.orbit_compose_class.
apply: congr1; apply: val_inj; exact: DPFusion.image_factorization.
Qed.

End ImageFactorization.

Section RawSpans.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T).

Definition raw_apex (t : S) : {group S} :=
  (DPFusion.image (val f) :&: (DPFusion.image (val g)) :^ t^-1)%G.

Lemma raw_apex_left (t : S) : raw_apex t \subset DPFusion.image (val f).
Proof. exact: subsetIl. Qed.

Lemma raw_apex_right (t : S) : (raw_apex t) :^ t \subset DPFusion.image (val g).
Proof. rewrite sub_conjg; exact: subsetIr. Qed.

Definition raw_left (t : S) : DPFusionSystem.arrow F (raw_apex t) P :=
  Sub (DPFusion.compose (DPFusion.inclusion (raw_apex_left t))
    (DPFusion.inverse (val f)))
    (DPFusionSystem.composition_closed
      (DPFusionSystem.inclusion_allowed F (raw_apex_left t))
      (DPFusionSystem.inverse_closed (valP f))).

Definition raw_right (t : S) : DPFusionSystem.arrow F (raw_apex t) Q :=
  Sub (DPFusion.compose (DPFusion.conjugation (raw_apex_right t))
    (DPFusion.inverse (val g)))
    (DPFusionSystem.composition_closed
      (DPFusionSystem.conjugation_closed F (raw_apex_right t))
      (DPFusionSystem.inverse_closed (valP g))).

Lemma raw_left_value t x : x \in raw_apex t ->
    DPFusion.map_fun (val (raw_left t)) x = DPFusion.inverse (val f) x.
Proof.
move=> Ax; rewrite /raw_left /= DPFusion.compose_in // DPFusion.inclusion_in //.
Qed.

Lemma raw_right_value t x : x \in raw_apex t ->
    DPFusion.map_fun (val (raw_right t)) x = DPFusion.inverse (val g) (x ^ t).
Proof.
move=> Ax; rewrite /raw_right /= DPFusion.compose_in // DPFusion.conjugation_in //.
Qed.

Lemma raw_left_triangle t x : x \in raw_apex t ->
    DPFusion.map_fun (val f) (DPFusion.map_fun (val (raw_left t)) x) = x.
Proof.
move=> Ax; rewrite raw_left_value // DPFusion.inverse_cancel_right //.
exact: (subsetP (raw_apex_left t) x Ax).
Qed.

Lemma raw_right_triangle t x : x \in raw_apex t ->
    DPFusion.map_fun (val g) (DPFusion.map_fun (val (raw_right t)) x) = x ^ t.
Proof.
move=> Ax; rewrite raw_right_value // DPFusion.inverse_cancel_right //.
move: Ax; by rewrite /raw_apex inE mem_conjgV => /andP[_].
Qed.

Definition raw_span (t : S) :
    @mackey_span (DPFusionOrbit.orbit_category F) P Q :=
  @MackeySpan (DPFusionOrbit.orbit_category F) P Q (raw_apex t)
    (DPFusionOrbit.orbit_class (raw_left t))
    (DPFusionOrbit.orbit_class (raw_right t)).

Lemma raw_span_commutes (t : S) : t \in T ->
    Category.compose (span_left (raw_span t)) (DPFusionOrbit.orbit_class f) =
    Category.compose (span_right (raw_span t)) (DPFusionOrbit.orbit_class g).
Proof.
move=> Tt; change
  (DPFusionOrbit.orbit_compose (DPFusionOrbit.orbit_class (raw_left t))
      (DPFusionOrbit.orbit_class f) =
   DPFusionOrbit.orbit_compose (DPFusionOrbit.orbit_class (raw_right t))
      (DPFusionOrbit.orbit_class g)).
rewrite !DPFusionOrbit.orbit_compose_class.
apply/DPFusionOrbit.orbit_class_eq; apply/exists_inP; exists t => //.
apply/forall_inP=> x Ax; apply/eqP.
change (DPFusion.compose (val (raw_right t)) (val g) x =
  (DPFusion.compose (val (raw_left t)) (val f) x) ^ t).
rewrite (@DPFusion.compose_in S (raw_apex t) Q T (val (raw_right t)) (val g) x Ax).
rewrite (@DPFusion.compose_in S (raw_apex t) P T (val (raw_left t)) (val f) x Ax).
by rewrite raw_left_triangle // raw_right_triangle.
Qed.

Definition raw_index :=
  [the finType of double_coset_index (DPFusion.image (val f)) (DPFusion.image (val g)) T].

Definition raw_term (i : raw_index) := raw_span (double_coset_representative i).

Lemma raw_term_commutes (i : raw_index) :
    Category.compose (span_left (raw_term i)) (DPFusionOrbit.orbit_class f) =
    Category.compose (span_right (raw_term i)) (DPFusionOrbit.orbit_class g).
Proof. apply: raw_span_commutes; exact: double_coset_representative_mem. Qed.

(** The arbitrary-arrow span has exactly the inclusion intersection as apex;
    its legs are the standard legs followed by the actual image inverses. *)
Lemma raw_left_image_factorization (t : S) :
    Category.compose
      (span_left (inclusion_span F (DPFusion.image (val f)) (DPFusion.image (val g)) t))
      (DPFusionOrbit.orbit_class
        (Sub (DPFusion.inverse (val f)) (DPFusionSystem.inverse_closed (valP f)))) =
    span_left (raw_span t).
Proof.
cbn [Category.compose DPFusionOrbit.orbit_category span_left inclusion_span raw_span].
rewrite DPFusionOrbit.orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Ax.
rewrite /DPFusionSystem.arrow_compose /inclusion_left /raw_left /=.
by rewrite !DPFusion.compose_in // !DPFusion.inclusion_in.
Qed.

Lemma raw_right_image_factorization (t : S) :
    Category.compose
      (span_right (inclusion_span F (DPFusion.image (val f)) (DPFusion.image (val g)) t))
      (DPFusionOrbit.orbit_class
        (Sub (DPFusion.inverse (val g)) (DPFusionSystem.inverse_closed (valP g)))) =
    span_right (raw_span t).
Proof.
cbn [Category.compose DPFusionOrbit.orbit_category span_right inclusion_span raw_span].
rewrite DPFusionOrbit.orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Ax.
rewrite /DPFusionSystem.arrow_compose /inclusion_right /raw_right /=.
by rewrite !DPFusion.compose_in // !DPFusion.conjugation_in.
Qed.

End RawSpans.

Section OrbitShape.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition fusion_mackey_shape : mackey_shape (DPFusionOrbit.orbit_category F) :=
  @MackeyShape (DPFusionOrbit.orbit_category F)
    (fun P Q T f g => raw_index (repr f) (repr g))
    (fun P Q T f g i => @raw_term S F P Q T (repr f) (repr g) i).

End OrbitShape.
End DPFusionMackey.

Print Assumptions DPFusionMackey.double_coset_representative_set.
Print Assumptions DPFusionMackey.raw_term_commutes.
Print Assumptions DPFusionMackey.fusion_mackey_shape.
Print Assumptions DPFusionMackey.orbit_image_iso.
Print Assumptions DPFusionMackey.orbit_image_factorization.
Print Assumptions DPFusionMackey.raw_left_image_factorization.
Print Assumptions DPFusionMackey.raw_right_image_factorization.
