(** The restricted Mackey input is the literal inclusion double-coset
    identity, retaining precisely centric intersection subgroups. The
    all-arrow pullback identity below follows by actual image isomorphisms;
    no extension of the coefficient pair to noncentric objects is used. *)
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFinitePullbacks
  FusionMaps FusionSystems FusionOrbit FusionMackeyShape FusionCentricBasics
  FusionFiniteCategory FusionCentricPullbacks MackeyStructures MackeyPair.
Import GRing.Theory DPFusionSystem DPFusionOrbit DPFusionMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricRestricted.
Section Geometry.
Variable S : finGroupType.
Variable F : system S.
Local Notation C := (centric_orbit_category F).

Definition centric_image (P T : C) (f : arrow F (val P) (val T)) : C :=
  Sub (DPFusion.image (val f))
    (DPFusionCentricBasics.centric_image (valP f) (valP P)).

Definition centric_image_iso (P T : C) (f : arrow F (val P) (val T)) :
    @isomorphism C P (@centric_image P T f) :=
  @Build_isomorphism C P (@centric_image P T f)
    (iso_hom (orbit_image_iso f)) (iso_inv (orbit_image_iso f))
    (iso_hom_inv (orbit_image_iso f)) (iso_inv_hom (orbit_image_iso f)).

Definition centric_inclusion (P T : C) (h : val P \subset val T) : hom C P T :=
  orbit_class (inclusion_arrow F h).

Definition inclusion_index (P Q T : C) :=
  {i : double_coset_index (val P) (val Q) (val T) |
    centric F (inclusion_apex (val P) (val Q) (double_coset_representative i))}.

Definition inclusion_term (P Q T : C) (i : inclusion_index P Q T) :
    @mackey_span C P Q :=
  @MackeySpan C P Q
    (Sub (inclusion_apex (val P) (val Q) (double_coset_representative (val i))) (valP i))
    (orbit_class (inclusion_left F (val P) (val Q) (double_coset_representative (val i))))
    (orbit_class (inclusion_right F (val P) (val Q) (double_coset_representative (val i)))).

Definition raw_index (P Q T : C) (f : arrow F (val P) (val T))
    (g : arrow F (val Q) (val T)) :=
  {i : DPFusionMackey.raw_index f g |
    centric F (raw_apex f g (double_coset_representative i))}.

Definition raw_term (P Q T : C) (f : arrow F (val P) (val T))
    (g : arrow F (val Q) (val T)) (i : raw_index f g) : @mackey_span C P Q :=
  @MackeySpan C P Q
    (Sub (raw_apex f g (double_coset_representative (val i))) (valP i))
    (orbit_class (raw_left f g (double_coset_representative (val i))))
    (orbit_class (raw_right f g (double_coset_representative (val i)))).

Section Coefficients.
Variable R : comPzRingType.
Variable M : mackey_pair R C.

Definition inclusion_mackey_formula :=
  forall (P Q T : C) (hP : val P \subset val T) (hQ : val Q \subset val T) x,
    pair_pull M (centric_inclusion hQ) (pair_push M (centric_inclusion hP) x) =
    \sum_(i : inclusion_index P Q T)
      pair_push M (span_right (inclusion_term i))
        (pair_pull M (span_left (inclusion_term i)) x).

Hypothesis hM : inclusion_mackey_formula.

Theorem raw_mackey_formula (P Q T : C)
    (f : arrow F (val P) (val T)) (g : arrow F (val Q) (val T)) x :
    pair_pull M (orbit_class g) (pair_push M (orbit_class f) x) =
    \sum_(i : raw_index f g)
      pair_push M (span_right (raw_term i)) (pair_pull M (span_left (raw_term i)) x).
Proof.
have ht := @pair_mackey_iso_transport R C M P Q (@centric_image P T f) (@centric_image Q T g) T
  (@centric_image_iso P T f) (@centric_image_iso Q T g)
  (@centric_inclusion (@centric_image P T f) T (DPFusion.image_sub (val f)))
  (@centric_inclusion (@centric_image Q T g) T (DPFusion.image_sub (val g)))
  [the finType of raw_index f g]
  (fun i => @inclusion_term (@centric_image P T f) (@centric_image Q T g) T i)
  (@hM (@centric_image P T f) (@centric_image Q T g) T
    (DPFusion.image_sub (val f)) (DPFusion.image_sub (val g))) x.
have hf : @compose C _ _ _ (iso_hom (@centric_image_iso P T f))
    (@centric_inclusion (@centric_image P T f) T (DPFusion.image_sub (val f))) = orbit_class f :=
  orbit_image_factorization f.
have hg : @compose C _ _ _ (iso_hom (@centric_image_iso Q T g))
    (@centric_inclusion (@centric_image Q T g) T (DPFusion.image_sub (val g))) = orbit_class g :=
  orbit_image_factorization g.
rewrite hf hg in ht.
rewrite ht; apply: eq_bigr=> i _.
have hl := @raw_left_image_factorization S F (val P) (val Q) (val T) f g
  (double_coset_representative (val i)).
have hr := @raw_right_image_factorization S F (val P) (val Q) (val T) f g
  (double_coset_representative (val i)).
pose A : C := Sub (raw_apex f g (double_coset_representative (val i))) (valP i).
have hlc : @compose C A (@centric_image P T f) P
    (orbit_class (inclusion_left F (DPFusion.image (val f)) (DPFusion.image (val g))
      (double_coset_representative (val i))))
    (orbit_class (inverse_arrow f)) =
    orbit_class (raw_left f g (double_coset_representative (val i))) := hl.
have hrc : @compose C A (@centric_image Q T g) Q
    (orbit_class (inclusion_right F (DPFusion.image (val f)) (DPFusion.image (val g))
      (double_coset_representative (val i))))
    (orbit_class (inverse_arrow g)) =
    orbit_class (raw_right f g (double_coset_representative (val i))) := hr.
by rewrite hlc hrc.
Qed.

Theorem pullback_mackey_formula (P Q T : C)
    (f : hom C P T) (g : hom C Q T) x :
    pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index (DPFusionCentricPullbacks.centric_pullback f g))
      pair_push M (pb_right (DPFusionCentricPullbacks.centric_pullback f g) i)
        (pair_pull M (pb_left (DPFusionCentricPullbacks.centric_pullback f g) i) x).
Proof.
have h := raw_mackey_formula (repr f) (repr g) x.
rewrite /orbit_class !reprK in h; exact h.
Qed.
End Coefficients.
End Geometry.
End DPFusionCentricRestricted.

Print Assumptions DPFusionCentricRestricted.pullback_mackey_formula.
