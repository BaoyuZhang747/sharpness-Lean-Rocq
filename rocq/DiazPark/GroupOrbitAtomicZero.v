(** Atomic coefficients at 1 vanish in every genuine derived degree when
    the ambient finite group has a nontrivial normal p-subgroup. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup sylow.
From DiazPark Require Import Category CategoryModules CategoryAdjunction
  CategoryNaturalIso CategoryDerivedLimits CategoryDerivedAdjunction CategoryDerivedZero
  BarHigherLimitVanishing GroupOrbitCollections GroupOrbitNormalReflection GroupOrbitPReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupOrbitAtomic.
Section Collection.
Variable G : finGroupType.
Variable N : {group G}.
Hypothesis normalN : N <| [set: G].
Hypothesis ntN : N :!=: 1%G.
Variable B : {group G} -> bool.
Hypothesis join_closed : forall H, B H -> B (DPGroupOrbitNormal.join N H).
Variable R : pzRingType.
Variable A : module_codiagram R (DPGroupOrbitCollection.category B).
Hypothesis atomicA : forall H : DPGroupOrbitCollection.category B,
  val H :!=: 1%G -> forall v : fobj A H, v = 0.

Theorem normal_collection_atomic_zero n : forall q : derived_limit R A n, q = 0.
Proof.
  pose a := DPGroupOrbitNormal.normal_reflection normalN join_closed.
  pose e := nat_iso_component (derived_left_adjoint_nat_iso R (adjunction_op a) n) A.
  apply (proj2 (module_iso_zero_iff e)).
  apply (@pointwise_zero_derived_limits R (DPGroupOrbitNormal.containing N B)
    (functor_comp (functor_op (DPGroupOrbitNormal.inclusion N B)) A)) => H v.
  apply atomicA.
  change (val H :!=: 1%G).
  apply/eqP => h.
  have sN := (andP (valP H)).2.
  rewrite h subG1 in sN. by move: ntN; rewrite (eqP sN) eqxx.
Qed.
End Collection.

Section POrbit.
Variable G : finGroupType.
Variable p : nat.
Variable N : {group G}.
Hypothesis normalN : N <| [set: G].
Hypothesis ntN : N :!=: 1%G.
Hypothesis pN : p.-group N.
Variable R : pzRingType.

Theorem normal_p_atomic_zero
    (A : module_codiagram R (DPGroupOrbitP.orbit_category G p))
    (atomicA : forall H : DPGroupOrbitP.orbit_category G p,
      val H :!=: 1%G -> forall v : fobj A H, v = 0)
    n : forall q : derived_limit R A n, q = 0.
Proof.
  exact (@normal_collection_atomic_zero G N normalN ntN (DPGroupOrbitP.psubgroups p)
    (DPGroupOrbitP.join_pgroup normalN pN) R A atomicA n).
Qed.

Theorem normal_p_bounded_atomic_zero (T : {group G}) (sNT : N \subset T)
    (A : module_codiagram R (DPGroupOrbitP.bounded_orbit_category p T))
    (atomicA : forall H : DPGroupOrbitP.bounded_orbit_category p T,
      val H :!=: 1%G -> forall v : fobj A H, v = 0)
    n : forall q : derived_limit R A n, q = 0.
Proof.
  exact (@normal_collection_atomic_zero G N normalN ntN (DPGroupOrbitP.bounded_psubgroups p T)
    (DPGroupOrbitP.join_bounded normalN pN sNT) R A atomicA n).
Qed.

Theorem normal_p_sylow_atomic_zero (T : {group G}) (sylT : p.-Sylow([set: G]) T)
    (A : module_codiagram R (DPGroupOrbitP.bounded_orbit_category p T))
    (atomicA : forall H : DPGroupOrbitP.bounded_orbit_category p T,
      val H :!=: 1%G -> forall v : fobj A H, v = 0)
    n : forall q : derived_limit R A n, q = 0.
Proof.
  exact (@normal_p_bounded_atomic_zero T
    (DPGroupOrbitP.normal_p_sub_sylow normalN pN sylT) A atomicA n).
Qed.

End POrbit.
End DPGroupOrbitAtomic.
