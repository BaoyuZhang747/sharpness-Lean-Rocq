(** The scalar inverse required for stable elements is constructed from the
    actual Sylow index and the stated coefficient-ring hypotheses. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers FusionStableLimit PrimeLocalRing PrimeLocalUniversal
  PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyMackeyPair FiniteGroupFusion GroupCohomologyStableElementsNative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPGroupCohomology DPGroupCohomologyPullback
  DPGroupCohomologyMackeyPair DPGroupCohomologyStableElementsNative.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologyStableElementsSylow.

Lemma sylow_index_coprime (G : finGroupType) (P : {group G}) p
    (hp : prime p) (hP : p.-Sylow([set: G]) P) : coprime p (indexg [set: G] P).
Proof.
have /and3P[_ _ hindex] := hP.
exact: pnat_coprime (pnat_id hp) hindex.
Qed.

Section Local.
Variable G : finGroupType.
Variable P : {group G}.
Variable p : nat.
Variable hp : prime p.
Variable hP : p.-Sylow([set: G]) P.
Variable R : comPzRingType.
Variable localR : DPPrimeLocalUniversal.primes_inverted p R.
Variable A : lmodType R.
Variable n : nat.

Lemma sylow_index_inverse_exists : exists u : R, u * (indexg [set: G] P)%:R == 1.
Proof.
have [u hu] := @localR (indexg [set: G] P) (sylow_index_coprime hp hP).
exists u; exact/eqP.
Qed.

Definition sylow_index_inverse : R := xchoose sylow_index_inverse_exists.

Lemma sylow_index_inverse_spec : sylow_index_inverse * (indexg [set: G] P)%:R = 1.
Proof. exact: (eqP (xchooseP sylow_index_inverse_exists)). Qed.

Definition sylow_stable_iso :=
  @finite_group_stable_iso G P R A n sylow_index_inverse sylow_index_inverse_spec.

Theorem sylow_stable_iso_value z :
  submodule_val (module_hom_fun (iso_hom sylow_stable_iso) z) =
    module_hom_fun (pull A (top_ambient_inclusion P) n) z.
Proof. exact: finite_group_stable_iso_value. Qed.

End Local.

Definition field_sylow_stable_iso (G : finGroupType) (P : {group G}) p
    (hP : p.-Sylow([set: G]) P) (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  @sylow_stable_iso G P p (pcharf_prime charp) hP K
    (@DPFusionCentricAcyclicity.field_local p K charp) A n.

Definition prime_local_algebra_sylow_stable_iso (G : finGroupType) (P : {group G}) p
    (hp : prime p) (hP : p.-Sylow([set: G]) P) (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) (A : lmodType R) n :=
  @sylow_stable_iso G P p hp hP R
    (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n.

Theorem field_sylow_stable_iso_value (G : finGroupType) (P : {group G}) p
    (hP : p.-Sylow([set: G]) P) (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n z :
  submodule_val (module_hom_fun (iso_hom (field_sylow_stable_iso hP charp A n)) z) =
    module_hom_fun (pull A (top_ambient_inclusion P) n) z.
Proof. exact: sylow_stable_iso_value. Qed.

Theorem prime_local_algebra_sylow_stable_iso_value (G : finGroupType) (P : {group G}) p
    (hp : prime p) (hP : p.-Sylow([set: G]) P) (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) (A : lmodType R) n z :
  submodule_val (module_hom_fun
    (iso_hom (prime_local_algebra_sylow_stable_iso hp hP phi A n)) z) =
    module_hom_fun (pull A (top_ambient_inclusion P) n) z.
Proof. exact: sylow_stable_iso_value. Qed.

End DPGroupCohomologyStableElementsSylow.
