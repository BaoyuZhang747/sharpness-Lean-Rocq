(** Enough injectives for arbitrary left modules over an arbitrary unital
    possibly-zero ring. The construction embeds the underlying abelian group
    in its proved divisible envelope, then uses actual integer coinduction. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules ModuleInjectives
  ModuleDivisibleInjectives ModuleRationalEnvelope ModuleCoinduced
  ModuleCoinducedInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "M ^z" := (zmodule M) : type_scope.

Theorem module_enough_injectives (R : pzRingType) (A : lmodType R) :
    exists (J : lmodType R) (i : module_hom A J),
      injective i /\ module_injective J.
Proof.
  pose (E := [the lmodType int of DiazParkRationalEnvelope.envelope A]).
  pose (e := (exist _ (@DiazParkRationalEnvelope.embedding_int A)
      (@DiazParkRationalEnvelope.embedding_int_linear A) :
        module_hom [the lmodType int of A^z] E)).
  have e_inj : injective e := @DiazParkRationalEnvelope.embedding_int_injective A.
  have E_inj : module_injective E.
  { apply divisible_integer_module_injective.
    exact (@DiazParkRationalEnvelope.envelope_divisible A). }
  exists (coinduced_module R E), (@coinduced_lift R E A e). split.
  - exact (@coinduced_lift_injective R E A e e_inj).
  - exact (@coinduced_injective R E E_inj).
Qed.
