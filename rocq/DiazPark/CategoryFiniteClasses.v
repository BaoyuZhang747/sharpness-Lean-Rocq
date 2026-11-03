From HB Require Import structures.
From mathcomp Require Import all_boot generic_quotient.
From DiazPark Require Import CategoryFinite.

(** The existing actual isomorphism quotient inherits finiteness from its
    representative subtype of the finite object set. *)
HB.instance Definition _ (C : finite_category) :=
  [Finite of fc_iso_class C by <:%/].
