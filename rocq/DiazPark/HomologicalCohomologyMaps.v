From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import HomologicalComplex HomologicalMaps
  HomologicalCohomology ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps
  DiazParkCohomology.
Local Open Scope ring_scope.

(** Induced native linear maps on the actual cohomology quotient. *)
Module DiazParkCohomologyMaps.

Section Maps.
Variable R : pzRingType.
Variables C D : @cochain_complex R.
Variable f : cochain_map C D.

Definition cycle_map n : {linear cycle_module C n -> cycle_module D n} :=
  @submodule_map R (cochain_term C n) (cochain_term D n)
    (cochain_map_at f n) (cycle_subspace C n) (cycle_subspace D n)
    (fun x hx => @cochain_map_cocycle R C D f n x hx).

Lemma cycle_map_val n (z : cycle_module C n) :
  cycle_inclusion D n (cycle_map n z) = cochain_map_at f n (cycle_inclusion C n z).
Proof. reflexivity. Qed.

Lemma cycle_map_boundary n (z : cycle_module C n) :
  boundaries_in_cycles C n z -> boundaries_in_cycles D n (cycle_map n z).
Proof.
move=> hz.
change (boundary_subspace D n (cochain_map_at f n (cycle_inclusion C n z))).
apply/boundary_subspaceE; apply: cochain_map_coboundary.
by apply/boundary_subspaceE.
Qed.

Definition cohomology_map n : {linear cohomology C n -> cohomology D n} :=
  @quotient_map R (cycle_module C n) (cycle_module D n) (cycle_map n)
    (boundaries_in_cycles C n) (boundaries_in_cycles D n)
    (@cycle_map_boundary n).

Lemma cohomology_map_pi n (z : cycle_module C n) :
  cohomology_map n (quotient_pi (boundaries_in_cycles C n) z) =
    quotient_pi (boundaries_in_cycles D n) (cycle_map n z).
Proof. exact: quotient_map_pi. Qed.

Lemma cohomology_map_class n (x : cochain_term C n) (hx : cocycle C n x) :
  cohomology_map n (cohomology_class hx) =
    cohomology_class (@cochain_map_cocycle R C D f n x hx).
Proof.
rewrite /cohomology_class cohomology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective; reflexivity.
Qed.

End Maps.

Section Laws.
Variable R : pzRingType.

Lemma cohomology_pi_eq (C : @cochain_complex R) n (x y : cycle_module C n) :
  quotient_pi (boundaries_in_cycles C n) x =
      quotient_pi (boundaries_in_cycles C n) y <->
    coboundary C n (cycle_inclusion C n x - cycle_inclusion C n y).
Proof.
split.
- move=> h; apply/boundary_subspaceE.
  have hm : boundaries_in_cycles C n (x - y).
    apply/subspace_predP; rewrite -quotient_pi_eq.
    by apply/eqP.
  change (boundary_subspace C n (cycle_inclusion C n (x - y))) in hm.
  by rewrite linearB in hm.
- move=> h; apply/eqP; rewrite quotient_pi_eq; apply/subspace_predP.
  change (boundary_subspace C n (cycle_inclusion C n (x - y))).
  rewrite linearB; by apply/boundary_subspaceE.
Qed.

Lemma cohomology_map_identity (C : @cochain_complex R) n
    (q : cohomology C n) : cohomology_map (cochain_identity C) n q = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Lemma cohomology_map_composition (C D E : @cochain_complex R)
    (f : cochain_map C D) (g : cochain_map D E) n (q : cohomology C n) :
  cohomology_map (cochain_composition f g) n q =
    cohomology_map g n (cohomology_map f n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Theorem cohomology_map_homotopy (C D : @cochain_complex R)
    (f g : cochain_map C D) (h : cochain_homotopy f g)
    n (q : cohomology C n) : cohomology_map f n q = cohomology_map g n q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; apply/cohomology_pi_eq.
change (coboundary D n
  (cochain_map_at f n (cycle_inclusion C n z) -
    cochain_map_at g n (cycle_inclusion C n z))).
exact: (@homotopy_cohomologous R C D f g h n
  (cycle_inclusion C n z) (submodule_val_mem z)).
Qed.

End Laws.
End DiazParkCohomologyMaps.
