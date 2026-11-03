From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

(** The actual connecting linear map on kernel/image quotients. Choices are
    used to lift representatives, but independence and linearity are proved. *)
Module DiazParkHomologicalConnecting.
Section Connecting.
Variable R : pzRingType.
Variables A B C : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C).
Variable s : degreewise_short_exact f g.

Definition connecting_lift n (z : cycle_module C n) : cochain_term B n :=
  proj1_sig (constructive_indefinite_description
    (@short_exact_surjective R A B C f g s n (cycle_inclusion C n z))).

Lemma connecting_lift_spec n (z : cycle_module C n) :
  cochain_map_at g n (connecting_lift z) = cycle_inclusion C n z.
Proof.
exact: (proj2_sig (constructive_indefinite_description
  (@short_exact_surjective R A B C f g s n (cycle_inclusion C n z)))).
Qed.

Lemma connecting_lift_d_kernel n (z : cycle_module C n) :
  cochain_map_at g n.+1 (cochain_d B n (connecting_lift z)) = 0.
Proof.
rewrite -cochain_map_commutes connecting_lift_spec.
exact (submodule_val_mem z).
Qed.

Definition connecting_preimage n (z : cycle_module C n) : cochain_term A n.+1 :=
  proj1_sig (constructive_indefinite_description
    (@short_exact_kernel R A B C f g s n.+1 _ (connecting_lift_d_kernel z))).

Lemma connecting_preimage_spec n (z : cycle_module C n) :
  cochain_map_at f n.+1 (connecting_preimage z) = cochain_d B n (connecting_lift z).
Proof.
exact: (proj2_sig (constructive_indefinite_description
  (@short_exact_kernel R A B C f g s n.+1 _ (connecting_lift_d_kernel z)))).
Qed.

Lemma connecting_preimage_cocycle n (z : cycle_module C n) :
  cocycle A n.+1 (connecting_preimage z).
Proof.
apply: (@short_exact_injective R A B C f g s n.+2).
rewrite linear0 -cochain_map_commutes connecting_preimage_spec.
exact: cochain_d2.
Qed.

Definition connecting_cycle n (z : cycle_module C n) : cycle_module A n.+1 :=
  cycle_of_cocycle (connecting_preimage_cocycle z).

Definition connecting_class n (z : cycle_module C n) : cohomology A n.+1 :=
  quotient_pi (boundaries_in_cycles A n.+1) (connecting_cycle z).

Lemma connecting_class_solution n (z : cycle_module C n)
    (b : cochain_term B n) (a : cycle_module A n.+1)
    (hb : cochain_map_at g n b = cycle_inclusion C n z)
    (ha : cochain_map_at f n.+1 (cycle_inclusion A n.+1 a) = cochain_d B n b) :
  connecting_class z = quotient_pi (boundaries_in_cycles A n.+1) a.
Proof.
apply/cohomology_pi_eq.
have hker : cochain_map_at g n (connecting_lift z - b) = 0.
  by rewrite linearB connecting_lift_spec hb subrr.
have [u hu] := @short_exact_kernel R A B C f g s n _ hker.
exists u; apply: (@short_exact_injective R A B C f g s n.+1).
change (cochain_map_at f n.+1 (cochain_d A n u) =
  cochain_map_at f n.+1 (connecting_preimage z - cycle_inclusion A n.+1 a)).
by rewrite -cochain_map_commutes hu !linearB connecting_preimage_spec ha.
Qed.

Lemma connecting_class_linear n : linear (@connecting_class n).
Proof.
move=> r z w.
rewrite -linearP.
apply: (@connecting_class_solution n (r *: z + w)
  (r *: connecting_lift z + connecting_lift w)
  (r *: connecting_cycle z + connecting_cycle w)).
- by rewrite linearP !connecting_lift_spec linearP.
- change (cochain_map_at f n.+1
    (r *: connecting_preimage z + connecting_preimage w) =
    cochain_d B n (r *: connecting_lift z + connecting_lift w)).
  by rewrite !linearP !connecting_preimage_spec.
Qed.

Definition connecting_class_hom n :
    module_hom [the lmodType R of cycle_module C n] [the lmodType R of cohomology A n.+1] :=
  exist _ (@connecting_class n) (@connecting_class_linear n).

Lemma connecting_class_boundary n (z : cycle_module C n) :
  boundaries_in_cycles C n z -> connecting_class z = 0.
Proof.
case: n z => [|n] z hz.
- have hz0 : z = 0 by apply submodule_val_injective; exact: hz.
  rewrite hz0; exact: (module_hom_zero (connecting_class_hom 0)).
- have [c hc] := hz.
  have [b hb] := @short_exact_surjective R A B C f g s n c.
  have he := @connecting_class_solution n.+1 z (cochain_d B n b) 0.
  have hg : cochain_map_at g n.+1 (cochain_d B n b) = cycle_inclusion C n.+1 z.
    by rewrite -cochain_map_commutes hb hc.
  have hf : cochain_map_at f n.+2 (cycle_inclusion A n.+2 0) = cochain_d B n.+1 (cochain_d B n b).
    by rewrite !linear0 cochain_d2.
  rewrite (he hg hf); exact: linear0.
Qed.

Definition connecting_map n : {linear cohomology C n -> cohomology A n.+1} :=
  (@quotient_lift R (cycle_module C n) (boundaries_in_cycles C n)
    [the lmodType R of cohomology A n.+1]
    (module_hom_to_linear (connecting_class_hom n)) (@connecting_class_boundary n) :
    {linear cohomology C n -> cohomology A n.+1}).

Lemma connecting_map_pi n (z : cycle_module C n) :
  connecting_map n (quotient_pi (boundaries_in_cycles C n) z) = connecting_class z.
Proof. exact: quotient_lift_pi. Qed.

Theorem connecting_map_kernel n (q : cohomology C n) :
  connecting_map n q = 0 <->
    exists r : cohomology B n, cohomology_map g n r = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite connecting_map_pi; split.
- move=> hz.
  have ha : coboundary A n.+1 (connecting_preimage z).
    apply/boundary_subspaceE.
    have hm : boundaries_in_cycles A n.+1 (connecting_cycle z).
      apply/quotient_pi_kernel; exact: hz.
    exact: hm.
  have [u hu] := ha.
  pose b := connecting_lift z - cochain_map_at f n u.
  have hb : cocycle B n b.
    by rewrite /cocycle /b linearB cochain_map_commutes hu connecting_preimage_spec subrr.
  exists (cohomology_class hb).
  rewrite cohomology_map_class /cohomology_class.
  congr (quotient_pi _ _); apply submodule_val_injective.
  change (cochain_map_at g n b = cycle_inclusion C n z).
  by rewrite /b linearB connecting_lift_spec
    (@short_exact_composite R A B C f g s n u) subr0.
- move=> [r hr].
  have [w hw] := quotient_pi_surjective r.
  have hc : connecting_map n (cohomology_map g n r) = 0.
    rewrite -hw cohomology_map_pi connecting_map_pi.
    have he := @connecting_class_solution n (cycle_map g n w)
      (cycle_inclusion B n w) 0.
    have hf : cochain_map_at f n.+1 (cycle_inclusion A n.+1 0) =
        cochain_d B n (cycle_inclusion B n w).
      rewrite !linear0; symmetry; exact: (submodule_val_mem w).
    rewrite (he (Logic.eq_refl _) hf); exact: linear0.
  by rewrite hr connecting_map_pi in hc.
Qed.

Theorem connecting_map_surjective n
    (hB : forall b : cochain_term B n.+1, cocycle B n.+1 b -> coboundary B n.+1 b) :
  forall q : cohomology A n.+1, exists r : cohomology C n, connecting_map n r = q.
Proof.
move=> q; have [a <-] := quotient_pi_surjective q.
have hc := cochain_map_cocycle f (submodule_val_mem a).
have [b hb] := hB _ hc.
have hz : cocycle C n (cochain_map_at g n b).
  rewrite /cocycle cochain_map_commutes hb.
  exact: (@short_exact_composite R A B C f g s n.+1 (cycle_inclusion A n.+1 a)).
exists (cohomology_class hz).
rewrite /cohomology_class connecting_map_pi.
apply: (@connecting_class_solution n (cycle_of_cocycle hz) b a).
- reflexivity.
- exact: esym hb.
Qed.

Theorem connecting_map_injective n
    (hB : forall q : cohomology B n, q = 0) : injective (connecting_map n).
Proof.
move=> x y hxy.
have hz : connecting_map n (x - y) = 0 by rewrite linearB hxy subrr.
have [r hr] := proj1 (connecting_map_kernel _) hz.
rewrite (hB r) linear0 in hr.
exact: subr0_eq (esym hr).
Qed.

End Connecting.
End DiazParkHomologicalConnecting.



