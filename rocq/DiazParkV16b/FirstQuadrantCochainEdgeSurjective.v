(** Lifting an actual zero-column cohomology kernel class to a total cocycle,
    by a two-column seed and finite elimination of its remaining obstruction. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainEdge
  FirstQuadrantCochainLeading FirstQuadrantCochainInclusion FirstQuadrantCochainElimination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps
  DPFirstQuadrantSupport DPFirstQuadrantEdge DPFirstQuadrantLeading DPFirstQuadrantInclusion
  DPFirstQuadrantElimination.
Local Open Scope ring_scope.

Module DPFirstQuadrantEdgeSurjective.
Section Surjectivity.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma zero_column_zero_supported n (x : total_term K n) :
    zero_column_at x = 0 -> supported_from x 1%N.
Proof.
intros hx p q h hp.
have ep : p = 0%N by lia. subst p.
have eq : q = n by lia. subst q.
have eh : h = Logic.eq_refl by apply Prop_irrelevance.
rewrite eh. exact hx.
Qed.

Lemma kernel_cycle_seed n (x : bicomplex_term K 0%N n)
    (hx : cocycle (vertical_complex K 0%N) n x)
    (hh : horizontal_cohomology K 0%N n (cohomology_class hx) = 0) :
    exists z : total_term K n, zero_column_at z = x /\ supported_from (total_d z) 2%N.
Proof.
rewrite /horizontal_cohomology cohomology_map_class in hh.
have hb := proj1 (cohomology_class_zero _) hh.
destruct n as [|n].
- pose h00 : (0 + 0)%coq_nat = 0%N := Logic.eq_refl.
  pose z : total_term K 0%N := total_include h00 x.
  have hz : zero_column_at z = x := total_include_same h00 Logic.eq_refl x.
  exists z; split; [exact hz|].
  intros p q h hp.
  have hor : p = 0%N \/ p = 1%N by lia.
  destruct hor as [ep|ep]; subst p.
  + exact (@include_cycle_d_supported R K 0%N 0%N 0%N h00 x hx 0%N q h (Nat.lt_0_succ 0)).
  + have eq : q = 0%N by lia. subst q.
    have eh : h = horizontal_output_index h00 by apply Prop_irrelevance.
    rewrite eh /z include_d_horizontal. exact hb.
- destruct hb as [b hb].
  pose h0 : (0 + n.+1)%coq_nat = n.+1 := Logic.eq_refl.
  pose h1 : (1 + n)%coq_nat = n.+1 := Logic.eq_refl.
  pose z : total_term K n.+1 := total_include h0 x + total_include h1 b.
  have hz : zero_column_at z = x.
    change (@total_include R K 0%N n.+1 n.+1 h0 x 0%N n.+1 Logic.eq_refl +
      @total_include R K 1%N n n.+1 h1 b 0%N n.+1 Logic.eq_refl = x).
    rewrite total_include_same total_include_other; [by rewrite addr0|lia].
  exists z; split; [exact hz|].
  have hs0 : supported_from (total_d z) 1%N.
    apply zero_column_zero_supported.
    rewrite -zero_column_d hz. exact hx.
  intros p q h hp.
  have hor : p = 0%N \/ p = 1%N by lia.
  destruct hor as [ep|ep]; subst p.
  + exact (hs0 0%N q h (Nat.lt_0_succ 0)).
  + have eq : q = n.+1 by lia. subst q.
    rewrite /z linearD.
    change (@total_d R K n.+1 (total_include h0 x) 1%N n.+1 h +
      @total_d R K n.+1 (total_include h1 b) 1%N n.+1 h = 0).
    have eh0 : h = horizontal_output_index h0 by apply Prop_irrelevance.
    have eh1 : h = vertical_output_index h1 by apply Prop_irrelevance.
    rewrite eh0 include_d_horizontal -eh0 eh1 include_d_vertical expr1 scaleN1r.
    change (vertical K 1%N n b = horizontal K 0%N n.+1 x) in hb.
    by rewrite hb subrr.
Qed.

Lemma kernel_cycle_lift (hK : positive_horizontal_exact K) n
    (x : bicomplex_term K 0%N n) (hx : cocycle (vertical_complex K 0%N) n x)
    (hh : horizontal_cohomology K 0%N n (cohomology_class hx) = 0) :
    exists z : total_term K n, cocycle (total_complex K) n z /\ zero_column_at z = x.
Proof.
have [z [hz hzs]] := @kernel_cycle_seed n x hx hh.
have hd : cocycle (total_complex K) n.+1 (total_d z) := total_d_squared z.
have [y [hy hys]] := @tail_cycle_boundary R K hK n 1%N (total_d z) hd hzs.
exists (z - y); split.
- change (total_d (z - y) = 0).
  rewrite linearB.
  change (total_d z - total_d y = 0).
  by rewrite hy subrr.
- rewrite linearB.
  change (zero_column_at z - zero_column_at y = x).
  have hy0 : zero_column_at y = 0 := hys 0%N n Logic.eq_refl (Nat.lt_0_succ 0).
  by rewrite hz hy0 subr0.
Qed.

Theorem edge_map_surjective (hK : positive_horizontal_exact K) n :
    forall a : edge_module K n, exists x, edge_map K n x = a.
Proof.
intro a.
have [z hz] := quotient_pi_surjective (submodule_val a).
have hh : horizontal_cohomology K 0%N n
    (cohomology_class (submodule_val_mem z)) = 0.
  have hclass : cohomology_class (submodule_val_mem z) =
      quotient_pi (boundaries_in_cycles (vertical_complex K 0%N) n) z.
    unfold cohomology_class; congr (quotient_pi _ _).
    apply submodule_val_injective; reflexivity.
  rewrite hclass hz; exact (submodule_val_mem a).
have [x [hx he]] := @kernel_cycle_lift hK n
  (cycle_inclusion (vertical_complex K 0%N) n z) (submodule_val_mem z) hh.
exists (cohomology_class hx).
apply submodule_val_injective.
rewrite edge_map_component cohomology_map_class.
rewrite <- hz.
unfold cohomology_class; congr (quotient_pi _ _).
apply submodule_val_injective.
exact he.
Qed.
End Surjectivity.
End DPFirstQuadrantEdgeSurjective.
