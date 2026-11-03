(** Relative homology comparison for an actual map preserving subcomplexes. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainSubcomplex ChainSubcomplexMaps ChainShortExact ChainExactComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPChainSubcomplex
  DPChainSubcomplexMaps DPChainShortExact DPChainExactComparison.
Module DPChainSubcomplexComparison.
Section Comparison.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable S : chain_subcomplex C.
Variable T : chain_subcomplex D.
Variable hf : forall n x, subspace_at S n x -> subspace_at T n (chain_map_at f n x).
Let sf := @subcomplex_map R C D f S T hf.
Let qf := @relative_map R C D f S T hf.
Variable hsi : forall n, injective (homology_map sf n).
Variable hss : forall n y, exists x, homology_map sf n x = y.
Variable hfi : forall n, injective (homology_map f n).
Variable hfs : forall n y, exists x, homology_map f n x = y.

Definition relative_homology_iso n : @isomorphism (module_category R)
    [the lmodType R of homology (quotient_chain S) n]
    [the lmodType R of homology (quotient_chain T) n] :=
  @comparison_iso R (subcomplex_chain S) C (quotient_chain S)
    (subcomplex_chain T) D (quotient_chain T)
    (subcomplex_inclusion S) (quotient_projection S)
    (subcomplex_inclusion T) (quotient_projection T)
    (subcomplex_short_exact S) (subcomplex_short_exact T) sf f qf
    (fun n x => esym (@subcomplex_map_inclusion R C D f S T hf n x))
    (@relative_map_projection R C D f S T hf)
    hsi hss hfi hfs n.

Theorem relative_homology_iso_hom n (q : homology (quotient_chain S) n) :
  module_hom_fun (iso_hom (relative_homology_iso n)) q = homology_map qf n q.
Proof. exact: comparison_iso_hom. Qed.
End Comparison.
End DPChainSubcomplexComparison.
