(** Actual comparison between integer filtration and the native filtration
    at max(p,0), including literal compatibility of transitions and inclusion. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  HomologicalComplex HomologicalCohomology CategoryComplexIso ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainIntegerFiltration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DPFirstQuadrantCochain
  DPFirstQuadrantTotal DPColumnFiltration DPIntegerColumnFiltration.

Module DPIntegerNative.
Section Native.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition integer_native_term_iso p n : @isomorphism (module_category R)
    (cochain_term (integer_column K p) n) (column_term K (Z.to_nat p) n).
Proof.
destruct p as [|p|p].
- exact (iso_symm (zero_column_term_iso K n)).
- exact (@iso_refl (module_category R) (column_term K (Pos.to_nat p) n)).
- exact (iso_symm (zero_column_term_iso K n)).
Defined.

Lemma integer_native_term_commutes p n x :
    cochain_d (column_complex K (Z.to_nat p)) n
      (module_hom_fun (iso_hom (integer_native_term_iso p n)) x) =
    module_hom_fun (iso_hom (integer_native_term_iso p n.+1))
      (cochain_d (integer_column K p) n x).
Proof.
destruct p as [|p|p].
- apply submodule_val_injective.
  change (cochain_d (total_complex K) n
    (module_hom_fun (iso_hom (zero_column_term_iso K n))
      (module_hom_fun (iso_inv (zero_column_term_iso K n)) x)) =
    module_hom_fun (iso_hom (zero_column_term_iso K n.+1))
      (module_hom_fun (iso_inv (zero_column_term_iso K n.+1)) (cochain_d (total_complex K) n x))).
  by rewrite !module_iso_inv_hom_apply.
- reflexivity.
- apply submodule_val_injective.
  change (cochain_d (total_complex K) n
    (module_hom_fun (iso_hom (zero_column_term_iso K n))
      (module_hom_fun (iso_inv (zero_column_term_iso K n)) x)) =
    module_hom_fun (iso_hom (zero_column_term_iso K n.+1))
      (module_hom_fun (iso_inv (zero_column_term_iso K n.+1)) (cochain_d (total_complex K) n x))).
  by rewrite !module_iso_inv_hom_apply.
Qed.

Definition integer_native_map p := @term_iso_cochain_map R (integer_column K p)
  (column_complex K (Z.to_nat p)) (integer_native_term_iso p) (@integer_native_term_commutes p).
Definition native_integer_map p := @term_iso_cochain_inverse R (integer_column K p)
  (column_complex K (Z.to_nat p)) (integer_native_term_iso p) (@integer_native_term_commutes p).

Lemma integer_native_total p n x :
    cochain_map_at (column_inclusion K (Z.to_nat p)) n (cochain_map_at (integer_native_map p) n x) =
      cochain_map_at (integer_inclusion K p) n x.
Proof.
destruct p as [|p|p]; try reflexivity.
all: change (module_hom_fun (iso_hom (zero_column_term_iso K n))
  (module_hom_fun (iso_inv (zero_column_term_iso K n)) x) = x).
all: exact: module_iso_inv_hom_apply.
Qed.

Definition integer_to_nat_mono p q (h : Z.le p q) : (Z.to_nat p <= Z.to_nat q)%coq_nat.
Proof.
destruct (Z_le_dec 0 p) as [hp|hp].
- have hq : Z.le 0 q by lia.
  exact (proj1 (Z2Nat.inj_le p q hp hq) h).
- destruct p; simpl; lia.
Defined.

Lemma integer_native_transition p q (h : Z.le p q) n x :
    cochain_map_at (integer_native_map p) n (cochain_map_at (integer_transition K h) n x) =
    cochain_map_at (column_transition K (integer_to_nat_mono h)) n
      (cochain_map_at (integer_native_map q) n x).
Proof.
apply (@column_inclusion_injective R K (Z.to_nat p) n).
rewrite integer_native_total integer_transition_total.
change (cochain_map_at (integer_inclusion K q) n x =
  cochain_map_at (column_inclusion K (Z.to_nat q)) n (cochain_map_at (integer_native_map q) n x)).
symmetry; exact: integer_native_total.
Qed.

End Native.
End DPIntegerNative.
