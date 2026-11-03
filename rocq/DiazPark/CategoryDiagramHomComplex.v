(** Applying the genuine natural-transformation Hom module to diagram complexes,
    chain maps and homotopies. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalDiagramInjectives CategoryInjectiveResolution
  CategoryInjectiveResolutionComparison CategoryInjectiveResolutionHomotopy
  CategoryDerivedLimits MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.
Section HomComplex.
Variable R : comPzRingType.
Variable C : category.
Variable A : module_diagram R C.

Definition diagram_hom_complex (K : @diagram_complex R C) : @cochain_complex R.
Proof.
refine (@CochainComplex R (fun n => diagram_hom_type A (diagram_term K n))
  (fun n => (diagram_hom_post A (diagram_d K n) : {linear _ -> _})) _).
intros n f; apply diagram_hom_ext; intros x v.
exact (@diagram_d2 R C K n x (diagram_hom_at f x v)).
Defined.

Definition diagram_hom_cochain_map {K L : @diagram_complex R C}
    (f : diagram_cochain_map K L) : cochain_map (diagram_hom_complex K) (diagram_hom_complex L).
Proof.
refine (@CochainMap R (diagram_hom_complex K) (diagram_hom_complex L)
  (fun n => (diagram_hom_post A (diagram_cochain_map_at f n) : {linear _ -> _})) _).
intros n h; apply diagram_hom_ext; intros x v.
exact (diagram_cochain_map_commutes f n x (diagram_hom_at h x v)).
Defined.

Definition diagram_hom_cochain_homotopy {K L : @diagram_complex R C}
    {f g : diagram_cochain_map K L} (h : diagram_cochain_homotopy f g) :
    cochain_homotopy (diagram_hom_cochain_map f) (diagram_hom_cochain_map g).
Proof.
refine (@CochainHomotopy R (diagram_hom_complex K) (diagram_hom_complex L) (diagram_hom_cochain_map f) (diagram_hom_cochain_map g)
  (fun n => (diagram_hom_post A (diagram_homotopy_at h n) : {linear _ -> _})) _ _).
- intro u; apply diagram_hom_ext; intros x v.
  rewrite diagram_hom_at_add diagram_hom_at_opp.
  change (module_hom_fun (component (diagram_cochain_map_at f 0) x) (diagram_hom_at u x v) -
    module_hom_fun (component (diagram_cochain_map_at g 0) x) (diagram_hom_at u x v) = module_hom_fun (component (diagram_homotopy_at h 0) x) (module_hom_fun (component (diagram_d K 0) x) (diagram_hom_at u x v))).
  exact (diagram_homotopy_zero h x (diagram_hom_at u x v)).
- intros n u; apply diagram_hom_ext; intros x v.
  rewrite !diagram_hom_at_add diagram_hom_at_opp.
  change (module_hom_fun (component (diagram_cochain_map_at f n.+1) x) (diagram_hom_at u x v) -
    module_hom_fun (component (diagram_cochain_map_at g n.+1) x) (diagram_hom_at u x v) = module_hom_fun (component (diagram_d L n) x) (module_hom_fun (component (diagram_homotopy_at h n) x) (diagram_hom_at u x v)) + module_hom_fun (component (diagram_homotopy_at h n.+1) x) (module_hom_fun (component (diagram_d K n.+1) x) (diagram_hom_at u x v))).
  exact (diagram_homotopy_succ h n x (diagram_hom_at u x v)).
Defined.

Lemma diagram_hom_cohomology_identity (K : @diagram_complex R C) n
    (q : cohomology (diagram_hom_complex K) n) :
    cohomology_map (diagram_hom_cochain_map (diagram_cochain_identity K)) n q = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; apply diagram_hom_ext; intros x v; reflexivity.
Qed.

Lemma diagram_hom_cohomology_composition {K L M : @diagram_complex R C}
    (f : diagram_cochain_map K L) (g : diagram_cochain_map L M) n
    (q : cohomology (diagram_hom_complex K) n) :
    cohomology_map (diagram_hom_cochain_map (diagram_cochain_composition f g)) n q =
      cohomology_map (diagram_hom_cochain_map g) n (cohomology_map (diagram_hom_cochain_map f) n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; apply diagram_hom_ext; intros x v; reflexivity.
Qed.

Theorem diagram_hom_resolution_map_independent
    {F G : module_diagram R C} {X : injective_resolution F} {Y : injective_resolution G}
    {u : nat_trans F G} (a b : injective_resolution_map X Y u) n
    (q : cohomology (diagram_hom_complex (injective_resolution_complex X)) n) :
    cohomology_map (diagram_hom_cochain_map (resolution_map_complex a)) n q =
      cohomology_map (diagram_hom_cochain_map (resolution_map_complex b)) n q.
Proof.
exact (cohomology_map_homotopy
  (diagram_hom_cochain_homotopy (injective_resolution_maps_homotopic a b)) q).
Qed.
End HomComplex.
Arguments diagram_hom_complex {R C} A K.
Arguments diagram_hom_cochain_map {R C} A {K L} f.




