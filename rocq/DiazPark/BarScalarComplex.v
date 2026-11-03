From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  CategoryComplexIso HomologicalComplex HomologicalScalarRestriction HomologicalScalarCohomology
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  BarPaths BarComplex BarNaturality BarResolutionComparison
  MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkScalarRestriction DiazParkScalarCohomology
  DiazParkBarPaths DiazParkBarComplex DiazParkBarNaturality DiazParkBarResolutionComparison.
Local Open Scope ring_scope.

Module DiazParkBarScalarComplex.
Section Scalars.
Variables A B : pzRingType.
Variable f : {rmorphism A -> B}.
Variable C : category.

Section Coefficients.
Variable D : module_codiagram B C.
Local Notation DA := (restriction_diagram f D).
Local Notation KA := (restriction_complex f (bar_complex D)).
Local Notation KB := (bar_complex DA).

Definition bar_scalar_term_iso n : @isomorphism (module_category A)
    (cochain_term KA n) (cochain_term KB n).
Proof.
unshelve refine (@Build_isomorphism (module_category A) (cochain_term KA n) (cochain_term KB n)
  (exist _ (fun x => x) _) (exist _ (fun x => x) _) _ _).
- move=> a x y; reflexivity.
- move=> a x y; reflexivity.
- apply module_hom_ext => x; reflexivity.
- apply module_hom_ext => x; reflexivity.
Defined.

Lemma bar_scalar_d n (a : bar_term D n) : bar_d DA n a = bar_d D n a.
Proof.
rewrite !bar_d_formula.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (bar_evaluation DA p (\sum_(i < n.+2) (-1)^+i *: bar_coface (D:=DA) i a) =
  bar_evaluation D p (\sum_(i < n.+2) (-1)^+i *: bar_coface (D:=D) i a)).
rewrite !linear_sum; apply: eq_bigr => i _; rewrite !linearZ.
change (f ((-1)^+i) *: @bar_coface A C DA n i a x p =
  (-1)^+i *: @bar_coface B C D n i a x p).
rewrite rmorph_sign; reflexivity.
Qed.

Lemma bar_scalar_term_commutes n x :
  cochain_d KB n (module_hom_fun (iso_hom (bar_scalar_term_iso n)) x) =
  module_hom_fun (iso_hom (bar_scalar_term_iso n.+1)) (cochain_d KA n x).
Proof. exact: bar_scalar_d. Qed.

Definition bar_scalar_cochain_map : cochain_map KA KB :=
  term_iso_cochain_map bar_scalar_term_commutes.

Definition bar_scalar_cohomology_iso n : @isomorphism (module_category A)
    (restricted_module_type f [the lmodType B of cohomology (bar_complex D) n])
    [the lmodType A of cohomology KB n] :=
  module_iso_comp (iso_symm (scalar_cohomology_iso f (bar_complex D) n))
    (term_iso_cohomology_iso bar_scalar_term_commutes n).

End Coefficients.
End Scalars.
End DiazParkBarScalarComplex.
