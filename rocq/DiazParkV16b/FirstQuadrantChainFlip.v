(** Actual exchange of the two unsigned bicomplex directions. *)
From mathcomp Require Import all_boot all_algebra.
From DiazParkV16b Require Import ChainComplex FirstQuadrantChainBicomplex FirstQuadrantChainTotalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPFirstQuadrantChain DPFirstQuadrantChainTotalMaps.

Module DPFirstQuadrantChainFlip.
Section Flip.
Variable R : pzRingType.

Definition flip (K : bicomplex R) : bicomplex R :=
  @Bicomplex R (fun p q => bicomplex_term K q p)
    (fun p q => vertical K q p) (fun p q => horizontal K q p)
    (fun p q => @vertical_squared R K q p)
    (fun p q => @horizontal_squared R K q p)
    (fun p q x => Logic.eq_sym (@horizontal_vertical R K q p x)).

Definition flip_map (K L : bicomplex R) (f : bicomplex_map K L) : bicomplex_map (flip K) (flip L) :=
  @BicomplexMap R (flip K) (flip L) (fun p q => bicomplex_map_at f q p)
    (fun p q => @bicomplex_map_vertical R K L f q p)
    (fun p q => @bicomplex_map_horizontal R K L f q p).

Lemma flip_vertical (K : bicomplex R) p : vertical_complex (flip K) p = horizontal_complex K p.
Proof. reflexivity. Qed.

Lemma flip_vertical_map (K L : bicomplex R) (f : bicomplex_map K L) p :
  vertical_map (flip_map f) p = horizontal_map f p.
Proof. reflexivity. Qed.

End Flip.
End DPFirstQuadrantChainFlip.
