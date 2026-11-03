import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! A first-quadrant diagonal is finite in each total degree. The
horizontal index determines the pair, by the actual sum equation. -/
set_option autoImplicit false
namespace Sharpness

abbrev NatTotalIndex (n : ℕ) := {pq : ℕ × ℕ // pq.1+pq.2=n}

instance natTotalIndex_finite (n : ℕ) : Finite (NatTotalIndex n) := by
  let f : NatTotalIndex n → Fin (n+1) := fun z => ⟨z.val.1, by have := z.property; omega⟩
  apply Finite.of_injective f
  intro z w h
  have hp : z.val.1=w.val.1 := congrArg Fin.val h
  apply Subtype.ext
  apply Prod.ext hp
  have hz := z.property
  have hw := w.property
  omega

end Sharpness
