import Mathlib
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic

open Filter

class isEmbiggen (M : Type → Type) where
  iso : Set (M α) ≃ Filter α
  inj : α → M α
  inj_spec (s : Set (M α)) (a : α) : inj a ∈ s ↔ pure a ≤ iso s

def Limited (x : α) [LinearOrderedRing α] : Prop := ∃ n : ℕ, abs x ≤ n

