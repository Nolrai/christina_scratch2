import Mathlib
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Germ Topology

def hello := "world"

def HyperRat := Germ (hyperfilter ℕ : Filter ℕ) ℚ

noncomputable
instance : LinearOrderedField HyperRat :=
  inferInstanceAs (LinearOrderedField (Germ _ _))

abbrev Near [LinearOrderedField α] (a b : α) : Prop :=
  ∀ n : ℕ, abs (a - b) ≤ 1 / (n + 1)

@[simp]
theorem zero_lt_nat_add_one [LinearOrderedField α] (n : ℕ) : (0 : α) < ↑n + 1 := by
  induction n
  case zero => simp only [CharP.cast_eq_zero, zero_add, zero_lt_one]
  case succ n h =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← add_zero 0]
    apply add_lt_add h zero_lt_one

def Near.setoid [LinearOrderedField α] : Setoid α where
  r := Near
  iseqv := {
    refl := λ x => by
      rw [Near]
      intros n
      simp
      induction n
      case zero => simp
      case succ _ n h =>
        apply add_nonneg (by aesop) (by simp)
    symm := by
      intros x y x_near_y n
      rw [abs_sub_comm]
      apply x_near_y
    trans := by
      intros x y z x_near_y y_near_z n
      rw [← sub_add_sub_cancel x y z]
      trans (1 / (↑(n * 2 + 1) + 1) + 1 / (↑(n * 2 + 1) + 1))
      trans abs (x - y) + abs (y - z)
      apply abs_add_le
      apply add_le_add
      apply x_near_y (n * 2 + 1)
      apply y_near_z (n * 2 + 1)
      rw [div_add_div, one_mul, div_le_iff]
      rw [div_mul_comm]
      simp [mul_one]
      rw [← mul_two]
      rw [le_div_iff]
      ring_nf
      rfl
      simp
      ring_nf
      have : (0 : α) < (1 + n * 2 : ℕ) := by
        rename_i inst
        simp_all only [Nat.cast_add, Nat.cast_one]
        simp
      apply add_pos
      · apply add_pos
        exact zero_lt_one
        apply mul_pos
        apply this
        aesop
      · apply pow_two_pos_of_ne_zero
        symm
        apply ne_of_lt
        exact this
  }

instance : Setoid (HyperRat) := Near.setoid

inductive Limited [Preorder α] [Semiring α] (a : α) : Prop where
  | pos (n : ℕ) : 0 < a → a < n → Limited a
  | neg (n : ℕ) : a ≤ 0 → 0 < a + n → Limited a

abbrev BigReal : Type := Quotient (Near.setoid : Setoid HyperRat)

theorem BigReal.aux [LinearOrderedField α] {x₁ x₂ : α} :
  Near x₁ x₂ → (n : ℕ) → 0 < n → abs (x₁ - x₂) < 1 / ↑n := by
  intros x_near n n_pos
  have := x_near (n.pred)
  have : ↑n = ↑(n.pred) + 1 := by
    simp only [Nat.pred_eq_sub_one]
    rw [Nat.sub_add_cancel]
    apply n_pos
  rw [this, Nat.cast_add]

def BigReal.add : BigReal → BigReal → BigReal := by
  apply Quotient.map₂ (· + ·)
  intros x₁ x₂ x_equiv y₁ y₂ y_equiv
  simp
  intros n
  have : x₁ + y₁ - (x₂ + y₂) = x₁ - x₂ + (y₁ - y₂) := by ring
  rw [this]
  trans (1/((n+1) * 2) + 1/((n+1) * 2))
  trans
  apply abs_add_le
  apply add_le_add
  trans
  apply x_equiv (n*2+1)
  apply div_le_div
  · exact zero_le_one
  · exact le_refl 1
  · simp only [zero_lt_nat_add_one, mul_pos_iff_of_pos_left, Nat.ofNat_pos]
  · simp_rw [right_distrib, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_mul]
    ring_nf
    rfl
  · rw [← Nat.cast_two]
    rw [← Nat.cast_one]
    rw [← Nat.cast_add, ← Nat.cast_mul]
    rw [Nat.cast_one]
    apply le_of_lt
    apply BigReal.aux y_equiv
    ring_nf
    omega
  · rw [← mul_two, div_mul_eq_mul_div, one_mul]
    rw [div_le_div_iff, one_mul, mul_comm]
    · simp only [zero_lt_nat_add_one, mul_pos_iff_of_pos_left, Nat.ofNat_pos]
    · apply zero_lt_nat_add_one

instance : LinearOrderedField BigReal where
  add := BigReal.add

def altReals := {x : BigReal // Limited x}
