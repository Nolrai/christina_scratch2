import Mathlib
import Mathlib.Order.Filter.Basic
import Mathlib.CategoryTheory.Category.Basic

section Words

inductive Data where
  | bit : Bool → Data
  | pair : Data → Data → Data

infix:50 " -:- " => Data.pair

-- standard partial equivalence
structure BSet where
  eq : Data → Data → Bool
  symm : Symmetric (eq · ·)
  trans : Transitive (eq · ·)
  cotrans : ∀ x y, eq x y = false → ∀ z, eq x z = false ∨ eq y z = false
  dec : DecidableRel (eq · ·)

def BSet.defined (x : Data) (s : BSet) : Prop := s.eq x x

-- This suffices to show that it both takes defined to defined,
-- and equal to equal.
structure BSetFun (dom cod : BSet) where
  toFun : Data → Data
  welldefined : ∀ {x y}, dom.eq x y → cod.eq (toFun x) (toFun y)

def BSetFun.comp {X Y Z} (f : BSetFun X Y) (g : BSetFun Y Z) : BSetFun X Z := {
    toFun := g.toFun ∘ f.toFun
    welldefined := g.welldefined ∘ f.welldefined
  }

theorem BSetFun.assoc
  (X Y Z W : BSet)
  (f : BSetFun X Y)
  (g : BSetFun Y Z)
  (h : BSetFun Z W)
  : (f.comp g).comp h = f.comp (g.comp h) := rfl

def BSetFun.equiv {dom cod : BSet}
  (f : BSetFun dom cod)
  (g : BSetFun dom cod) : Prop :=
  ∀ {x y}, dom.eq x y → cod.eq (f.toFun x) (g.toFun y)

instance BSetFun.setoid dom cod : Setoid (BSetFun dom cod) where
  r := BSetFun.equiv
  iseqv :=
    ⟨ λ f _ _ x_eq_y => f.welldefined x_eq_y
    , by
      intros f g f_eq_g x y x_eq_y
      apply cod.symm
      apply f_eq_g
      apply dom.symm
      apply x_eq_y
    , fun {f g h} f_eq_g g_eq_h x y x_eq_y => by
      apply cod.trans
      apply f_eq_g x_eq_y
      apply g_eq_h (dom.trans (dom.symm x_eq_y) x_eq_y)
    ⟩

def BSetHom dom cod := Quotient (BSetFun.setoid dom cod)

abbrev BSetHom.mk {dom cod} (F : BSetFun dom cod) : BSetHom dom cod := Quotient.mk _ F

abbrev BSetHom.comp {X Y Z} : BSetHom X Y → BSetHom Y Z → BSetHom X Z := by
  apply Quotient.map₂ BSetFun.comp _
  intros F₁ F₂ F_eq G₁ G₂ G_eq

  intros x y x_eq_y
  simp [BSetFun.comp] at *
  apply G_eq
  apply F_eq
  assumption

open CategoryTheory

instance : CategoryStruct BSet where
  Hom := BSetHom
  id _X := BSetHom.mk {
    toFun := id
    welldefined := λ h ↦ h
  }
  comp := BSetHom.comp

instance : Category BSet where
  id_comp {X Y} f := by
    induction f using Quotient.ind
    case _ f =>
    simp [CategoryStruct.id, CategoryStruct.comp, BSetHom.comp, BSetFun.comp]
  comp_id {X Y} f := by
    induction f using Quotient.ind
    case _ f =>
    simp [CategoryStruct.id, CategoryStruct.comp, BSetHom.comp, BSetFun.comp]
  assoc {X Y Z W} f g h := by
    induction f using Quotient.ind
    case _ f =>
    induction g using Quotient.ind
    case _ g =>
    induction h using Quotient.ind
    case _ h =>
    simp [CategoryStruct.comp, f.assoc]

open CategoryTheory.Limits

instance : OfNat BSet 0 where
  ofNat := {
    eq := λ _x _y => False
    symm := λ x y h => by cases h
    trans := λ x y z h => by cases h
    cotrans := λ x y _ z =>
      Or.inl <| by
      simp at *
    dec := λ x y => isFalse (by simp)
  }

instance : Unique ((0 : BSet) ⟶ Y) where
  default := ⟦ {
    toFun := id
    welldefined := λ h => by cases h
  } ⟧
  uniq f := by
    induction f using Quotient.ind
    case a f =>
    simp [default]
    apply Quotient.sound
    intros _ _ h
    cases h

instance : OfNat BSet 1 where
  ofNat := {
    eq := λ _x _y => true
    symm := λ x y _h => rfl
    trans := λ x y z _h₁ _h₂ => rfl
    cotrans := λ x y h z => by simp at h
    dec := λ x y => isTrue (by simp)
  }

instance : Unique (Y ⟶ (1 : BSet)) where
  default := ⟦ {
    toFun := λ _ => Data.bit false
    welldefined := λ _ => by simp [OfNat.ofNat]
  } ⟧
  uniq f := by
    induction f using Quotient.ind
    case a f =>
    simp [default]
    apply Quotient.sound
    intros _ _ _
    rfl

instance : HasTerminal BSet := hasTerminal_of_unique 1

instance : HasInitial BSet := hasInitial_of_unique 0

open Data

def BSet.mul (X Y : BSet) : BSet where
  eq a b :=
    match a, b with
    | a₁ -:- a₂, b₁ -:- b₂ => X.eq a₁ b₁ ∧ Y.eq a₂ b₂
    | _, _ => False
  symm a b h :=
    match a, b with
    | a₁ -:- a₂, b₁ -:- b₂ => by
      simp at *
      exact ⟨X.symm h.1, Y.symm h.2⟩
    | bit _, _ => by
      simp at h
  trans a b c a_eq_b b_eq_c :=
    match a, b, c with
      | x₁ -:- x₂
      , y₁ -:- y₂
      , z₁ -:- z₂ => by
        simp at *
        apply And.intro (X.trans a_eq_b.1 b_eq_c.1) (Y.trans a_eq_b.2 b_eq_c.2)
  cotrans a b a_ne_b c :=
    match c, a, b with
    | bit _, _, _ => by simp
    | _, bit _, _ => by simp
    | _, _, bit _ => by simp
    | c₁ -:- c₂
    , a₁ -:- a₂
    , b₁ -:- b₂ => by
      simp at *
      simp_rw [imp_iff_not_or, Bool.not_eq_true] at *
      cases a_ne_b
      case inl h₁ =>
        have := X.cotrans _ _ h₁ c₁
        cases this with
        | inl h => simp_all only [true_or]
        | inr h_1 => simp_all only [true_or, or_true]
      case inr h₂ =>
        have := Y.cotrans _ _ h₂ c₂
        cases this with
        | inl h => simp_all only [or_true, true_or]
        | inr h_1 => simp_all only [or_true]

  dec a b :=
    match a, b with
    | bit _, _ => isFalse (by simp)
    | _, bit _ => isFalse (by simp)
    | a₁ -:- a₂, b₁ -:- b₂ =>
      if h : X.eq a₁ b₁ ∧ Y.eq a₂ b₂
      then isTrue (by simp; exact h)
      else isFalse (by simp at *; exact h)

instance : HasBinaryProducts BSet :=
