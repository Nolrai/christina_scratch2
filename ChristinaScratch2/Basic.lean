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
  cotrans : ∀ {x y}, eq x y = false → ∀ z, eq x z = false ∨ eq y z = false

def BSet.def (X : BSet) (x : Data) : Prop := X.eq x x

instance : DecidablePred (BSet.def X) := λ d =>
  if h : X.eq d d
    then isTrue h
    else isFalse h

theorem BSet.def_of_eq_right {X : BSet} (a_eq_b : X.eq a b) : X.def b :=
  not_not.mp <| λ b_not_def ↦ by
    simp [BSet.def] at *
    have b_ne_a := X.cotrans b_not_def a
    rw [or_self] at *
    rw [X.symm a_eq_b] at b_ne_a
    · cases b_ne_a

-- This suffices to show that it both takes defined to defined,
-- and equal to equal.
abbrev BSetFun (dom cod : BSet) :=
  { f : Data → Data
  // ∀ {x y}, dom.eq x y → cod.eq (f x) (f y)
  }

instance : FunLike (BSetFun dom cod) Data Data where
  coe f := f.val
  coe_injective' := by
    intros x y h
    ext
    simp at h
    rw [h]

def BSetFun.comp {X Y Z} (f : BSetFun X Y) (g : BSetFun Y Z) : BSetFun X Z := {
    val := g.val ∘ f.val
    property := g.property ∘ f.property
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
  ∀ {x y}, dom.eq x y → cod.eq (f x) (g y)

instance BSetFun.setoid dom cod : Setoid (BSetFun dom cod) where
  r := BSetFun.equiv
  iseqv :=
    ⟨ λ f _ _ x_eq_y => f.property x_eq_y
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
    val := id
    property := λ h ↦ h
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
    cotrans := λ {x y} _ z =>
      Or.inl <| by
      simp at *
  }

instance : Unique ((0 : BSet) ⟶ Y) where
  default := ⟦ {
    val := id
    property := λ h => by cases h
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
    cotrans := λ {x y} h z => by simp at h
  }

instance : Unique (Y ⟶ (1 : BSet)) where
  default := ⟦ {
    val := λ _ => Data.bit false
    property := λ _ => by simp [OfNat.ofNat]
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
  cotrans {a b} a_ne_b c :=
    match c, a, b, a_ne_b with
    | bit _, _, _, _ => by simp
    | _, bit _, _, _  => by simp
    | _, _, bit _, _  => by simp
    | c₁ -:- c₂
    , a₁ -:- a₂
    , b₁ -:- b₂
    , a_ne_b =>
      by
      simp at *
      have h := imp_iff_not_or.mp a_ne_b
      match h with
      | .inl h₁ =>
        rw [Bool.not_eq_true] at *
        have := X.cotrans h₁ c₁
        cases this
        case inl h₂ =>
          rw [h₂]
          tauto
        case inr h₂ =>
          rw [h₂]
          tauto
      | .inr h₂ =>
        have := Y.cotrans h₂ c₂
        tauto

@[simp]
def BSet.mul_eq_of_pair (X Y : BSet) :
  (X.mul Y).eq (x₁ -:- y₁) (x₂ -:- y₂) ↔ (X.eq x₁ x₂) ∧ (Y.eq y₁ y₂) := by
  simp [BSet.mul]

def BSet.mul_fst (X Y : BSet) : BSetHom (X.mul Y) X :=
  BSetHom.mk
    { val := λ d ↦
      match d with
      | x -:- _ => x
      | _ => bit 0
    , property := λ {x y} h => by
        cases x
        case bit => simp [mul] at h
        case pair a₁ a₂ =>
          cases y
          case bit => simp [mul] at h
          case pair b₁ b₂ =>
            simp [mul] at *
            apply h.1
    }

def BSet.mul_snd (X Y : BSet) : BSetHom (X.mul Y) Y :=
  BSetHom.mk
    { val := λ d ↦
      match d with
      | _ -:- y => y
      | _ => bit 0
    , property := λ {x y} h => by
        cases x
        case bit => simp [mul] at h
        case pair a₁ a₂ =>
          cases y
          case bit => simp [mul] at h
          case pair b₁ b₂ =>
            simp [mul] at *
            apply h.2
    }

open CategoryTheory.Limits

def BSet.pair_cone_pi (A B : BSet)
  : (Functor.const (Discrete WalkingPair)).obj (A.mul B) ⟶ Limits.pair A B where
  app LR :=
  match LR with
  | ⟨.left⟩ => BSet.mul_fst A B
  | ⟨.right⟩ => BSet.mul_snd A B
  naturality LR₁ LR₂ f :=
    have ⟨⟨h⟩⟩ := f
    match LR₁, LR₂ with
    | ⟨.left⟩,  ⟨.left⟩   => by simp
    | ⟨.right⟩, ⟨.right⟩  => by simp
    | ⟨.left⟩,  ⟨.right⟩  => by cases h
    | ⟨.right⟩, ⟨.left⟩   => by cases h

def BSet.pair_cone (X Y : BSet) : Cone (Limits.pair X Y) where
  pt := BSet.mul X Y
  π := BSet.pair_cone_pi X Y

def BSetFun.lift_pi (getX : BSetFun pt X) (getY : BSetFun pt Y) : BSetFun pt (X.mul Y) where
  val d := getX d -:- getY d
  property := λ {d₁ d₂} d_eq => by
    simp [BSet.mul]
    exact ⟨getX.property d_eq, getY.property d_eq⟩

def BSet.lift_pi {X Y : BSet} : (pt ⟶ X) → (pt ⟶ Y) → (pt ⟶ X.mul Y) := by
  apply Quotient.map₂ BSetFun.lift_pi _
  intros f₁ f₂ f_eq g₁ g₂ g_eq
  intros a b h
  have h₃ := BSet.def_of_eq_right h
  apply BSet.trans (X.mul Y) (y := (BSetFun.lift_pi f₁ g₁).val b)
  · apply (BSetFun.lift_pi f₁ g₁).property h
  apply BSet.trans (X.mul Y) (y := (BSetFun.lift_pi f₁ g₂).val b)
  · simp [BSetFun.lift_pi]
    apply And.intro (f₁.property h₃) (g_eq h₃)
  · simp [BSet.mul, BSetFun.lift_pi]
    apply And.intro
    · apply f_eq h₃
    · apply g₂.property h₃

def BSet.pair_limit_cone (X Y : BSet) : LimitCone (Limits.pair X Y) where
  cone := BSet.pair_cone X Y
  isLimit := {
    lift := λ s =>
      have ⟨pt, π⟩ := s
      have ⟨a, b⟩ := π
      have (aₗ, aᵣ) := (a ⟨.left⟩, a ⟨.right⟩)
      BSet.lift_pi aₗ aᵣ
    fac := by
      intros s j
      have ⟨pt, π⟩ := s
      have ⟨a, b⟩ := π
      have l_l : (⟨.left⟩ : Discrete WalkingPair) ⟶ ⟨.left⟩ := ⟨⟨rfl⟩⟩
      have r_r : (⟨.right⟩ : Discrete WalkingPair) ⟶ ⟨.right⟩ := ⟨⟨rfl⟩⟩
      have bₗ := (b l_l)
      have bᵣ := (b r_r)
      simp
      simp [lift_pi]
      rw [Functor.const_obj_map] at *
      

    uniq := _
  }


instance : HasBinaryProducts BSet := by
  have (X Y : BSet) : HasLimit (Limits.pair X Y) := {exists_limit := _}
  apply hasBinaryProducts_of_hasLimit_pair
