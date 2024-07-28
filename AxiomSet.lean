import Mathlib.Data.Set.Lattice
open Classical

structure Ring (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  neg : α → α
  add_comm : ∀ x y : α, add x y = add y x
  mul_comm : ∀ x y : α, mul x y = mul y x
  add_assoc : ∀ x y z : α, add x (add y z)=add (add x y) z
  mul_assoc : ∀ x y z : α, mul x (mul y z)=mul (mul x y) z
  distrib : ∀ x y z : α, mul x (add y z) = add (mul x y) (mul x z)
  add_zero : ∀ x : α, add x zero = x
  add_inv : ∀ x : α, add x (neg x) = zero
  mul_ident : ∀ x : α, mul x one = x


--P1 : zero is unique
theorem zero_unique {α : Type} (R : Ring α) (z z' : α)
  (hz : ∀ x : α, R.add x z = x) (hz' : ∀ x : α, R.add x z' = x) : z = z' :=
  have h1 : R.add z z' = z := by rw [hz']
  have h2 : R.add z' z = z' := by rw [hz]
  have h3 : R.add z z' = R.add z' z := by rw [R.add_comm]
  have h4 : z = z' := by rw [←h1, h3, h2]
  by exact h4

--P2 : 0 = 1 is False, salvage see theorem `one_not_zero` for `OrderedRing`

--P3 : ` a + b = a + b' → b = b' `
theorem right_add_eq {α : Type} (R : Ring α) (a b b' : α)
  (h : R.add a b = R.add a b') : b = b' := by
  have h0 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) (R.add a b') := by
    rw [h]
  have h1 : b = R.add (R.neg a) (R.add a b) := by
    rw [R.add_assoc (R.neg a) a b ]
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.add_comm (R.zero) b]
    rw [R.add_zero]
  have h2 : b' = R.add (R.neg a) (R.add a b') := by
    rw [R.add_assoc (R.neg a) a b']
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.add_comm (R.zero) b']
    rw [R.add_zero]
  rw [h2]
  rw [h1]
  exact h0

--P4 (1) : inverse is unique
theorem inv_unique {α : Type} (R : Ring α) (a b b' : α)
  (h : R.add a b = R.zero) (h' : R.add a b' = R.zero) : b = b' :=
  have h0 : R.add a b = R.add a b' := by
    rw [h]
    rw [h']
  suffices h0': R.add a b = R.add a b' from (right_add_eq R a b b' h0')
  show R.add a b = R.add a b' from h0
  --`show b = b' from (right_add_eq R a b b' h0)`

--P4 (2) : `-(-a) = a`
theorem inv_inv {α : Type} (R : Ring α) (a : α) : R.neg (R.neg a) = a :=
  have h0 : R.add (R.neg a) (R.neg (R.neg a)) = R.zero := by
    rw [R.add_inv]
  have h1 : R.add (R.neg a) a = R.zero := by
    rw [R.add_comm]
    rw [R.add_inv]
  inv_unique R (R.neg a) (R.neg (R.neg a)) a h0 h1

--P4 (3) : ` -(ab) = -a(b) `
lemma mul_zero {α : Type} (R: Ring α) (a : α) : R.mul a R.zero = R.zero := -- `a * 0 =a`
  have h0 : R.add R.zero R.zero = R.zero := by rw [R.add_zero] --0 + 0 = 0
  have h1 : R.add (R.mul a R.zero) (R.mul a R.zero ) = R.mul a R.zero:= by --a0 + a0 = a0
    rw (config := {occs := .pos [3]}) [←h0]
    rw [R.distrib]
  have h2 : R.add (R.mul a R.zero) R.zero = R.mul a R.zero := by rw [R.add_zero] --a0 + 0 = a0
  have h3 : R.add (R.mul a R.zero) (R.mul a R.zero) = R.add (R.mul a R.zero) R.zero := by -- a0 + a0 = a0 + 0
    rw [h1]
    rw [h2]
  show R.mul a R.zero = R.zero from (right_add_eq R (R.mul a R.zero) (R.mul a R.zero) R.zero h3)

theorem inv_assoc {α : Type} (R : Ring α) (a b : α) : R.neg (R.mul a b) = R.mul (R.neg a) b :=
  have h1 : R.add (R.mul a b) (R.neg (R.mul a b))= R.zero := by
    rw [R.add_inv]
  have h2' : R.add (R.mul a b) (R.mul (R.neg a) b) = R.mul (R.add (R.neg a) a) b := by
    rw [R.mul_comm (R.add (R.neg a) a) b]
    rw [R.distrib b (R.neg a) a]
    rw [R.mul_comm (R.neg a) b]
    rw [R.mul_comm a b]
    rw [R.add_comm (R.mul b (R.neg a)) (R.mul b a)]
  have h2 : R.add (R.mul a b) (R.mul (R.neg a) b) = R.zero := by
    rw [h2']
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.mul_comm R.zero b]
    rw [mul_zero R b]
  have h3 : R.add (R.mul a b) (R.mul (R.neg a) b) = R.add (R.mul a b) (R.neg (R.mul a b)) := by
    rw [h2]
    rw [h1]
  show R.neg (R.mul a b) = R.mul (R.neg a) b from (right_add_eq R (R.mul a b) (R.mul (R.neg a) b) (R.neg (R.mul a b)) h3).symm

--P4 (4) : ` (-a)(-b) = ab `
theorem inv_mul_inv {α : Type} (R : Ring α) (a b : α) : R.mul (R.neg a) (R.neg b) = R.mul a b := by
  rw [←inv_assoc R a (R.neg b)]
  rw [R.mul_comm]
  rw [inv_assoc]
  rw [inv_inv]
  rw [R.mul_comm]

--P4 (5) : ` -a = (-1) a `
theorem inv_eq_mul_neg1 {α : Type} (R : Ring α) (a : α) : R.neg a = R.mul (R.neg R.one) a := by
 rw [←inv_assoc]
 rw [R.mul_comm R.one a]
 rw [R.mul_ident]

--P5 : subtraction definition
def Ring.sub {α : Type} (R : Ring α) (x y : α) : α :=
  R.add x (R.neg y)

--P6 salvage : ( a ≠ 0, ab = ab' → b = b' ) ⇔ ( ab = 0 → a = 0 ∨ b = 0 )
lemma add_inv_to_zero {α : Type} (R : Ring α) (a b: α) (h : R.add a (R.neg b) = R.zero) :  a = b :=by
  have h0 : R.add (R.add a (R.neg b)) b = b := by
    rw (config := {occs := .pos [3]}) [←(R.add_zero b)]
    rw [R.add_comm b R.zero]
    rw [h]
  have h2 : a = b := by
    rw [←R.add_zero a]
    rw [←R.add_inv b]
    rw [R.add_comm b (R.neg b)]
    rw [R.add_assoc]
    exact h0
  exact h2

def is_integral_domain {α : Type}(R : Ring α):=
  ∀ a b, (R.mul a b = R.zero → a = R.zero ∨ b = R.zero)

def is_zero {α : Type}(R : Ring α)(x : α):=
  x = R.zero

theorem mul_inv_zero_divisor {α : Type} (R : Ring α) :
  (∀ a b b': α, (a ≠ R.zero)→(R.mul a b = R.mul a b' → b = b')) ↔ is_integral_domain R:= by
  unfold is_integral_domain
  constructor
  · intro h
    intro x y
    intro h'
    have h'' : R.mul x y = R.mul x R.zero := by
      rw [mul_zero]
      exact h'
    --apply h h''
    specialize h x y R.zero
    have h2 : x ≠ R.zero → R.mul x y = R.mul x R.zero → y = R.zero := by
      intro htmp
      intro htmp'
      apply h htmp htmp'
    by_cases h3 : is_zero R x
    · left
      exact h3
    · right
      apply h2 h3 h''

  · rintro h
    intro x y y'
    intro h'
    intro h''
    have h1 : R.mul x (R.add y (R.neg y'))  = R.zero := by
      rw [R.distrib]
      rw (config := {occs := .pos [2]}) [R.mul_comm]
      rw [←inv_assoc]
      rw (config := {occs := .pos [2]}) [R.mul_comm]
      rw [h'']
      apply R.add_inv
    specialize h x (R.add y (R.neg y'))
    have h2 : x = R.zero ∨ R.add y (R.neg y') = R.zero := by
      apply h h1

    rcases h2 with h3 | h3
    exfalso
    exact h' h3
    have h4 : y = y' := by
      apply add_inv_to_zero R y y' h3
    exact h4


structure OrderedRing (α : Type) extends Ring α where
  P : Set α -- α → Prop
  P_nonempty : P.Nonempty -- ∃ x : α , P α
  P_add : ∀ a b : α, a ∈ P → b ∈ P → add a b ∈ P
  P_mul : ∀ a b : α, a ∈ P → b ∈ P → mul a b ∈ P
  trichotomy1 : zero ∉ P
  trichotomy2 : ∀ a , a ∈ P → neg a ∉ P
  trichotomy3 : ∀ a , a ∉ P → a ≠ zero → neg a ∈ P

-- P7 : `1 ∈ P ∧ -1 ∉ P`
lemma neg_one_mul_neg_one {α : Type} (R : Ring α) : R.mul (R.neg R.one) (R.neg R.one) = R.one := by
  rw [inv_mul_inv R R.one R.one]
  rw [R.mul_ident]

--salvage p2 here: one is not zero in an ordered ring
lemma one_not_zero {α : Type} (R : OrderedRing α) : R.one ≠ R.zero := by
  by_contra h
  have h1 : ∀ a : α, R.mul a R.zero = R.zero := by
    intro a
    rw [mul_zero R.toRing a]
  have h2 : ∀ a : α, R.mul a R.zero = a := by
    intro a
    rw [←h]
    rw [R.mul_ident]
  have h3 : ∀ a : α, a = R.zero := by
    intro a
    rw [←h2 a]
    rw [h1]
  have h4 : ∀ a : α, a ∉ R.P := by
    intro a
    rw [h3 a]
    exact R.trichotomy1
  have h5 := R.P_nonempty
  rcases h5 with ⟨ b , h6 ⟩
  have h7 : b ∉ R.P := by
    apply h4
  exact h7 h6
  -- apply h7 exact h6

lemma neg_one_not_zero {α : Type} (R : OrderedRing α) : R.neg R.one ≠ R.zero := by
  by_contra h
  have h1 : R.mul (R.neg R.one) (R.neg R.one) = R.mul (R.neg R.one) (R.zero) := by
    rw [h]
  have h2 : R.one = R.zero := by
    rw [←neg_one_mul_neg_one]
    rw [←mul_zero R.toRing (R.neg R.one)]
    exact h1
  exact one_not_zero R h2


theorem neg_one_not_pos {α : Type} (R : OrderedRing α) : R.neg R.one ∉ R.P := by
  by_contra h1
  have h2 : R.mul (R.neg R.one) (R.neg R.one) = R.one := by rw [neg_one_mul_neg_one R.toRing]
  have h3 : R.one ∈ R.P := by
    rw [←h2]
    apply R.P_mul
    exact h1
    exact h1
  have h4 : R.neg R.one ∉ R.P := by
    apply R.trichotomy2 (R.one) h3
  contradiction

theorem one_pos {α : Type} (R : OrderedRing α) : R.one ∈ R.P := by
  rw [←(inv_inv R.toRing R.one)]
  apply R.trichotomy3
  exact neg_one_not_pos R
  exact neg_one_not_zero R

--P8 : `(a ≤ b), (b ≤ c) → (a ≤ c)`
def OrderedRing.lt {α : Type} (R : OrderedRing α) (a b : α) : Prop :=
  R.add a (R.neg b) ∈ R.P

def OrderedRing.le {α : Type} (R : OrderedRing α) (a b : α) : Prop :=
  R.add a (R.neg b) ∈ R.P ∨ a = b

def is_lt {α : Type} (R : OrderedRing α) (a b : α) : Prop :=
  R.lt a b

def is_eq {α : Type} (a b : α) : Prop :=
  a = b

theorem le_transitive {α : Type} (R : OrderedRing α) (a b c :α) (h : R.le a b) (h' : R.le b c) : R.le a c :=by
  unfold OrderedRing.le
  have h : R.lt a b ∨ a = b := h
  have h' : R.lt b c ∨ b = c := h'
  · by_cases h0 : is_lt R a b
    · by_cases h0' : is_lt R b c
      left
      have h1 : R.add a (R.neg b) ∈ R.P := h0
      have h1' : R.add b (R.neg c) ∈ R.P :=h0'
      have h1'' : R.add (R.add a (R.neg b)) (R.add b (R.neg c)) ∈ R.P := by
        apply R.P_add
        exact h1
        exact h1'
      rw [←(R.add_zero a)]
      rw [←(R.add_inv b)]
      rw (config := {occs := .pos [3]}) [R.add_comm]
      rw [R.add_assoc a (R.neg b) b]
      rw [←(R.add_assoc (R.add a (R.neg b)) b (R.neg c))]
      exact h1''

      left
      have h2 : R.add a (R.neg b) ∈ R.P := h0
      have h2' : R.add b (R.neg c) ∉ R.P := h0'
      rcases h' with tmp | tmp
      have tmp' : R.add b (R.neg c) ∈ R.P := tmp
      exfalso
      exact h2' tmp'
      --other rcases
      rw [←tmp]
      exact h2

    · by_cases h0' : is_lt R b c
      left
      have h3 : R.add a (R.neg b) ∉ R.P := h0
      have h3' : R.add b (R.neg c) ∈ R.P := h0'
      rcases h with tmp | tmp
      have tmp' : R.add a (R.neg b) ∈ R.P := tmp
      exfalso
      exact h3 tmp'
      --other rcases
      rw [tmp]
      exact h3'

      right
      have h4 : R.add a (R.neg b) ∉ R.P := h0
      have h4' : R.add b (R.neg c) ∉ R.P := h0'
      rcases h with tmp | tmp
      have tmp' : R.add a (R.neg b) ∈ R.P := tmp
      exfalso
      exact h4 tmp'
      --other rcases
      rcases h' with tmp'' | tmp''
      have tmp''' : R.add b (R.neg c) ∈ R.P := tmp''
      exfalso
      exact h4' tmp'''
      rw [tmp]
      exact tmp''

--P9 : exactly one is true : ` a < b `,  ` a = b ` ,  ` a > b `
def OrderedRing.gt {α : Type} (R : OrderedRing α) (a b : α) : Prop := -- b > a
  R.add b (R.neg a) ∈ R.P

def OrderedRing.ge {α : Type} (R : OrderedRing α) (a b : α) : Prop := -- b > a
  R.add b (R.neg a) ∈ R.P ∨ a = b

def is_gt {α : Type} (R : OrderedRing α) (a b : α) : Prop :=
  R.gt a b

lemma inv_distrib_add {α : Type} (R : Ring α) (a b : α) : R.neg (R.add a b) = R.add (R.neg a) (R.neg b):= by
  rw [inv_eq_mul_neg1]
  rw [R.distrib]
  rw [←inv_eq_mul_neg1]
  rw [←inv_eq_mul_neg1]

lemma inv_zero_eq_zero {α : Type} (R : Ring α) : R.neg R.zero = R.zero := by
  have h0 : R.add R.zero (R.neg R.zero) = R.zero := by
    rw [R.add_inv]
  have h1 : R.add R.zero R.zero = R.zero := by
    rw [R.add_zero]
  apply inv_unique R R.zero (R.neg R.zero) R.zero h0 h1

theorem lt_eq_gt {α : Type} (R : OrderedRing α) (a b : α) : ((R.lt a b) ∧ ¬(a = b) ∧ ¬(R.gt a b)) ∨
                                                            (¬(R.lt a b) ∧ (a = b) ∧ ¬(R.gt a b)) ∨
                                                            (¬(R.lt a b) ∧ ¬(a = b) ∧ (R.gt a b)) := by
  unfold OrderedRing.lt
  unfold OrderedRing.gt
  by_cases h0 : is_lt R a b
  · left
    have h0_0 : R.add a (R.neg b) ∈ R.P := by
      exact h0

    apply And.intro
    exact h0_0

    apply And.intro
    intro h0_1
    have h0_1' : R.add a (R.neg b) = R.zero := by
      rw [h0_1]
      rw [R.add_inv]
    have h0_1'' : R.add a (R.neg b) ∉ R.P := by
      rw [h0_1']
      exact R.trichotomy1
    exact h0_1'' h0_0

    have h0_2 : R.neg (R.add b (R.neg a) ) = R.add (R.neg b) a := by
      rw [inv_distrib_add]
      rw [inv_inv]
    have h0_2' : R.neg (R.add b (R.neg a) ) ∈ R.P := by
      rw [h0_2]
      rw [R.add_comm]
      exact h0_0
    have h0_2''p : R.neg (R.neg (R.add b (R.neg a) )) = R.add b (R.neg a) := by
      rw [inv_inv]
    have h0_2'' : R.add b (R.neg a) ∉ R.P := by
      rw [←h0_2''p]
      apply R.trichotomy2 (R.neg (R.add b (R.neg a) )) h0_2'
    exact h0_2''
  · right
    have h1_0 : R.add a (R.neg b) ∉ R.P := by
      exact h0
    by_cases g0 : is_eq a b
    · left
      have g0_0 : a = b := by
        exact g0

      apply And.intro
      exact h1_0

      apply And.intro
      exact g0_0

      have g0_2 : R.add b (R.neg a) ∉ R.P := by
        rw [g0]
        rw [R.add_inv]
        exact R.trichotomy1
      exact g0_2
    · right
      apply And.intro
      exact h1_0

      apply And.intro
      exact g0

      have g1_2 : R.neg (R.add b (R.neg a)) ∉ R.P := by
        rw [inv_distrib_add]
        rw [inv_inv]
        rw [R.add_comm]
        exact h1_0
      have g1_2' : R.add b (R.neg a) = R.neg (R.neg (R.add b (R.neg a))) := by
        rw [inv_inv]
      have g1_2'' : R.neg (R.add b (R.neg a)) ≠ R.zero := by
        rw [inv_distrib_add R.toRing b (R.neg a)]
        rw [inv_inv]
        rw [R.add_comm]
        intro h
        have g1_2''' : a = b := by
          apply add_inv_to_zero R.toRing a b h
        exact g0 g1_2'''
      have g1_2''' : R.add b (R.neg a) ∈ R.P := by
        rw [g1_2']
        apply R.trichotomy3 (R.neg (R.add b (R.neg a))) g1_2 g1_2''
      exact g1_2'''


--P10 : ( b ≤ a , y ≤ x) → ( b + y ≤ a + x )
theorem lt_add {α : Type} (R : OrderedRing α) (a b x y: α) (h : R.le a b) (h' : R.le x y ) :
  R.le (R.add a x) (R.add b y) := by
  unfold OrderedRing.le
  · by_cases h0 : is_lt R a b
    · by_cases h0' : is_lt R x y
      left
      have h1 : R.add a (R.neg b) ∈ R.P := h0
      have h1' : R.add x (R.neg y) ∈ R.P := h0'
      rw [inv_eq_mul_neg1 R.toRing]
      rw [R.distrib]
      rw [←inv_eq_mul_neg1 R.toRing b]
      rw [←inv_eq_mul_neg1 R.toRing y]
      rw (config := {occs := .pos [2]}) [R.add_comm]
      rw [R.add_assoc]
      rw [←(R.add_assoc x a (R.neg b))]
      rw (config := {occs := .pos [2]}) [R.add_comm]
      rw [←(R.add_assoc)]
      apply R.P_add
      exact h1
      exact h1'

      left
      have h2 : R.add a (R.neg b) ∈ R.P := h0
      have h2' : R.add x (R.neg y) ∉ R.P := h0'
      rcases h' with tmp | tmp
      exfalso
      exact h2' tmp
      --other rcases
      have tmp' : R.add x (R.neg y) = R.zero := by
        rw [tmp]
        rw [R.add_inv]
      rw [inv_distrib_add]
      rw [R.add_comm (R.neg b) (R.neg y)]
      rw [←R.add_assoc a x (R.add (R.neg y) (R.neg b))]
      rw [R.add_assoc x (R.neg y) (R.neg b)]
      rw [R.add_comm (R.add x (R.neg y)) (R.neg b)]
      rw [R.add_assoc]
      rw [tmp']
      rw [R.add_zero]
      exact h2

    · by_cases h0' : is_lt R x y
      left
      have h3 : R.add a (R.neg b) ∉ R.P := h0
      have h3' : R.add x (R.neg y) ∈ R.P := h0'
      rcases h with tmp | tmp
      exfalso
      exact h3 tmp
      --other rcases
      have tmp' : R.add a (R.neg b) = R.zero := by
        rw [tmp]
        rw [R.add_inv]
      rw [inv_distrib_add]
      rw [R.add_comm (R.neg b) (R.neg y)]
      rw [←R.add_assoc a x (R.add (R.neg y) (R.neg b))]
      rw [R.add_assoc x (R.neg y) (R.neg b)]
      rw [R.add_comm (R.add x (R.neg y)) (R.neg b)]
      rw [R.add_assoc]
      rw [tmp']
      rw [R.add_comm]
      rw [R.add_zero]
      exact h3'

      right
      have h4 : R.add a (R.neg b) ∉ R.P := h0
      have h4' : R.add x (R.neg y) ∉ R.P := h0'
      rcases h with tmp | tmp
      exfalso
      exact h4 tmp
      have h4'' : x = y := by
        rcases h' with tmp' | tmp'
        exfalso
        exact h4' tmp'
        exact tmp'
      rw [tmp]
      rw [h4'']
