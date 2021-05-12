module papers.CalculatingDependentlyTypedCompilers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; _+_)
open import Data.Bool using (Bool; if_then_else_; true; false; _∨_; _∧_)
open import Data.List using (List; _∷_; [])

variable
  T T′ : Set

variable
  S S′ S″ : List Set

{-
The Exp type represents the syntax of the language
we wish to compile.
-}
data Exp : Set → Set where
  val  : T → Exp T
  add  : Exp ℕ → Exp ℕ → Exp ℕ
  if   : Exp Bool → Exp T → Exp T → Exp T

infixr 20 _▹_

data Stack : List Set → Set where
  ε : Stack []
  _▹_ : T → Stack S → Stack (T ∷ S)

eval : Exp T → T
eval (val x)    = x
eval (add x y)  = eval x + eval y
eval (if b x y) = if eval b then eval x else eval y

dist-if : ∀ (f : T → T′) → ∀ { b : Bool } → ∀ { x y : T } → 
  (f (if b then x else y)) ≡ (if b then (f x) else (f y))
dist-if f {false} {x} {y} = refl
dist-if f {true} {x} {y}  = refl


module CompilerSpecification where
  {-
  Code repesents the syntax of the language we will to 
  compile into.
  -}
  data Code : List Set → List Set → Set₁ where
    PUSH  : T → Code S (T ∷ S)
    _+++_ : Code S S′ → Code S′ S″ → Code S S″
    IF    : Code S S′ → Code S S′ → Code (Bool ∷ S) S′ 
    ADD   : Code (ℕ ∷ ℕ ∷ S) (ℕ ∷ S)

  {-
  The compile function compiles expressions into 
  values in the target language.
  -}
  compile : Exp T → Code S (T ∷ S)
  compile (val x) = PUSH x
  compile (add x y) = (compile x +++ compile y) +++ ADD
  compile (if b x y) = compile b +++ IF (compile x) (compile y)

  {-
  exec is a function that runs compiled code
  -}
  exec : Code S S′ → Stack S → Stack S′
  exec (PUSH x) s = x ▹ s
  exec (c +++ c₁) s = exec c₁ (exec c s)
  exec (IF c c₁) (b ▹ s) = if b then (exec c s) else (exec c₁ s)
  exec ADD (m ▹ n ▹ s) = (n + m) ▹ s

  {-
  Compiling some expression then executing it against a given stack
  produces the same result as directly evaluating the expression
  and pushing that result onto the stack.
  -}
  correctness : (e : Exp T) → (s : Stack S) → eval e ▹ s ≡ exec (compile e) s
  correctness (val x) s = refl
  correctness (add x y) s =
    begin
      eval (add x y) ▹ s
    ≡⟨⟩
      (eval x + eval y) ▹ s
    ≡⟨⟩
      exec ADD (eval y ▹ eval x ▹ s)
    ≡⟨ cong (λ t → exec ADD (eval y ▹ t)) (correctness x s) ⟩
      exec ADD (eval y ▹ exec (compile x) s)
    ≡⟨ cong (exec ADD) (correctness y (exec (compile x) s)) ⟩
      exec ADD (exec (compile y) (exec (compile x) s))
    ≡⟨⟩
      exec ADD (exec (compile x +++ compile y) s)
    ≡⟨⟩
      exec ((compile x +++ compile y) +++ ADD) s
    ≡⟨⟩
      exec (compile (add x y)) s
    ∎
  correctness (if b x y) s = 
    begin
      eval (if b x y) ▹ s
    ≡⟨⟩
      (if eval b then eval x else eval y) ▹ s
    ≡⟨ dist-if (_▹ s) ⟩ -- distribution over if
      (if eval b then (eval x ▹ s) else (eval y ▹ s))
    ≡⟨ cong (λ t → if eval b then t else (eval y ▹ s)) (correctness x s) ⟩ -- Induction hypothesis
      (if eval b then (exec (compile x) s) else (eval y ▹ s))
    ≡⟨ cong (λ t → if eval b then (exec (compile x) s) else t) (correctness y s) ⟩ -- Induction hypothesis
      (if eval b then (exec (compile x) s) else (exec (compile y) s))
    ≡⟨⟩
      exec (IF (compile x) (compile y)) (eval b ▹ s)
    ≡⟨ cong (λ t → exec (IF (compile x) (compile y)) t) (correctness b s) ⟩ -- Induction hypothesis
      exec (IF (compile x) (compile y)) (exec (compile b) s) 
    ≡⟨⟩ -- by definition
      exec (compile b +++ IF (compile x) (compile y)) s
    ≡⟨⟩ -- by definition
      exec (compile (if b x y)) s
    ∎

{-
The basic form of this calculation was to start from the assumption that 
eval e ▹ s = exec (compile e) s in all cases, and then work backwards
to fill in the required definitions. (i.e. the bytecode ops and compilation rules.)

E.g. in the add case, we begin with eval (add x y) ▹ s - i.e. the 
top of the stack contains the result of evaluating (add x y) in our
language. We then apply the definition of eval to rewrite this as
(eval x + eval y) ▹ s. We know we want this to look like exec c s 
for some c, so we define a new bytecode operation ADD, such that
exec ADD (m ▹ n ▹ s) = (n + m) ▹ s. Now we use this operation to
rewrite the equation, so we're left with exec ADD (eval y ▹ eval x ▹ s).

Next we use induction to convert eval x ▹ s into exec (compile x) s,
then apply the induction hypothesis a second time to convert 
eval y ▹ exec (compile x) s into exec (compile y) (exec (compile x) s).

Now we're left with exec ADD (exec (compile y) (exec (compile x) s)). 
We'd like to simplify the second argument to the first exec down to just
s, so we need to convert x and y from exec'd stack values back to
bytecode elements. We define +++ as a way of combining two Code values
into a single one, and then we use its definition twice to rewrite the
equation as exec ((compile x +++ compile y) +++ ADD) s.

This is in the form (exec c s) that we set out to construct, so we can 
conclude that compile (add x y) must be equal to (compile x +++ compile y) +++ ADD,
which seems sensible & valid.
-}

module CodeContinuations where
  data Code : List Set → List Set → Set₁ where
    PUSH : T → Code (T ∷ S) S′ → Code S S′
    ADD  : Code (ℕ ∷ S) S′ → Code (ℕ ∷ ℕ ∷ S) S′
    IF   : Code S S′ → Code S S′ → Code (Bool ∷ S) S′
    HALT : Code S S

  exec : Code S S′ → Stack S → Stack S′
  exec (PUSH x c) s        = exec c (x ▹ s)
  exec (ADD c) (m ▹ n ▹ s) = exec c ((n + m) ▹ s)
  exec (IF c c₁) (b ▹ s)   = if b then exec c s else exec c₁ s
  exec HALT s              = s

  {-
  A generalisation of compile which takes code to be executed 
  after the compiled code as an argument.
  -}
  comp : Exp T → Code (T ∷ S) S′ → Code S S′
  comp (val x) c    = PUSH x c
  comp (if b x y) c = comp b (IF (comp x c) (comp y c))
  comp (add x y) c  = comp x (comp y (ADD c))

  compile : Exp T → Code S (T ∷ S)
  compile e = comp e HALT

  {-
  N.b. I had originally expressed this as exec (comp e c) s ≡ exec c (eval e ▹ s)
  but Agda wouldn't typecheck the proof for some reason. :'(
  -}
  correctness : (c : Code (T ∷ S) S′) → (e : Exp T) → (s : Stack S) 
    → exec c (eval e ▹ s) ≡ exec (comp e c) s
  correctness c (val x) s    = refl
  correctness c (if b x y) s = begin
      exec c ((eval (if b x y)) ▹ s)
    ≡⟨⟩
      exec c ((if eval b then eval x else eval y) ▹ s)
    ≡⟨ cong (exec c) (dist-if (_▹ s)) ⟩ -- distributivity of if
      exec c (if eval b then (eval x ▹ s) else (eval y ▹ s))
    ≡⟨ dist-if (exec c) ⟩ -- distributivity of if
      (if eval b then exec c (eval x ▹ s) else exec c (eval y ▹ s))
    ≡⟨ cong (λ z → if eval b then z else exec c (eval y ▹ s)) (correctness c x s) ⟩
      (if eval b then exec (comp x c) s else exec c (eval y ▹ s))
    ≡⟨ cong (λ z → if eval b then exec (comp x c) s else z) (correctness c y s) ⟩
      (if eval b then exec (comp x c) s else exec (comp y c) s)
    ≡⟨⟩
      exec (IF (comp x c) (comp y c)) (eval b ▹ s)
    ≡⟨ correctness ((IF (comp x c) (comp y c))) b s ⟩
      exec (comp b (IF (comp x c) (comp y c))) s 
    ≡⟨⟩
      exec (comp (if b x y) c) s
    ∎ 
  correctness c (add x y) s  = begin
      exec c ((eval (add x y )) ▹ s)
    ≡⟨⟩
      exec c ((eval x + eval y) ▹ s)
    ≡⟨⟩
      exec (ADD c) (eval y ▹ eval x ▹ s)
    ≡⟨ correctness (ADD c) y (eval x ▹ s) ⟩
      exec (comp y (ADD c)) (eval x ▹ s)
    ≡⟨ correctness ((comp y (ADD c))) x s ⟩
      exec (comp (add x y) c) s
    ∎

  compile-correctness : (e : Exp T) → (s : Stack S) → eval e ▹ s ≡ exec (compile e) s
  compile-correctness e s = correctness HALT e s