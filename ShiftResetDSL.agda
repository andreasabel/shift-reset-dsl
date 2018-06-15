module ShiftResetDSL where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Sum

-- reset : A → C
-- shift : ((A → B) → C) → A
-- 1 ∷ ⟨ 2 + shift k. k (k 3) ∷ [] ⟩

module Definitional where

  M : (B α ω : Set) → Set
  M B α ω = (B → α) → ω

  Pure : (B : Set) → Set₁
  Pure B = ∀{α} → M B α α

  return : ∀{B} → B → Pure B
  return x k = k x

  bind : ∀{α β ω A B} → M A β ω → (A → M B α β) → M B α ω
  bind m f k = m λ a → f a k

  shift : ∀{α β ω B} → ((k : B → α) → M β β ω) → M B α ω
  shift f k = f k id

  reset : ∀{α β B} → M β β B → M B α α
  reset m k = k (m id)

  fmap : ∀{α ω A B : Set} (f : A → B) (m : M A α ω) → M B α ω
  fmap f m = bind m λ a → return (f a)

  -- Special instance: exceptions
  -- handle (... throw e ...)

  throw : ∀{E A B} (e : E) → M A (E ⊎ B) (E ⊎ B)
  throw e = shift λ _ →  return (inj₁ e)

  handle : ∀{E B} → M B (E ⊎ B) (E ⊎ B) → Pure (E ⊎ B)
  handle m = reset (fmap inj₂ m)



-- α = initial answer type
-- ω = final answer type

-- Think  M B α ω = (B → α) → ω

data M (B : Set) : (α ω : Set) → Set₁ where
  return : ∀{α} → B → M B α α
  bind   : ∀{α β ω A} → M A β ω → (A → M B α β) → M B α ω
  shift  : ∀{α β ω} → ((k : B → α) → M β β ω) → M B α ω
  -- reset  : ∀{α β} → M β β B → M B α α

-- Pure contexts can be modelled using return and bind

fmap : ∀{α ω A B : Set} (e : A → B) (m : M A α ω) → M B α ω
fmap e m = bind m (return ∘ e)

-- Application of an impure dependent function to a pure argument
-- is just Agda's application.

app : ∀{α ω A B : Set} {C : A → Set} → ((x : A) → M (C x) α ω) → (a : A) → M (C a) α ω
app f a = f a

-- Evaluation representing evaluation contexts as functions

mutual
  eval : ∀{α ω C} → M C α ω → (C → α) → ω
  eval (return x) k = k x
  eval (bind m f) k = eval m (λ a → eval (f a) k)
  eval (shift f)  k = eval' (f k)
  -- eval (reset m)  k = k (eval' m)

  eval' : ∀{α ω} → M α α ω → ω
  eval' m = eval m id

eval-fmap : ∀{α ω A B : Set} (e : A → B) (m : M A α ω) (k : B → α) →
  eval (fmap e m) k ≡ eval m (k ∘ e)
eval-fmap e m k = refl

-- Reset is definable

resetM : ∀{α β B} → M β β B → M B α α
resetM m = return (eval' m)
