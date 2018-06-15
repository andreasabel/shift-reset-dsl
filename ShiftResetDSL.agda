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

module Interpretational where

  -- α = initial answer type
  -- ω = final answer type

  -- Think  M B α ω = (B → α) → ω

  data M (B : Set) : (α ω : Set) → Set₁ where
    return : ∀{α} → B → M B α α
    bind   : ∀{α β ω A} → M A β ω → (A → M B α β) → M B α ω
    shift  : ∀{α β ω} → ((k : B → α) → M β β ω) → M B α ω
    -- reset  : ∀{α β} → M β β B → M B α α

  Pure : (B : Set) → Set₁
  Pure B = ∀{α} → M B α α

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

  -- Pure contexts can be modelled using return and bind

  fmap' : ∀{α ω A B : Set} (f : A → B) (m : M A α ω) → M B α ω
  fmap' f m = bind m λ a → return (f a)

  eval-fmap : ∀{α ω A B : Set} (e : A → B) (m : M A α ω) (k : B → α) →
    eval (fmap' e m) k ≡ eval m (k ∘ e)
  eval-fmap e m k = refl

  -- Reset is definable

  reset : ∀{α β B} → M β β B → M B α α
  reset m = return (eval' m)

-- open Definitional
open Interpretational

-- Pure contexts can be modelled using return and bind

fmap : ∀{α ω A B : Set} (f : A → B) (m : M A α ω) → M B α ω
fmap f m = bind m λ a → return (f a)

-- Special instance: exceptions
-- handle (... throw e ...)

Except : (E B A : Set) → Set _
Except E B A = M A (E ⊎ B) (E ⊎ B)

  -- E: type of errors
  -- B: final answer type
  -- A: local result type

throw : ∀{E A B} (e : E) → Except E B A
throw e = shift λ _ →  return (inj₁ e)

handle : ∀{E B} → Except E B B → Pure (E ⊎ B)
handle m = reset (fmap inj₂ m)

module ExceptionExample where

  open import Data.Unit
  open import Data.Nat.Base using (ℕ; zero; suc)

  pred : ∀{B} → ℕ → Except ⊤ B ℕ
  pred 0 = throw _
  pred (suc m) = return m

  test : ℕ → Pure (⊤ ⊎ ℕ)
  test n = handle (pred n)
