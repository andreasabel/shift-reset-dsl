module ShiftResetDSL where

open import Function
open import Relation.Binary.PropositionalEquality

-- reset : A → C
-- shift : ((A → B) → C) → A
-- 1 ∷ ⟨ 2 + shift k. k (k 3) ∷ [] ⟩

-- α = initial answer type
-- ω = final answer type

data M (α ω B : Set) : Set₁ where
  return : α ≡ ω → B → M α ω B
  bind   : ∀{β A} → M β ω A → (A → M α β B) → M α ω B
  shift  : ∀{β} → ((k : B → α) → M β ω β) → M α ω B
  reset  : ∀{β} → M β ω β → M α ω B
  fmap   : ∀{A} → (A → B) → M α ω A → M α ω B

-- Application of an impure dependent function to a pure argument
-- is just Agda's application.

app : ∀{α ω A B : Set} {C : A → Set} → ((x : A) → M α ω (C x)) → (a : A) → M α ω (C a)
app f a = f a

-- Evaluation representing evaluation contexts as functions

mutual
  eval : ∀{α ω C} → M α ω C → (C → α) → ω
  eval (return refl x) k = k x
  eval (bind m f)      k = eval m (λ a → eval (f a) k)
  eval (shift f)       k = eval' (f k)
  eval (reset m)       k = eval' m
  eval (fmap e m)      k = eval m (k ∘ e)

  eval' : ∀{α ω} → M α ω α → ω
  eval' m = eval m id
