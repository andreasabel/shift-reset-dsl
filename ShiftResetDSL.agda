module ShiftResetDSL where

open import Function
open import Relation.Binary.PropositionalEquality

-- reset : A → C
-- shift : ((A → B) → C) → A
-- 1 ∷ ⟨ 2 + shift k. k (k 3) ∷ [] ⟩

-- α = initial answer type
-- ω = final answer type

-- Think  M B α ω = (B → α) → ω

data M (B α ω : Set) : Set₁ where
  return' : α ≡ ω → B → M B α ω
  bind   : ∀{β A} → M A β ω → (A → M B α β) → M B α ω
  shift  : ∀{β} → ((k : B → α) → M β β ω) → M B α ω
  reset'  : ∀{β} → α ≡ ω → B ≡ ω → M β β ω → M B α ω

pattern return x = return' refl x
pattern reset x  = reset' refl refl x

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
  eval (reset m)  k = k (eval' m)

  eval' : ∀{α ω} → M α α ω → ω
  eval' m = eval m id

eval-fmap : ∀{α ω A B : Set} (e : A → B) (m : M A α ω) (k : B → α) →
  eval (fmap e m) k ≡ eval m (k ∘ e)
eval-fmap e m k = refl
