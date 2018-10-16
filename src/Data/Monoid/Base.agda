module Data.Monoid.Base where

open import Data.PropositionalEquality

record Monoid {α} (A : Set α) : Set α where
  field
    _∘_ : A → A → A
    id : A
    left-id : ∀ a  → (id ∘ a) ≡ a
    right-id : ∀ a → (a ∘ id) ≡ a
    assoc : ∀ a b c → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
