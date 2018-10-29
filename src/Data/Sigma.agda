{-# OPTIONS --cubical #-}
module Data.Sigma where

open import Agda.Primitive

infixr 60 _,_

record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σ public

_×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
A × B = Σ A (λ _ → B)

∃ : ∀ {α β} {A : Set α} → (A → Set β) → Set (α ⊔ β)
∃ = Σ _

∃! : ∀ {α β γ} {A : Set α} → (A → A → Set γ) → (A → Set β) → Set (α ⊔ β ⊔ γ)
∃! _≈_ B = ∃ λ x → B x × (∀ {y} → B y → x ≈ y)
