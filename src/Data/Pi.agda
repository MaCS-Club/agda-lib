{-# OPTIONS --cubical #-}
module Data.Pi where

open import Agda.Primitive

Π : ∀ {α β} (A : Set α) (P : A → Set β) → Set (α ⊔ β)
Π A P = (x : A) → P x
