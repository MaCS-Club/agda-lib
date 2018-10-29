{-# OPTIONS --cubical #-}
module Data.Category.Base where

open import Cubical.Core
open import Agda.Primitive
open import Data.PropositionalEquality


record Category {α β} : Set (lsuc (α ⊔ β)) where
  field
    obj : Set α
    hom : obj → obj → Set β
    id : (x : obj) → hom x x
    _∘_ : {x y z : obj} → hom y z → hom x y → hom x z

    left-id : {x y : obj} → (f : hom x y) → id y ∘ f ≡ f
    right-id : {x y : obj} → (f : hom x y) → f ∘ id x ≡ f
    assoc : {x y z w : obj} → (f : hom z w) (g : hom y z) (h : hom x y) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Functor {α β γ δ}(A : Category {α} {β})(B : Category {γ} {δ}): Set (lsuc (α ⊔ β) ⊔ lsuc (γ ⊔ δ)) where
  field
    omap : Category.obj A → Category.obj B
    fmap : {x y : Category.obj A} → Category.hom A x y → Category.hom B (omap x) (omap y)

    preserves-id : (x : Category.obj A) → (fmap (Category.id A x)) ≡ Category.id B (omap x)
    preserves-comp : {x y z : Category.obj A} → (f : Category.hom A x y) → (g : Category.hom A y z) → (fmap (Category._∘_ A g f)) ≡ (Category._∘_ B (fmap g) (fmap f))
