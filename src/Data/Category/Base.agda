{-# OPTIONS --cubical #-}
module Data.Category.Base where

open import Agda.Primitive
open import Data.PropositionalEquality
open import Data.Sigma renaming (_×_ to _×′_)


record Category {α β} : Set (lsuc (α ⊔ β)) where
  constructor category
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

_ᵒᵖ : ∀{α β} → Category {α} {β} → Category {α} {β}
C ᵒᵖ = record {
    obj = obj;
    hom = λ A B → hom B A;
    _∘_ = λ f g → g ∘ f;
    left-id = right-id;
    right-id = left-id;
    assoc = λ f g h → sym (assoc h g f)
  } where
      open Category C

_×_ : ∀{α β γ δ} → Category {α} {β} → Category {γ} {δ} → Category {α ⊔ γ} {β ⊔ δ}
C × K = category
    (obj C ×′ obj K)
    (λ { (C₁ , K₁) (C₂ , K₂) → hom C C₁ C₂ ×′ hom K K₁ K₂ })
    (λ { (c₁ , k₁) → (id C c₁) , (id K k₁) })
    (λ { (f₁ , g₁) (f₂ , g₂) -> ( (f₁ C∘ f₂) , (g₁ K∘ g₂) ) })
    (λ { (f , g) → (C-l-id f) =,= (K-l-id g) })
    (λ { (f , g) → (C-r-id f) =,= (K-r-id g) })
    (λ { (f₁ , g₁) (f₂ , g₂) (f₃ , g₃) → (C-assoc f₁ f₂ f₃) =,= (K-assoc g₁ g₂ g₃) })
  where
    open Category
    open Category C using () renaming (_∘_ to _C∘_ ; left-id to C-l-id ; right-id to C-r-id ; assoc to C-assoc)
    open Category K using () renaming (_∘_ to _K∘_ ; left-id to K-l-id ; right-id to K-r-id ; assoc to K-assoc)
