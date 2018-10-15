{-# OPTIONS --without-K #-}
module Examples.Category.Lecture-2 where

open import Data.Category
open import Data.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Nat

⊥-category : Category
⊥-category = record {
    obj = ⊥;
    hom = λ _ _ → ⊥;
    _∘_ = λ ();
    id = λ ();
    left-id = λ ();
    right-id = λ ();
    assoc = λ ()
  }

⊤-category : Category
⊤-category = record {
    obj = ⊤;
    hom = λ _ _ → ⊤;
    id = λ tt → tt;
    left-id = λ _ → refl;
    right-id = λ _ → refl;
    assoc = λ _ _ _ → refl
  }

ℕ-category : Category
ℕ-category = record {
    obj = ⊤;
    hom = λ _ _ → ℕ;
    id = λ tt → 0;
    _∘_ = λ x y → x + y;
    left-id = +-leftUnit;
    right-id = +-rightUnit;
    assoc = +-assoc
  }

Sets-category : Category
Sets-category = record {
    obj = Set;
    hom = λ A B → (A → B);
    _∘_ = λ g f → (λ x → g(f x));
    id = λ A → (λ x → x);
    left-id = λ f → refl;
    right-id = λ f → refl;
    assoc = λ f g h → refl
  }

ℕ-to-⊤-functor : Functor (ℕ-category) (⊤-category)
ℕ-to-⊤-functor = record {
    omap = λ x → x;
    fmap = λ _ → tt;
    preserves-id = λ _ → refl;
    preserves-comp = λ _ _ → refl
  }
