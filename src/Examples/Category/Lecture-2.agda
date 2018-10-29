{-# OPTIONS --cubical #-}
module Examples.Category.Lecture-2 where

open import Cubical.Core
open import Agda.Primitive
open import Data.Category
open import Data.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Monoid

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

id-functor : ∀ {α}(A : Category {α}{α})  → Functor A A
id-functor A = record {
    omap = λ x → x;
    fmap = λ x → x;
    preserves-id = λ _ → refl;
    preserves-comp = λ _ _ → refl
  }

ℕ-to-⊤-functor : Functor (ℕ-category) (⊤-category)
ℕ-to-⊤-functor = record {
    omap = λ x → x;
    fmap = λ _ → tt;
    preserves-id = λ _ → refl;
    preserves-comp = λ _ _ → refl
  }

ℕ-2×-functor : Functor (ℕ-category) (ℕ-category)
ℕ-2×-functor = record {
    omap = λ x → x;
    fmap = λ x → 2 * x;
    preserves-id = λ _ → refl;
    preserves-comp = λ g f → *-distl 2 f g
  }

hom-A-A-is-monoid : ∀ {α}{β} → ∀ (C : Category {α}{β}) → (A : Category.obj C) → Monoid {β} (Category.hom C A A)
hom-A-A-is-monoid C A = record {
    id = Category.id C A;
    _∘_ = Category._∘_ C;
    left-id = Category.left-id C;
    right-id = Category.right-id C;
    assoc = Category.assoc C
  }


-- Скорее всего я тупой, но эта штука вешает агду насмерть
--
-- Category-of-categories : Category
-- Category-of-categories = record {
--     obj = Category;
--     hom = λ A B → Functor A B;
--     id = λ A → id-functor A;
--     _∘_ = λ g f → record {
--       omap = λ x → Functor.omap g (Functor.omap f x);
--       fmap = λ x → Functor.fmap g (Functor.fmap f x);
--       preserves-id = λ A → begin
--             Functor.fmap g (Functor.fmap f (Category.id _ A)) ≡⟨ cong (Functor.fmap g) (Functor.preserves-id f A) ⟩
--             Functor.fmap g (Category.id _ (Functor.omap f A)) ≡⟨ Functor.preserves-id g (Functor.omap f A) ⟩
--             Category.id _ (Functor.omap g (Functor.omap f A)) ∎;
--       preserves-comp = ?
--     }
--   }
