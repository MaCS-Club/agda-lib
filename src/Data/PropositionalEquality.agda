{-# OPTIONS --cubical #-}
module Data.PropositionalEquality where

open import Cubical.Core public
open import Data.Sigma

module _ {α}{A : Set α} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {β} {B : A → Set β} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → (λ i → B (p i)) [ f x ≡ f y ]
  cong f p = λ i → f (p i)

  cong' : ∀ {α β} {A : Set α} {B : Set β} {x y : A} (f : A → B) (p : x ≡ y) → f x ≡ f y
  cong' f p = λ i → f (p i)

  compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i =
    hcomp (λ j → \ { (i = i0) → x
                   ; (i = i1) → q j }) (p i)

infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : ∀ {α}{A : Set α}{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀{α}{A : Set α} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ {α}{A : Set α}(x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = compPath x≡y y≡z

_∎ : ∀ {α}{A : Set α}(x : A) → x ≡ x
_∎ _ = refl

_=,=_ : ∀{α β} {A : Set α} {B : Set β} {a1 a2 : A} {b1 b2 : B} -> a1 ≡ a2 -> b1 ≡ b2 -> (a1 , b1) ≡ (a2 , b2)
a1≡a2 =,= b1≡b2 = λ i → (a1≡a2 i , b1≡b2 i)
