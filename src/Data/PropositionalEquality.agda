{-# OPTIONS --without-K #-}
module Data.PropositionalEquality where

infix 4 _≡_

data _≡_ {α}{A : Set α} : A → A → Set α where
  refl : { x : A } → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

cong : ∀ {α β}{A : Set α} {B : Set β}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

sym : ∀{α}{A : Set α} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{α}{A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : ∀ {α}{A : Set α}{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀{α}{A : Set α} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ {α}{A : Set α}(x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ {α}{A : Set α}(x : A) → x ≡ x
_∎ _ = refl
