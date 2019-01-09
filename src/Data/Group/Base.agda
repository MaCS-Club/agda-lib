{-# OPTIONS --cubical #-}
module Data.Group.Base where

open import Data.PropositionalEquality

record Group {α} (A : Set α) : Set α where
  field
    id : A
    inv : A → A
    _∘_ : A → A → A

    left-id : ∀ a → id ∘ a ≡ a
    left-inv : ∀ a → inv a ∘ a ≡ id
    assoc : ∀ a b c → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)

  abstract
    right-inv : ∀ a → a ∘ inv a ≡ id
    right-inv a = begin
        a ∘ inv a ≡⟨ sym (left-id (a ∘ inv a)) ⟩
        id ∘ (a ∘ inv a) ≡⟨ cong (_∘ (a ∘ inv a)) (sym (left-inv (inv a))) ⟩
        (inv (inv a) ∘ inv a) ∘ (a ∘ inv a) ≡⟨ assoc (inv (inv a)) (inv a) (a ∘ inv a) ⟩
        inv (inv a) ∘ (inv a ∘ (a ∘ inv a)) ≡⟨ cong (inv (inv a) ∘_) (sym (assoc (inv a) a (inv a))) ⟩
        inv (inv a) ∘ ((inv a ∘ a) ∘ inv a) ≡⟨ cong (λ x → inv (inv a) ∘ (x ∘ inv a)) (left-inv a) ⟩
        inv (inv a) ∘ (id ∘ inv a) ≡⟨ cong (inv (inv a) ∘_) (left-id (inv a)) ⟩
        inv (inv a) ∘ inv a ≡⟨ left-inv (inv a) ⟩
        id ∎

    right-id : ∀ a → a ∘ id ≡ a
    right-id a = begin
        a ∘ id ≡⟨ cong (a ∘_) (sym (left-inv a)) ⟩
        a ∘ (inv a ∘ a) ≡⟨ sym(assoc a (inv a) a) ⟩
        (a ∘ inv a) ∘ a ≡⟨ cong (_∘ a) (right-inv a) ⟩
        id ∘ a ≡⟨ left-id a ⟩
        a ∎
