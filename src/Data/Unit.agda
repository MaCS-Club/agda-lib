{-# OPTIONS --cubical #-}
module Data.Unit where

record ⊤ : Set where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}
