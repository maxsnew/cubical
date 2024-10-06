{-# OPTIONS --safe #-}

module Cubical.Data.W.W where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty

private
  variable
    ℓ ℓ' ℓ'' : Level

data W (S : Type ℓ) (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  sup-W : (s : S) → (P s → W S P) → W S P

WInd : (S : Type ℓ) (P : S → Type ℓ') (M : W S P → Type ℓ'') →
       (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
       (w : W S P) → M w
WInd S P M e (sup-W s f) = e (λ p → WInd S P M e (f p))

module TermMonad (S : Type ℓ) (P : S → Type ℓ') where
  module _ (X : Type ℓ'') where
    Term : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Term = W (X ⊎ S) (Sum.rec (λ _ → ⊥*) P)

    η : X → Term
    η x = sup-W (inl x) Empty.elim*

    op : ∀ s → (∀ (p : P s) → Term) → Term
    op s args = sup-W (inr s) args
  
