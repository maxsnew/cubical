module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' ℓS : Level

Presheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
Presheaf C ℓS = Functor (C ^op) (SET ℓS)

PresheafCategory : Category ℓ ℓ' → (ℓS : Level)
       → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
                  (ℓ-max (ℓ-max ℓ ℓ') ℓS)
PresheafCategory C ℓS = FUNCTOR (C ^op) (SET ℓS)

isUnivalentPresheafCategory : {C : Category ℓ ℓ'}
                            → isUnivalent (PresheafCategory C ℓS)
isUnivalentPresheafCategory = isUnivalentFUNCTOR _ _ isUnivalentSET

open Functor
-- Category-like syntax for presheaves.
module PresheafNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} (P : Presheaf C ℓp)
       where
  private
    module C = Category C
  p[_] : C.ob → Type ℓp
  p[ x ] = ⟨ P ⟅ x ⟆ ⟩

  _⋆_ : ∀ {x y} (f : C [ x , y ]) (g : p[ y ]) → p[ x ]
  f ⋆ g = P .F-hom f g

  ⋆IdL : ∀ {x} (g : p[ x ]) → C.id ⋆ g ≡ g
  ⋆IdL = funExt⁻ (P .F-id)

  ⋆Assoc : ∀ {x y z} (f : C [ x , y ])(g : C [ y , z ])(h : p[ z ]) →
    (f C.⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc f g = funExt⁻ (P .F-seq g f)

  ⟨_⟩⋆⟨_⟩ : ∀ {x y} {f f' : C [ x , y ]} {g g' : p[ y ]}
            → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ f≡f' ⟩⋆⟨ g≡g' ⟩ = cong₂ _⋆_ f≡f' g≡g'

  isSetPsh : ∀ {x} → isSet (p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd


open Category

action : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS)
       → {a b : C .ob} → C [ a , b ] → fst (P ⟅ b ⟆) → fst (P ⟅ a ⟆)
action C P = P .F-hom

-- Convenient notation for naturality
syntax action C P f ϕ = ϕ ∘ᴾ⟨ C , P ⟩ f

∘ᴾId : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a : C .ob}
     → (ϕ : fst (P ⟅ a ⟆))
     → ϕ ∘ᴾ⟨ C , P ⟩ C .id ≡ ϕ
∘ᴾId C P ϕ i = P .F-id i ϕ

∘ᴾAssoc : ∀ (C : Category ℓ ℓ') → (P : Presheaf C ℓS) → {a b c : C .ob}
        → (ϕ : fst (P ⟅ c ⟆))
        → (f : C [ b , c ])
        → (g : C [ a , b ])
        → ϕ ∘ᴾ⟨ C , P ⟩ (f ∘⟨ C ⟩ g) ≡ (ϕ ∘ᴾ⟨ C , P ⟩ f) ∘ᴾ⟨ C , P ⟩ g
∘ᴾAssoc C P ϕ f g i = P .F-seq f g i ϕ
