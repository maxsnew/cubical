{-

  Definition of profunctors (https://ncatlab.org/nlab/show/profunctor)
  and some basic facts about them. Also known as distributors, bimodules,
  relators, correspondences,...

  A profunctor from C to D is a functor from C to Presheaves on D. Profunctors
  generalize functors in a similar way that relations generalize functions. We
  can view a profunctor as taking each c to a "specification" for on object of
  D. The functoriality says that these specifications vary functorially.

-}

module Cubical.Categories.Profunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category

Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (PresheafCategory D ℓS)

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓS where
  PROFUNCTOR : Category _ _
  PROFUNCTOR = FUNCTOR C (PresheafCategory D ℓS)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Profunctor C D ℓS) where
  -- A profunctor is representable when there is a universal element for every
  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)

  module _ (ues : UniversalElements) where
    open Functor
    open NatTrans
    private
      module ues (c : C .ob) = UniversalElement (ues c)
    open ues
    -- Given universal elements of a profunctor, we can construct a
    -- functor. This allows us to define functors satisfying universal
    -- properties without explicitly constructing the action on
    -- morphisms or proving functoriality. This can save a lot of
    -- tedious work.
    FunctorComprehension : Functor C D
    FunctorComprehension .F-ob x = vertex x
    FunctorComprehension .F-hom {x}{y} f =
      intro y (R .F-hom f .N-ob _ (element x))
    FunctorComprehension .F-id {x} =
      intro⟨ x ⟩ (funExt⁻ (funExt⁻ (cong N-ob (R .F-id)) _) _)
      ∙ sym (weak-η x)
    FunctorComprehension .F-seq {x} {y} {z} f g =
      intro⟨_⟩ _
        ( funExt⁻ (funExt⁻ (cong N-ob (R .F-seq f g)) _) _
        ∙ cong (R .F-hom g .N-ob _) (sym $ β _)
        ∙ funExt⁻ (R .F-hom g .N-hom _) _)
      ∙ (sym $ intro-natural z)

  -- TODO: if D is univalent, then we can perform FunctorComprehension
  -- provided only the mere existence of UniversalElements.
