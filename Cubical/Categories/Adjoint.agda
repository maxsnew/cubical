
module Cubical.Categories.Adjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open Functor

open Iso
open Category

{-
==============================================
                  Overview
==============================================

This module contains two definitions for adjoint
functors, and functions witnessing their
logical (and maybe eventually actual?)
equivalence.
-}

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

{-
==============================================
             Adjoint definitions
==============================================

We provide two alternative definitions for
adjoint functors: the unit-counit
definition, followed by the natural bijection
definition.
-}

module UnitCounit {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (G : Functor D C) where
  record TriangleIdentities
    (η : 𝟙⟨ C ⟩ ⇒ (funcComp G F))
    (ε : (funcComp F G) ⇒ 𝟙⟨ D ⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
    where
    field
      Δ₁ : ∀ c → F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧ ≡ D .id
      Δ₂ : ∀ d → η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫ ≡ C .id

  -- Adjoint def 1: unit-counit
  record _⊣_ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      -- unit
      η : 𝟙⟨ C ⟩ ⇒ (funcComp G F)
      -- counit
      ε : (funcComp F G) ⇒ 𝟙⟨ D ⟩
      triangleIdentities : TriangleIdentities η ε
    open TriangleIdentities triangleIdentities public


private
  variable
    C : Category ℓC ℓC'
    D : Category ℓC ℓC'
    E : Category ℓE ℓE'

module _ {F : Functor C D} {G : Functor D C} where
  open UnitCounit
  open _⊣_
  open NatTrans
  open TriangleIdentities
  oppositeAdjunction : (F ⊣ G) → ((G ^opF) ⊣ (F ^opF))
  N-ob (η (oppositeAdjunction x)) = N-ob (ε x)
  N-hom (η (oppositeAdjunction x)) f = sym (N-hom (ε x) f)
  N-ob (ε (oppositeAdjunction x)) = N-ob (η x)
  N-hom (ε (oppositeAdjunction x)) f = sym (N-hom (η x) f)
  Δ₁ (triangleIdentities (oppositeAdjunction x)) =
    Δ₂ (triangleIdentities x)
  Δ₂ (triangleIdentities (oppositeAdjunction x)) =
   Δ₁ (triangleIdentities x)

  -- -- Does anyone actually need this?
  -- Iso⊣^opF : Iso (F ⊣ G) ((G ^opF) ⊣ (F ^opF))
  -- fun Iso⊣^opF = oppositeAdjunction
  -- inv Iso⊣^opF = _
  -- sec Iso⊣^opF _ = {!!} -- refl
  -- ret Iso⊣^opF _ = {!!} -- refl

private
  variable
    F F' : Functor C D
    G G' : Functor D C


module AdjointUniqeUpToNatIso where
 open UnitCounit
 module Left
          (F⊣G  : _⊣_ {D = D} F G)
          (F'⊣G : F' ⊣ G) where
  open NatTrans

  private
    variable
      H H' : Functor C D

  _D⋆_ = seq' D

  m : (H⊣G : H ⊣ G) (H'⊣G : H' ⊣ G) →
        ∀ {x} → D [ H ⟅ x ⟆ , H' ⟅ x ⟆ ]
  m {H = H} H⊣G H'⊣G =
    H ⟪ (H'⊣G .η) ⟦ _ ⟧ ⟫ ⋆⟨ D ⟩ (H⊣G .ε) ⟦ _ ⟧ where open _⊣_

  private
   s : (H⊣G : H ⊣ G) (H'⊣G : H' ⊣ G) → ∀ {x} →
           seq' D (m H'⊣G H⊣G {x}) (m H⊣G H'⊣G {x})
              ≡ D .id
   s {H = H} {H' = H'} H⊣G H'⊣G = by-N-homs ∙ by-Δs
     where
      open _⊣_ H⊣G  using (η ; Δ₂)
      open _⊣_ H'⊣G using (ε ; Δ₁)
      by-N-homs =
        AssocCong₂⋆R D
        (AssocCong₂⋆L D (sym (N-hom ε _)))
          ∙ cong₂ _D⋆_
               (sym (F-seq H' _ _)
                ∙∙ cong (H' ⟪_⟫) ((sym (N-hom η  _)))
                ∙∙ F-seq H' _ _)
               (sym (N-hom ε _))

      by-Δs =
        ⋆Assoc D _ _ _
        ∙∙ cong (H' ⟪ _ ⟫ D⋆_)
             (sym (⋆Assoc D _ _ _)
             ∙ cong (_D⋆ ε ⟦ _ ⟧)
                 (  sym (F-seq H' _ _)
                 ∙∙ cong (H' ⟪_⟫) (Δ₂ (H' ⟅ _ ⟆))
                 ∙∙ F-id H')
             ∙ ⋆IdL D _)
        ∙∙ Δ₁ _

  open NatIso
  open isIso

  F≅ᶜF' : F ≅ᶜ F'
  N-ob (trans F≅ᶜF') _ = _
  N-hom (trans F≅ᶜF') _ =
       sym (⋆Assoc D _ _ _)
    ∙∙ cong (_D⋆ (F⊣G .ε) ⟦ _ ⟧)
         (sym (F-seq F _ _)
         ∙∙ cong (F ⟪_⟫) (N-hom (F'⊣G .η) _)
         ∙∙ (F-seq F _ _))
    ∙∙ AssocCong₂⋆R D (N-hom (F⊣G .ε) _)
   where open _⊣_
  inv (nIso F≅ᶜF' _) = _
  sec (nIso F≅ᶜF' _) = s F⊣G F'⊣G
  ret (nIso F≅ᶜF' _) = s F'⊣G F⊣G

  F≡F' : isUnivalent D → F ≡ F'
  F≡F' univD =
   isUnivalent.CatIsoToPath
    (isUnivalentFUNCTOR _ _ univD)
     (NatIso→FUNCTORIso _ _ F≅ᶜF')

 module Right (F⊣G  : F UnitCounit.⊣ G)
              (F⊣G' : F UnitCounit.⊣ G') where

  G≅ᶜG' : G ≅ᶜ G'
  G≅ᶜG' = Iso.inv congNatIso^opFiso
    (Left.F≅ᶜF' (oppositeAdjunction F⊣G')
                (oppositeAdjunction F⊣G))

  open NatIso

  G≡G' : isUnivalent _ → G ≡ G'
  G≡G' univC =
   isUnivalent.CatIsoToPath
    (isUnivalentFUNCTOR _ _ univC)
     (NatIso→FUNCTORIso _ _ G≅ᶜG')

module NaturalBijection where
  -- Adjoint def 2: natural bijection
  record _⊣_ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (G : Functor D C) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      adjIso : ∀ {c d} → Iso (D [ F ⟅ c ⟆ , d ]) (C [ c , G ⟅ d ⟆ ])

    infix 40 _♭
    infix 40 _♯
    _♭ : ∀ {c d} → (D [ F ⟅ c ⟆ , d ]) → (C [ c , G ⟅ d ⟆ ])
    (_♭) {_} {_} = adjIso .fun

    _♯ : ∀ {c d} → (C [ c , G ⟅ d ⟆ ]) → (D [ F ⟅ c ⟆ , d ])
    (_♯) {_} {_} = adjIso .inv

    field
      adjNatInD : ∀ {c : C .ob} {d d'} (f : D [ F ⟅ c ⟆ , d ]) (k : D [ d , d' ])
                → (f ⋆⟨ D ⟩ k) ♭ ≡ f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫

      adjNatInC : ∀ {c' c d} (g : C [ c , G ⟅ d ⟆ ]) (h : C [ c' , c ])
                → (h ⋆⟨ C ⟩ g) ♯ ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯

    adjNatInD' : ∀ {c : C .ob} {d d'} (g : C [ c , G ⟅ d ⟆ ]) (k : D [ d , d' ])
                → g ♯ ⋆⟨ D ⟩ k ≡ (g ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
    adjNatInD' {c} {d} {d'} g k =
      g ♯ ⋆⟨ D ⟩ k
        ≡⟨ sym (adjIso .ret (g ♯ ⋆⟨ D ⟩ k)) ⟩
      ((g ♯ ⋆⟨ D ⟩ k) ♭) ♯
        ≡⟨ cong _♯ (adjNatInD (g ♯) k) ⟩
      ((g ♯) ♭ ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
        ≡⟨ cong _♯ (cong (λ g' → seq' C g' (G ⟪ k ⟫)) (adjIso .sec g)) ⟩
      (g ⋆⟨ C ⟩ G ⟪ k ⟫) ♯ ∎

    adjNatInC' : ∀ {c' c d} (f : D [ F ⟅ c ⟆ , d ]) (h : C [ c' , c ])
                → h ⋆⟨ C ⟩ (f ♭) ≡ (F ⟪ h ⟫ ⋆⟨ D ⟩ f) ♭
    adjNatInC' {c'} {c} {d} f h =
      h ⋆⟨ C ⟩ (f ♭)
        ≡⟨ sym (adjIso .sec (h ⋆⟨ C ⟩ (f ♭))) ⟩
      ((h ⋆⟨ C ⟩ (f ♭)) ♯) ♭
        ≡⟨ cong _♭ (adjNatInC (f ♭) h) ⟩
      ((F ⟪ h ⟫ ⋆⟨ D ⟩ (f ♭) ♯) ♭)
        ≡⟨ cong _♭ (cong (λ f' → seq' D (F ⟪ h ⟫) f') (adjIso .ret f)) ⟩
      (F ⟪ h ⟫ ⋆⟨ D ⟩ f) ♭ ∎

  isLeftAdjoint : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isLeftAdjoint {C = C}{D} F = Σ[ G ∈ Functor D C ] F ⊣ G

  isRightAdjoint : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (G : Functor D C) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isRightAdjoint {C = C}{D} G = Σ[ F ∈ Functor C D ] F ⊣ G

module Compose {F : Functor C D} {G : Functor D C}
               {L : Functor D E} {R : Functor E D}
               where
 open NaturalBijection
 module _ (F⊣G : F ⊣ G) (L⊣R : L ⊣ R) where
  open _⊣_

  LF⊣GR : (L ∘F F) ⊣ (G ∘F R)
  adjIso LF⊣GR = compIso (adjIso L⊣R) (adjIso F⊣G)
  adjNatInD LF⊣GR f k =
   cong (adjIso F⊣G .fun) (adjNatInD L⊣R _ _) ∙ adjNatInD F⊣G _ _
  adjNatInC LF⊣GR f k =
   cong (adjIso L⊣R .inv) (adjNatInC F⊣G _ _) ∙ adjNatInC L⊣R _ _

{-
==============================================
            Proofs of equivalence
==============================================

This first unnamed module provides a function
adj'→adj which takes you from the second
definition to the first.

The second unnamed module does the reverse.
-}

module _ (F : Functor C D) (G : Functor D C) where
  open UnitCounit
  open NaturalBijection renaming (_⊣_ to _⊣²_)
  module _ (adj : F ⊣² G) where
    open _⊣²_ adj
    open _⊣_

    -- Naturality condition implies that a commutative square in C
    -- appears iff the transpose in D is commutative as well
    -- Used in adj'→adj
    adjNat' : ∀ {c c' d d'} {f : D [ F ⟅ c ⟆ , d ]} {k : D [ d , d' ]}
            → {h : C [ c , c' ]} {g : C [ c' , G ⟅ d' ⟆ ]}
            -- commutativity of squares is iff
            → ((f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g))
            × ((f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯))
    adjNat' {c} {c'} {d} {d'} {f} {k} {h} {g} = D→C , C→D
      where
        D→C : (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) → (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g)
        D→C eq = f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫
              ≡⟨ sym (adjNatInD _ _) ⟩
                ((f ⋆⟨ D ⟩ k) ♭)
              ≡⟨ cong _♭ eq ⟩
                (F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯) ♭
              ≡⟨ sym (cong _♭ (adjNatInC _ _)) ⟩
                (h ⋆⟨ C ⟩ g) ♯ ♭
              ≡⟨ adjIso .sec _ ⟩
                h ⋆⟨ C ⟩ g
              ∎
        C→D : (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫ ≡ h ⋆⟨ C ⟩ g) → (f ⋆⟨ D ⟩ k ≡ F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯)
        C→D eq = f ⋆⟨ D ⟩ k
              ≡⟨ sym (adjIso .ret _) ⟩
                (f ⋆⟨ D ⟩ k) ♭ ♯
              ≡⟨ cong _♯ (adjNatInD _ _) ⟩
                (f ♭ ⋆⟨ C ⟩ G ⟪ k ⟫) ♯
              ≡⟨ cong _♯ eq ⟩
                (h ⋆⟨ C ⟩ g) ♯
              ≡⟨ adjNatInC _ _ ⟩
                F ⟪ h ⟫ ⋆⟨ D ⟩ g ♯
              ∎

    open NatTrans

    -- note : had to make this record syntax because termination checker was complaining
    -- due to referencing η and ε from the definitions of Δs
    adj'→adj : F ⊣ G
    adj'→adj = record
      { η = η'
      ; ε = ε'
      ; triangleIdentities = record
        {Δ₁ = Δ₁'
        ; Δ₂ = Δ₂' }}

      where
        -- ETA

        -- trivial commutative diagram between identities in D
        commInD : ∀ {x y} (f : C [ x , y ]) → D .id ⋆⟨ D ⟩ F ⟪ f ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
        commInD f = (D .⋆IdL _) ∙ sym (D .⋆IdR _)

        sharpen1 : ∀ {x y} (f : C [ x , y ]) → F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ♭ ♯
        sharpen1 f = cong (λ v → F ⟪ f ⟫ ⋆⟨ D ⟩ v) (sym (adjIso .ret _))

        η' : 𝟙⟨ C ⟩ ⇒ G ∘F F
        η' .N-ob x = D .id ♭
        η' .N-hom f = sym (fst (adjNat') (commInD f ∙ sharpen1 f))

        -- EPSILON

        -- trivial commutative diagram between identities in C
        commInC : ∀ {x y} (g : D [ x , y ]) → C .id ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ G ⟪ g ⟫ ⋆⟨ C ⟩ C .id
        commInC g = (C .⋆IdL _) ∙ sym (C .⋆IdR _)

        sharpen2 : ∀ {x y} (g : D [ x , y ]) → C .id ♯ ♭ ⋆⟨ C ⟩ G ⟪ g ⟫ ≡ C .id ⋆⟨ C ⟩ G ⟪ g ⟫
        sharpen2 g = cong (λ v → v ⋆⟨ C ⟩ G ⟪ g ⟫) (adjIso .sec _)

        ε' : F ∘F G ⇒ 𝟙⟨ D ⟩
        ε' .N-ob x  = C .id ♯
        ε' .N-hom g = sym (snd adjNat' (sharpen2 g ∙ commInC g))

        -- DELTA 1

        Δ₁' : ∀ c → F ⟪ η' ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε' ⟦ F ⟅ c ⟆ ⟧ ≡ D .id
        Δ₁' c =
            F ⟪ η' ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε' ⟦ F ⟅ c ⟆ ⟧
          ≡⟨ sym (snd adjNat' (cong (λ v → (η' ⟦ c ⟧) ⋆⟨ C ⟩ v) (G .F-id))) ⟩
            D .id ⋆⟨ D ⟩ D .id
          ≡⟨ D .⋆IdL _ ⟩
            D .id
          ∎

        -- DELTA 2

        Δ₂' : ∀ d → η' ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε' ⟦ d ⟧ ⟫ ≡ C .id
        Δ₂' d =
            (η' ⟦ G ⟅ d ⟆ ⟧) ⋆⟨ C ⟩ (G ⟪ ε' ⟦ d ⟧ ⟫)
          ≡⟨ fst adjNat' (cong (λ v → v ⋆⟨ D ⟩ (ε' ⟦ d ⟧)) (sym (F .F-id))) ⟩
            C .id ⋆⟨ C ⟩ C .id
          ≡⟨ C .⋆IdL _ ⟩
            C .id
          ∎


  module _ (adj : F ⊣ G) where
    open _⊣_ adj
    open _⊣²_
    open NatTrans

    adj→adj' : F ⊣² G
    -- ∀ {c d} → Iso (D [ F ⟅ c ⟆ , d ]) (C [ c , G ⟅ d ⟆ ])
    -- takes f to Gf precomposed with the unit
    adj→adj' .adjIso {c = c} .fun f = η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫
    -- takes g to Fg postcomposed with the counit
    adj→adj' .adjIso {d = d} .inv g = F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
    -- invertibility follows from the triangle identities
    adj→adj' .adjIso {c = c} {d} .sec g
      = η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧ ⟫
      ≡⟨ cong (λ v → η ⟦ c ⟧ ⋆⟨ C ⟩ v) (G .F-seq _ _) ⟩
        η ⟦ c ⟧ ⋆⟨ C ⟩ (G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫)
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
        η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫
      -- apply naturality
      ≡⟨ rCatWhisker {C = C} _ _ _ natu ⟩
        (g ⋆⟨ C ⟩ η ⟦ G ⟅ d ⟆ ⟧) ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫
      ≡⟨ C .⋆Assoc _ _ _ ⟩
        g ⋆⟨ C ⟩ (η ⟦ G ⟅ d ⟆ ⟧ ⋆⟨ C ⟩ G ⟪ ε ⟦ d ⟧ ⟫)
      ≡⟨ lCatWhisker {C = C} _ _ _ (Δ₂ d) ⟩
        g ⋆⟨ C ⟩ C .id
      ≡⟨ C .⋆IdR _ ⟩
        g
      ∎
      where
        natu : η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ F ⟪ g ⟫ ⟫ ≡ g ⋆⟨ C ⟩ η ⟦ G ⟅ d ⟆ ⟧
        natu = sym (η .N-hom _)
    adj→adj' .adjIso {c = c} {d} .ret f
      = F ⟪ η ⟦ c ⟧ ⋆⟨ C ⟩ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
      ≡⟨ cong (λ v → v ⋆⟨ D ⟩ ε ⟦ d ⟧) (F .F-seq _ _) ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧
      ≡⟨ D .⋆Assoc _ _ _ ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ (F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧)
      -- apply naturality
      ≡⟨ lCatWhisker {C = D} _ _ _ natu ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ (ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f)
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
        F ⟪ η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f
      -- apply triangle identity
      ≡⟨ rCatWhisker {C = D} _ _ _ (Δ₁ c) ⟩
        D .id ⋆⟨ D ⟩ f
      ≡⟨ D .⋆IdL _ ⟩
        f
      ∎
      where
        natu : F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ ε ⟦ d ⟧ ≡ ε ⟦ F ⟅ c ⟆ ⟧ ⋆⟨ D ⟩ f
        natu = ε .N-hom _
    -- follows directly from functoriality
    adj→adj' .adjNatInD {c = c} f k = cong (λ v → η ⟦ c ⟧ ⋆⟨ C ⟩ v) (G .F-seq _ _) ∙ (sym (C .⋆Assoc _ _ _))
    adj→adj' .adjNatInC {d = d} g h = cong (λ v → v ⋆⟨ D ⟩ ε ⟦ d ⟧) (F .F-seq _ _) ∙ D .⋆Assoc _ _ _
