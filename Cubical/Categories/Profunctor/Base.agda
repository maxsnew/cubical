{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Base where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor

-- The simplest case is when the level of the sets in the profunctors
-- is the same as the level of the hom sets of categories. Roughly
-- this means the categories involved are "locally small".
module Profunctors (ℓ ℓ' : Level) where
  Cat : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  Cat = Cubical.Categories.Category.Category ℓ ℓ'
  PROF : (C D : Cat) → Category (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  PROF C D = FUNCTOR ((C ^op) × D) (SET ℓ')

  record Profunctor (C D : Cat) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    constructor fromFunc
    field
      asFunc : Category.ob (PROF C D)

    private
      R = asFunc

    module C = Category C
    module D = Category D
    _⋆C_ = C._⋆_
    _⋆D_ = D._⋆_

    Het[_,_] : C.ob → D.ob → Type ℓ'
    Het[ c , d ] = ⟨ asFunc ⟅ c , d ⟆ ⟩

    _⋆L⟨_⟩⋆R_ : ∀ {c c' d' d} → (f : C.Hom[ c , c' ])(r : Het[ c' , d' ])(g : D.Hom[ d' , d ]) → Het[ c , d ]
    f ⋆L⟨ r ⟩⋆R g = Functor.F-hom R (f , g) r

    ⋆L⟨⟩⋆RAssoc : ∀ {c c' c'' d'' d' d} → (f : C.Hom[ c , c' ])(f' : C.Hom[ c' , c'' ])(r : Het[ c'' , d'' ])(g' : D.Hom[ d'' , d' ])(g : D.Hom[ d' , d ])
                → (f ⋆C f') ⋆L⟨ r ⟩⋆R (g' ⋆D g) ≡ f ⋆L⟨ f' ⋆L⟨ r ⟩⋆R g' ⟩⋆R g
    ⋆L⟨⟩⋆RAssoc f f' r g' g i = Functor.F-seq R (f' , g') (f , g) i r

    ⋆L⟨⟩⋆RId : ∀ {c d} → (r : Het[ c , d ])
             → C.id ⋆L⟨ r ⟩⋆R D.id ≡ r
    ⋆L⟨⟩⋆RId r i = Functor.F-id R i r


    _⋆L_ : {c c' : C.ob} {d : D.ob}
              → C.Hom[ c , c' ]
              → Het[ c' , d ]
              → Het[ c  , d ]
    _⋆L_ f r = f ⋆L⟨ r ⟩⋆R D.id
    infixr 9 _⋆L_

    ⋆LId : ∀ {c d} → (r : Het[ c , d ]) → C.id ⋆L r ≡ r
    ⋆LId = ⋆L⟨⟩⋆RId

    ⋆LAssoc : ∀ {c c' c'' d} → (f : C.Hom[ c , c' ])(f' : C.Hom[ c' , c'' ])(r : Het[ c'' , d ])
            → (f ⋆C f' ⋆L r) ≡ (f ⋆L f' ⋆L r)
    ⋆LAssoc f f' r =
      ((f ⋆C f') ⋆L⟨ r ⟩⋆R D.id) ≡⟨ (λ i → (f ⋆C f') ⋆L⟨ r ⟩⋆R sym (D.⋆IdL D.id) i) ⟩
      ((f ⋆C f') ⋆L⟨ r ⟩⋆R (D.id ⋆D D.id)) ≡⟨ ⋆L⟨⟩⋆RAssoc f f' r D.id D.id ⟩
      f ⋆L f' ⋆L r ∎
            

    _⋆R_ : {c : C.ob} {d' d : D.ob}
         → Het[ c , d' ]
         → D [ d' , d ]
         → Het[ c , d ]
    _⋆R_ r g = C.id ⋆L⟨ r ⟩⋆R g
    infixl 9 _⋆R_

    ⋆RId : ∀ {c d} → (r : Het[ c , d ]) → r ⋆R D.id ≡ r
    ⋆RId = ⋆L⟨⟩⋆RId

    ⋆RAssoc : ∀ {c d'' d' d} → (r : Het[ c , d'' ])(g' : D.Hom[ d'' , d' ])(g : D.Hom[ d' , d ])
            → (r ⋆R g' ⋆D g) ≡ (r ⋆R g' ⋆R g)
    ⋆RAssoc r g' g =
      (C.id ⋆L⟨ r ⟩⋆R (g' ⋆D g)) ≡⟨ (λ i → sym (C.⋆IdL C.id) i ⋆L⟨ r ⟩⋆R (g' ⋆D g) ) ⟩
      ((C.id ⋆C C.id) ⋆L⟨ r ⟩⋆R (g' ⋆D g)) ≡⟨ ⋆L⟨⟩⋆RAssoc C.id C.id r g' g ⟩
      (r ⋆R g' ⋆R g) ∎

    ⋆L⋆R-unary-binaryL : ∀ {c c' d' d} → (f : C.Hom[ c , c' ])(r : Het[ c' , d' ])(g : D.Hom[ d' , d ])
                → ((f ⋆L r) ⋆R g) ≡ (f ⋆L⟨ r ⟩⋆R g)
    ⋆L⋆R-unary-binaryL f r g =
      ((f ⋆L r) ⋆R g) ≡⟨ sym (⋆L⟨⟩⋆RAssoc C.id f r D.id g) ⟩
      ((C.id ⋆C f) ⋆L⟨ r ⟩⋆R (D.id ⋆D g)) ≡⟨ (λ i → C.⋆IdL f i ⋆L⟨ r ⟩⋆R D.⋆IdL g i) ⟩
      (f ⋆L⟨ r ⟩⋆R g) ∎

    ⋆L⋆R-unary-binaryR : ∀ {c c' d' d} → (f : C.Hom[ c , c' ])(r : Het[ c' , d' ])(g : D.Hom[ d' , d ])
                → (f ⋆L (r ⋆R g)) ≡ (f ⋆L⟨ r ⟩⋆R g)
    ⋆L⋆R-unary-binaryR f r g =
      (f ⋆L (r ⋆R g))                     ≡⟨ sym (⋆L⟨⟩⋆RAssoc f C.id r g D.id) ⟩
      ((f ⋆C C.id) ⋆L⟨ r ⟩⋆R (g ⋆D D.id)) ≡⟨ (λ i → C.⋆IdR f i ⋆L⟨ r ⟩⋆R D.⋆IdR g i) ⟩
      (f ⋆L⟨ r ⟩⋆R g) ∎

    ⋆L⋆RAssoc : ∀ {c c' d' d} → (f : C.Hom[ c , c' ])(r : Het[ c' , d' ])(g : D.Hom[ d' , d ])
              → ((f ⋆L r) ⋆R g) ≡ (f ⋆L (r ⋆R g))
    ⋆L⋆RAssoc f r g =
      ((f ⋆L r) ⋆R g) ≡⟨ ⋆L⋆R-unary-binaryL f r g ⟩
      f ⋆L⟨ r ⟩⋆R g   ≡⟨ sym (⋆L⋆R-unary-binaryR f r g) ⟩
      (f ⋆L (r ⋆R g)) ∎

  record Homomorphism {C D : Cat} (P Q : Profunctor C D) : Type (ℓ-max ℓ ℓ') where
    module C = Category C
    module D = Category D
    module P = Profunctor P
    module Q = Profunctor Q

    _⋆LP⟨_⟩⋆R_ = P._⋆L⟨_⟩⋆R_
    _⋆LQ⟨_⟩⋆R_ = Q._⋆L⟨_⟩⋆R_
    
    field
      asNatTrans : PROF C D [ P.asFunc , Q.asFunc ]

    app : ∀ {c d} → P.Het[ c , d ] → Q.Het[ c , d ]
    app {c}{d} p = NatTrans.N-ob asNatTrans (c , d) p

    homomorphism : ∀ {c c' d' d} (f : C.Hom[ c , c' ])(p : P.Het[ c' , d' ])(g : D.Hom[ d' , d ])
               → app (f ⋆LP⟨ p ⟩⋆R g) ≡ (f ⋆LQ⟨ app p ⟩⋆R g)
    homomorphism f p g = λ i → NatTrans.N-hom asNatTrans (f , g) i p

  _⊸_ : {C D : Cat} → Profunctor C D → Profunctor C D → Type (ℓ-max ℓ ℓ')
  _⊸_ {C} {D} P Q = PROF C D [ Profunctor.asFunc P , Profunctor.asFunc Q ]

  swap : {C D : Cat} → Profunctor C D → Profunctor (D ^op) (C ^op)
  swap R = fromFunc
    record { F-ob  = λ (d , c) → R.F-ob (c , d)
           ; F-hom = λ (f , g) → R.F-hom (g , f)
           ; F-id  = R.F-id
           ; F-seq = λ (fl , fr) (gl , gr) → R.F-seq (fr , fl) (gr , gl)
           }
    where module R = Functor (Profunctor.asFunc R)

  HomProf : (C : Cat) → Profunctor C C
  HomProf C = fromFunc (HomFunctor C)

  _profF[_,_] : {B C D E : Cat}
             → (R : Profunctor D E)
             → (F : Functor B D)
             → (G : Functor C E)
             → Profunctor B C
  R profF[ F , G ] = fromFunc ((Profunctor.asFunc R) ∘F ((F ^opF) ×F G))

  _Represents_ : {C D : Cat} (F : Functor C D) (R : Profunctor C D) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  _Represents_ {C}{D} F R = NatIso (Profunctor.asFunc (HomProf D profF[ F , Id {C = D} ])) (Profunctor.asFunc R)

  Representable : {C D : Cat} → Profunctor C D → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Representable {C}{D} R = Σ[ F ∈ Functor C D ] (F Represents R)

  record Representable' {C D : Cat} (R : Profunctor C D) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    module C = Category C
    _⋆C_ = C._⋆_
    module D = Category D
    _⋆D_ = D._⋆_
    module R = Profunctor R
    open R using (_⋆R_ ; _⋆L_)
    field
      F₀             : C.ob → D.ob
      -- aka the introduction rule(s)/constructor(s)
      unit           : ∀ {c : C.ob} → R.Het[ c , F₀ c ]
      -- aka the elimination rule/pattern matching
      induction      : ∀ {c : C.ob} {d : D.ob} → R.Het[ c , d ] → D.Hom[ F₀ c , d ]
      -- aka the β-reduction principle
      computation    : ∀ {c : C.ob} {d : D.ob} → (r : R.Het[ c , d ])
                     → (unit ⋆R induction r) ≡ r
      -- aka the η-expansion principle
      extensionality : ∀ {c d} (f : D.Hom[ F₀ c , d ]) → f ≡ induction (unit ⋆R f)

    weak-extensionality : ∀ {c} → D.id ≡ induction (unit {c = c}) 
    weak-extensionality = D.id ≡⟨ extensionality D.id ⟩ induction (unit ⋆R D.id) ≡⟨ (λ i → induction (R.⋆RId unit i)) ⟩ induction unit ∎

    naturality : ∀ {c : C.ob}{d d' : D.ob}(r : R.Het[ c , d' ]) (k : D.Hom[ d' , d ])
               → (induction r ⋆D k) ≡ induction (r ⋆R k)
    naturality r k =
      induction r ⋆D k ≡⟨ extensionality (induction r ⋆D k) ⟩
      induction (unit ⋆R induction r ⋆D k) ≡⟨ (λ i → induction (R.⋆RAssoc unit (induction r) k i)) ⟩
      induction ((unit ⋆R induction r) ⋆R k) ≡⟨ (λ i → induction (computation r i ⋆R k)) ⟩
      induction (r ⋆R k) ∎


    F : Functor C D
    F = record
      { F-ob = F₀
      ; F-hom = λ f → induction ( f ⋆L unit)
      ; F-id =
             induction (C.id ⋆L unit) ≡⟨ (λ i → induction (R.⋆LId unit i)) ⟩
             induction unit ≡⟨ sym weak-extensionality ⟩
             D.id ∎
      ; F-seq = λ f g →
        induction ((f ⋆C g) ⋆L unit)  ≡⟨ (λ i → induction (R.⋆LAssoc f g unit i)) ⟩
        induction (f ⋆L (g ⋆L unit))  ≡⟨ (λ i → induction (f ⋆L sym (computation (g ⋆L unit)) i)) ⟩
        induction (f ⋆L (unit ⋆R (induction (g ⋆L unit))))  ≡⟨ (λ i → induction (sym (R.⋆L⋆RAssoc f unit (induction (g ⋆L unit))) i)) ⟩
        induction ((f ⋆L unit) ⋆R (induction (g ⋆L unit)))  ≡⟨ sym (naturality (f ⋆L unit) (induction (g ⋆L unit))) ⟩
        induction (f ⋆L unit) ⋆D induction (g ⋆L unit) ∎
      }

    module F = Functor F
    open R using (_⋆L⟨_⟩⋆R_; _⋆L_; _⋆R_)

    unduction : ∀ {c : C.ob} {d : D.ob} → D.Hom[ F₀ c , d ] → R.Het[ c , d ]
    unduction f = unit ⋆R f

    induction⁻¹ : (HomProf D profF[ F , Id ]) ⊸ R
    induction⁻¹ = natTrans (λ x r → unduction r) λ f⋆g i r → unduction-is-natural (fst f⋆g) (snd f⋆g) r i
      where 
            unduction-is-natural : ∀ {c c' d' d}
                                 → (f : C.Hom[ c , c' ])(g : D.Hom[ d' , d ])(IP : D.Hom[ F₀ c' , d' ])
                                 → unduction ((F ⟪ f ⟫ ⋆D IP) ⋆D g) ≡ f ⋆L⟨ unduction IP ⟩⋆R g
            unduction-is-natural f g IP =
              unit ⋆R ((induction (f ⋆L unit) ⋆D IP) ⋆D g) ≡⟨ (λ i → unit ⋆R D.⋆Assoc (induction (f ⋆L unit)) IP g i) ⟩
              unit ⋆R (induction (f ⋆L unit) ⋆D (IP ⋆D g)) ≡⟨ R.⋆RAssoc unit _ (IP ⋆D g) ⟩
              (unit ⋆R induction (f ⋆L unit)) ⋆R (IP ⋆D g) ≡⟨ (λ i → computation (f ⋆L unit) i ⋆R (IP ⋆D g)) ⟩
              (f ⋆L unit) ⋆R IP ⋆D g                         ≡⟨ R.⋆L⋆RAssoc f unit (IP ⋆D g) ⟩
              f ⋆L (unit ⋆R IP ⋆D g)                         ≡⟨ (λ i → f ⋆L R.⋆RAssoc unit IP g i) ⟩
              f ⋆L ((unit ⋆R IP) ⋆R g)                       ≡⟨ R.⋆L⋆R-unary-binaryR f _ g ⟩
              f ⋆L⟨ unit ⋆R IP ⟩⋆R g ∎

    F-represents-R : F Represents R
    F-represents-R = record { trans = induction⁻¹ ; nIso = λ x → isiso induction (λ i r → induction⁻¹-induction≡id r i) λ i IP → induction-induction⁻¹≡id IP i }
      where induction-induction⁻¹≡id : ∀ {c d}(IP : D.Hom[ F₀ c , d ]) → induction (unduction IP) ≡ IP
            induction-induction⁻¹≡id IP =
              induction (unit ⋆R IP) ≡⟨ sym (naturality unit IP) ⟩
              induction unit ⋆D IP ≡⟨ (λ i → sym weak-extensionality i ⋆D IP) ⟩
              D.id ⋆D IP               ≡⟨ D.⋆IdL _ ⟩
              IP ∎

            induction⁻¹-induction≡id : ∀ {c d}(r : R.Het[ c , d ]) → unduction (induction r) ≡ r
            induction⁻¹-induction≡id r = computation r 

  Repr⇒Repr' : ∀ {C D} (R : Profunctor C D) → Representable R → Representable' R
  Repr⇒Repr' {C}{D} R (F , F-repr-R)= record
                                 { F₀ = F.F-ob
                                 ; unit = unduction D.id
                                 ; induction = induction
                                 ; computation = computation
                                 ; extensionality = extensionality
                                 }
    where module C = Category C
          module D = Category D
          _⋆D_ = D._⋆_
          module R = Profunctor R
          open R using (_⋆R_; _⋆L⟨_⟩⋆R_)
          module F = Functor F
          module F-repr-R = NatIso F-repr-R
          induction : ∀ {c d} → R.Het[ c , d ] → D.Hom[ F.F-ob c , d ]
          induction r = isIso.inv (NatIso.nIso F-repr-R (_ , _)) r

          unduction-homo : Homomorphism (HomProf D profF[ F , Id ]) R
          unduction-homo = record { asNatTrans = F-repr-R.trans }

          module unduction-homo = Homomorphism unduction-homo

          unduction : ∀ {c d} → D.Hom[ F.F-ob c , d ] → R.Het[ c , d ]
          unduction = Homomorphism.app unduction-homo

          computation : ∀ {c d} (r : R.Het[ c , d ]) → unduction D.id ⋆R induction r ≡ r
          computation r =
            (C.id ⋆L⟨ unduction D.id ⟩⋆R induction r) ≡⟨ sym (unduction-homo.homomorphism C.id  D.id (induction r)) ⟩
            unduction ((F.F-hom C.id ⋆D D.id) ⋆D induction r) ≡⟨ (λ i → unduction (D.⋆IdR (F.F-hom C.id) i ⋆D induction r)) ⟩
            unduction (F.F-hom C.id ⋆D induction r) ≡⟨ (λ i → unduction (F.F-id i ⋆D induction r)) ⟩
            unduction (D.id ⋆D (induction r)) ≡⟨ (λ i → unduction (D.⋆IdL (induction r) i)) ⟩
            unduction (induction r) ≡⟨ (λ i → isIso.sec (NatIso.nIso F-repr-R _) i r) ⟩
            r ∎

          extensionality : ∀ {c d} (f : D.Hom[ F.F-ob c , d ]) → f ≡ induction (unduction D.id ⋆R f)
          extensionality f =
            f ≡⟨ sym (λ i → isIso.ret (NatIso.nIso F-repr-R _) i f) ⟩
            induction (unduction f) ≡⟨ (λ i → induction (unduction (sym (D.⋆IdL f) i))) ⟩
            induction (unduction (D.id ⋆D f)) ≡⟨ (λ i → induction (unduction (sym (D.⋆IdL D.id) i ⋆D f))) ⟩
            induction (unduction ((D.id ⋆D D.id) ⋆D f)) ≡⟨ (λ i → induction (unduction ((sym F.F-id i ⋆D D.id) ⋆D f))) ⟩
            induction (unduction ((F.F-hom C.id ⋆D D.id) ⋆D f)) ≡⟨ (λ i → induction (unduction-homo.homomorphism C.id D.id f i)) ⟩
            induction (C.id ⋆L⟨ unduction D.id ⟩⋆R f) ∎

          

  Repr'⇒Repr : ∀ {C D} (R : Profunctor C D) → Representable' R → Representable R
  Repr'⇒Repr R R-representable = (Representable'.F R-representable) , Representable'.F-represents-R R-representable