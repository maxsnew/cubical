module Cubical.HITs.QW.Base where
open import Cubical.Foundations.Prelude
open import Cubical.Data.W.W

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _ (S : Type ℓ)      -- Shapes
         (P : S → Type ℓ') -- Positions
         -- (Es : Type ℓ'')       -- equations
         -- (Ep : Es → Type ℓ''') -- equation positions/variables
         -- (l : ∀ (eq : Es) → )
       where
  private
    module Term = TermMonad S P
  module _ (Es : Type ℓ'') (Ep : Es → Type ℓ''')
           (l r : ∀ (eq : Es) → Term.Term (Ep eq))
           where
