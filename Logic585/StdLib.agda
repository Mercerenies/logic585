
module Logic585.StdLib where

open import Data.DifferenceList using (DiffList)
open import Data.List using (_∷_)

-- This is in a newer version of the Agda standard library, in
-- ridiculous generality. I've simply copy-pasted it from over there
-- :)
_∘₂_ : ∀ {a b c d}
         {A₁ : Set a} {A₂ : A₁ → Set d}
         {B : (x : A₁) → A₂ x → Set b}
         {C : {x : A₁} → {y : A₂ x} → B x y → Set c} →
       ({x : A₁} → {y : A₂ x} → (z : B x y) → C z) →
       (g : (x : A₁) → (y : A₂ x) → B x y) →
       ((x : A₁) → (y : A₂ x) → C (g x y))
f ∘₂ g = λ x y → f (g x y)

infixr 9 _∘₂_

module _ {a} {A : Set a} where

  infixl 6 _∷ʳ_

  _∷ʳ_ : DiffList A → A → DiffList A
  xs ∷ʳ x = λ k → xs (x ∷ k)
