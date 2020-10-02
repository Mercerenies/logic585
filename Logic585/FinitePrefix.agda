
module Logic585.FinitePrefix where

-- Some results about functions with domain ℕ when we only care about
-- a finite prefix of the output.

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)

AgreesPrefix : {A : Set} → ℕ → (ℕ → A) → (ℕ → A) → Set
AgreesPrefix n f g = ∀ (i : Fin n) → f (toℕ i) ≡ g (toℕ i)

agrees-shorter : {A : Set} {n m : ℕ} {f g : ℕ → A} → n ℕ.≤ m → AgreesPrefix m f g → AgreesPrefix n f g
agrees-shorter ℕ.z≤n agree ()
agrees-shorter (ℕ.s≤s leq) agree Fin.zero = agree Fin.zero
agrees-shorter {_} {ℕ.suc n} {ℕ.suc m} {f} {g} (ℕ.s≤s leq) agree (Fin.suc i) =
  agrees-shorter {f = f ∘ ℕ.suc} {g = g ∘ ℕ.suc} leq (agree ∘ Fin.suc) i

extrapolate-fin : {A : Set} {n : ℕ} → A → (Fin n → A) → ℕ → A
extrapolate-fin {n = ℕ.zero} a _ _ = a
extrapolate-fin {n = ℕ.suc n} _ f ℕ.zero = f Fin.zero
extrapolate-fin {n = ℕ.suc n} a f (ℕ.suc k) = extrapolate-fin a (f ∘ Fin.suc) k

extrapolate-agrees : {A : Set} {n : ℕ} (a : A) (f : ℕ → A) →
                     AgreesPrefix n f (extrapolate-fin {A} {n} a (f ∘ toℕ))
extrapolate-agrees _ _ Fin.zero = refl
extrapolate-agrees a f (Fin.suc i) = extrapolate-agrees a (f ∘ ℕ.suc) i
