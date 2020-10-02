
module Logic585.PropCalc.Tautology.Finite where

open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Tautology
open import Logic585.FinitePrefix

open import Function using (_∘_)
open import Data.Nat as ℕ using (ℕ)
open import Data.List
open import Data.Fin as Fin using (Fin)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
import Data.Nat.Properties as ℕProps

FinRelTautologyOn : ℕ → List Stmt → Stmt → Set
FinRelTautologyOn n Γ x = (∀ (f : Fin n → Bool) → all (assign (extrapolate-fin false f)) Γ ≡ true → (assign (extrapolate-fin false f) x ≡ true))

-- Like a relative tautology, but only proven on the necessary finite
-- subset. I will show that this is equivalent to RelTautology.
FinRelTautology : List Stmt → Stmt → Set
FinRelTautology Γ x = FinRelTautologyOn (foldr ℕ._⊔_ (vars-of x) (map vars-of Γ)) Γ x

rel-is-fin-rel : {Γ : List Stmt} {x : Stmt} → RelTautology Γ x → FinRelTautology Γ x
rel-is-fin-rel rel = λ f x₁ → rel (extrapolate-fin false f) x₁

fin-rel-is-rel : {Γ : List Stmt} {x : Stmt} → FinRelTautology Γ x → RelTautology Γ x
fin-rel-is-rel {Γ} {x} finrel f eq = trans (assignment-uses-prefix {f = f} {g = ḡ} {x} agreement′)
                                           (finrel g satisfies-Γ)
  where max-var : ℕ
        max-var = foldr ℕ._⊔_ (vars-of x) (map vars-of Γ)
        ≤lemma : {Δ : List Stmt} → vars-of x ℕ.≤ foldr ℕ._⊔_ (vars-of x) (map vars-of Δ)
        ≤lemma {[]} = ℕProps.≤-reflexive refl
        ≤lemma {x ∷ Δ} = ℕProps.≤-trans (≤lemma {Δ}) (ℕProps.n≤m⊔n _ _)
        g : Fin max-var → Bool
        g = f ∘ Fin.toℕ
        ḡ : ℕ → Bool
        ḡ = extrapolate-fin false g
        agreement : AgreesPrefix max-var f ḡ
        agreement = extrapolate-agrees false f
        agreement′ : AgreesPrefix (vars-of x) f ḡ
        agreement′ = agrees-shorter {f = f} {g = ḡ} (≤lemma {Γ}) agreement
        satisfies-Γ : all (assign ḡ) Γ ≡ true
        satisfies-Γ = trans (sym (agrees-all {Stmt} {Γ} agreement)) eq
