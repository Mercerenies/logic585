
module Logic585.PropCalc.Theorem where

open import Logic585.PropCalc.Stmt

open import Data.Nat using (ℕ)
open import Data.List
import Data.List.Membership.DecPropositional as DecPropMembership
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality

open DecPropMembership (_≟_)

data Axiom : Stmt → Set where
  A1-axiom : {b c : Stmt} → Axiom (b ⇒ c ⇒ b)
  A2-axiom : {b c d : Stmt} → Axiom ((b ⇒ c ⇒ d) ⇒ (b ⇒ c) ⇒ (b ⇒ d))
  A3-axiom : {b c : Stmt} → Axiom ((¬ c ⇒ ¬ b) ⇒ (¬ c ⇒ b) ⇒ c)

data _⊢_ (Γ : List Stmt) (b : Stmt) : Set where
  AxIsThm : Axiom b → Γ ⊢ b
  _$_ : {b₁ : Stmt} → Γ ⊢ (b₁ ⇒ b) → Γ ⊢ b₁ → Γ ⊢ b -- Modus ponens
  AsmIsThm : b ∈ Γ → Γ ⊢ b

infix 4 _⊢_
infix 4 ⊢_
infixl 20 _$_

⊢_ : Stmt → Set
⊢ b = {Γ : List Stmt} → Γ ⊢ b

A1 : {b c : Stmt} → ⊢ b ⇒ c ⇒ b
A1 = AxIsThm A1-axiom

A2 : {b c d : Stmt} → ⊢ (b ⇒ c ⇒ d) ⇒ (b ⇒ c) ⇒ (b ⇒ d)
A2 = AxIsThm A2-axiom

A3 : {b c : Stmt} → ⊢ (¬ c ⇒ ¬ b) ⇒ (¬ c ⇒ b) ⇒ c
A3 = AxIsThm A3-axiom

Asm1 : {b : Stmt} {Γ : List Stmt} → b ∷ Γ ⊢ b
Asm1 = AsmIsThm (here refl)

Asm2 : {b c : Stmt} {Γ : List Stmt} → b ∷ c ∷ Γ ⊢ c
Asm2 = AsmIsThm (there (here refl))

Asm3 : {b c d : Stmt} {Γ : List Stmt} → b ∷ c ∷ d ∷ Γ ⊢ d
Asm3 = AsmIsThm (there (there (here refl)))

Asm4 : {b c d e : Stmt} {Γ : List Stmt} → b ∷ c ∷ d ∷ e ∷ Γ ⊢ e
Asm4 = AsmIsThm (there (there (there (here refl))))

substitute-ax : {b : Stmt} → (f : ℕ → Stmt) → Axiom b → Axiom (substitute f b)
substitute-ax _ A1-axiom = A1-axiom
substitute-ax _ A2-axiom = A2-axiom
substitute-ax _ A3-axiom = A3-axiom
