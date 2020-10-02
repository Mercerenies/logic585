
module Logic585.PropCalc.Tautology where

open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Theorem
open import Logic585.StdLib.List using (all⊆; all-true)

open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; not)
open import Data.List
open import Data.List.Relation.Binary.Subset.Propositional

Tautology : Stmt → Set
Tautology x = (∀ (f : ℕ → Bool) → assign f x ≡ true)

RelTautology : List Stmt → Stmt → Set
RelTautology Γ x = (∀ (f : ℕ → Bool) → all (assign f) Γ ≡ true → (assign f x ≡ true))

tautologies-are-rel : {Γ : List Stmt} {x : Stmt} → Tautology x → RelTautology Γ x
tautologies-are-rel asn = λ f _ → asn f

strengthen-taut : {Γ Δ : List Stmt} {x : Stmt} → Γ ⊆ Δ → RelTautology Γ x → RelTautology Δ x
strengthen-taut sub asn = λ f eq → asn f (all⊆ sub eq)

empty-rel-taut : {x : Stmt} → RelTautology [] x → Tautology x
empty-rel-taut rel = λ f → rel f refl

identity-tautology : Tautology (var 1 ⇒ var 1)
identity-tautology f with f 1
identity-tautology f | false = refl
identity-tautology f | true = refl

axioms-are-tautologies : {b : Stmt} → Axiom b → Tautology b
axioms-are-tautologies (A1-axiom {b} {c}) f = A1-helper (assign f b) (assign f c)
  where A1-helper : (b c : Bool) → (b log⇒ (c log⇒ b)) ≡ true
        A1-helper false _ = refl
        A1-helper true false = refl
        A1-helper true true = refl
axioms-are-tautologies (A2-axiom {b} {c} {d}) f = A2-helper (assign f b) (assign f c) (assign f d)
  where A2-helper : (b c d : Bool) → ((b log⇒ (c log⇒ d)) log⇒ ((b log⇒ c) log⇒ (b log⇒ d))) ≡ true
        A2-helper false _ _ = refl
        A2-helper true false _ = refl
        A2-helper true true false = refl
        A2-helper true true true = refl
axioms-are-tautologies (A3-axiom {b} {c}) f = A3-helper (assign f b) (assign f c)
  where A3-helper : (b c : Bool) → (((not c) log⇒ (not b)) log⇒ (((not c) log⇒ b) log⇒ c)) ≡ true
        A3-helper false false = refl
        A3-helper false true = refl
        A3-helper true false = refl
        A3-helper true true = refl

theorems-are-tautologies : {Γ : List Stmt} {b : Stmt} → Γ ⊢ b → RelTautology Γ b
theorems-are-tautologies {Γ} {b} (AxIsThm ax) = tautologies-are-rel {Γ} {b} (axioms-are-tautologies ax)
theorems-are-tautologies (pf $ pf₁) = λ f x →
    MP-helper _ _ (theorems-are-tautologies pf₁ f x) (theorems-are-tautologies pf f x)
  where MP-helper : (b c : Bool) → (b ≡ true) → (b log⇒ c ≡ true) → c ≡ true
        MP-helper .true true refl refl = refl
theorems-are-tautologies (AsmIsThm elt) = λ f x → all-true elt x
