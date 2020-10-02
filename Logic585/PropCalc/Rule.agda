
module Logic585.PropCalc.Rule where

open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Theorem
open import Logic585.StdLib.List using (map-injective)

import Function as Fn
open import Data.List
open import Data.List.Relation.Binary.Subset.Propositional
import Data.List.Membership.DecPropositional as DecPropMembership
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ)

open DecPropMembership _≟_

-- Useful facts and derived rules for use in Prop Calc proofs

infixr 25 _∘_
infixl 20 _$snd_

id-thm : {b : Stmt} → ⊢ b ⇒ b
id-thm {b = b} = A2 $ A1 $ A1 {c = b ⇒ b}

+asm : {Δ Γ : List Stmt} {b : Stmt} → Δ ⊆ Γ → Δ ⊢ b → Γ ⊢ b
+asm sub (AxIsThm ax) = AxIsThm ax
+asm sub (pf $ pf₁) = +asm sub pf $ +asm sub pf₁
+asm sub (AsmIsThm elt) = AsmIsThm (sub elt)

trans-ent : {Δ Γ : List Stmt} {c : Stmt} → Δ ⊢ c → (∀ {b : Stmt} → b ∈ Δ → Γ ⊢ b) → Γ ⊢ c
trans-ent (AxIsThm ax) _ = AxIsThm ax
trans-ent (pf $ pf₁) apriori = trans-ent pf apriori $ trans-ent pf₁ apriori
trans-ent (AsmIsThm elt) apriori = apriori elt

+ante : {Γ : List Stmt} {b c : Stmt} → Γ ⊢ c → Γ ⊢ b ⇒ c
+ante pf = A1 $ pf

_∘_ : {Γ : List Stmt} {b c d : Stmt} → Γ ⊢ c ⇒ d → Γ ⊢ b ⇒ c → Γ ⊢ b ⇒ d
pf₁ ∘ pf₂ = A2 $ +ante pf₁ $ pf₂

-- Deduction Theorem
with-asm : {Γ : List Stmt} {b c : Stmt} → b ∷ Γ ⊢ c → Γ ⊢ b ⇒ c
with-asm (AxIsThm ax) = +ante (AxIsThm ax)
with-asm (pf $ pf₁) = A2 $ with-asm pf $ with-asm pf₁
with-asm (AsmIsThm (here refl)) = id-thm
with-asm (AsmIsThm (there elt)) = +ante (AsmIsThm elt)

-- Super-useful application of deduction theorem
ṡ : {Γ : List Stmt} {b c : Stmt} → (b ∷ Γ ⊢ b → b ∷ Γ ⊢ c) → Γ ⊢ b ⇒ c
ṡ f = with-asm (f Asm1)

ṡ₂ : {Γ : List Stmt} {b c d : Stmt} → (c ∷ b ∷ Γ ⊢ b → c ∷ b ∷ Γ ⊢ c → c ∷ b ∷ Γ ⊢ d) → Γ ⊢ b ⇒ c ⇒ d
ṡ₂ f = ṡ λ x → ṡ λ y → f (+asm there x) y

ṡ-syntax : {Γ : List Stmt} {b c : Stmt} → (b ∷ Γ ⊢ b → b ∷ Γ ⊢ c) → Γ ⊢ b ⇒ c
ṡ-syntax = ṡ

ṡ₂-syntax : {Γ : List Stmt} {b c d : Stmt} → (c ∷ b ∷ Γ ⊢ b → c ∷ b ∷ Γ ⊢ c → c ∷ b ∷ Γ ⊢ d) → Γ ⊢ b ⇒ c ⇒ d
ṡ₂-syntax = ṡ₂

syntax ṡ-syntax (λ x → concl) = ṡ[ x ] concl

-- Why doesn't this work?
--syntax ṡ₂-syntax (λ x y → concl) = ṡ₂[ x , y ] concl

infix 2 ṡ-syntax
infix 2 ṡ₂-syntax

swap⇒ : {Γ : List Stmt} {b c d : Stmt} → Γ ⊢ b ⇒ c ⇒ d → Γ ⊢ c ⇒ b ⇒ d
swap⇒ pf = ṡ₂ λ x y → +asm (there Fn.∘ there) pf $ y $ x

MPRule : {b c : Stmt} → ⊢ b ⇒ (b ⇒ c) ⇒ c
MPRule = swap⇒ id-thm

¬self⇒ : {b : Stmt} → ⊢ (¬ b ⇒ b) ⇒ b
¬self⇒ = A3 $ id-thm

_$snd_ : {Γ : List Stmt} {b c d : Stmt} → Γ ⊢ b ⇒ c ⇒ d → Γ ⊢ c → Γ ⊢ b ⇒ d
_$snd_ f x = swap⇒ f $ x

¬¬elim : {b : Stmt} → ⊢ (¬ ¬ b ⇒ b)
¬¬elim = ṡ[ ¬¬b ] A3 $ +ante ¬¬b $ id-thm

¬¬intro : {b : Stmt} → ⊢ (b ⇒ ¬ ¬ b)
¬¬intro = ṡ[ b ] A3 $ ¬¬elim $ +ante b

explosion : {b c : Stmt} → ⊢ (¬ b ⇒ b ⇒ c)
explosion = ṡ₂ λ ¬b b → A3 $ +ante ¬b $ +ante b

contra₁ : {b c : Stmt} → ⊢ ((¬ c ⇒ ¬ b) ⇒ (b ⇒ c))
contra₁ = (ṡ₂ λ f b → f $ +ante b) ∘ A3

contra₂ : {b c : Stmt} → ⊢ ((b ⇒ c) ⇒ (¬ c ⇒ ¬ b))
contra₂ = ṡ[ b⇒c ] contra₁ $ ¬¬intro ∘ b⇒c ∘ ¬¬elim

¬⇒thm : {b c : Stmt} → ⊢ (b ⇒ ¬ c ⇒ ¬ (b ⇒ c))
¬⇒thm = ṡ[ b ] contra₂ $ (MPRule $ Asm1)

in-any-case : {b c : Stmt} → ⊢ ((b ⇒ c) ⇒ (¬ b ⇒ c) ⇒ c)
in-any-case = ṡ₂ λ b⇒c ¬b⇒c -> A3 $ (contra₂ $ b⇒c) $ ¬¬elim ∘ (contra₂ $ (¬b⇒c))

proofs-lift : {Γ : List Stmt} {b : Stmt} → (f : ℕ → Stmt) → Γ ⊢ b → map (substitute f) Γ ⊢ substitute f b
proofs-lift f (AxIsThm x) = AxIsThm (substitute-ax f x)
proofs-lift f (pf $ pf₁) = proofs-lift f pf $ proofs-lift f pf₁
proofs-lift f (AsmIsThm elt) = AsmIsThm (map-injective elt)
