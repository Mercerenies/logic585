
module Logic585.PropCalc.Output where

open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Theorem
import Logic585.PropCalc.Stmt.Order as Stmt<
open import Logic585.StdLib

open import Function using (case_of_)
open import Data.String
open import Data.DifferenceList as DList using (DiffList)
open import Data.List using (List; foldr)
open import Data.Nat
open import Data.Fin using (toℕ)
open import Data.Unit
open import Data.Nat.Properties as ℕProps
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (does)
import Data.AVL.Map as Map
open import Category.Monad
open import Category.Monad.State
open import Data.Product using (proj₂)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Relation.Unary.Any using (index)

open Map Stmt<.<-strictTotalOrder

¬prec : ℕ
¬prec = 20

⇒prec : ℕ
⇒prec = 10

showParens : Bool → String → String
showParens false s = s
showParens true s = "(" ++ s ++ ")"

stmtToStringPrec : ℕ → (ℕ → String) → Stmt → String
stmtToStringPrec n f (var x) = f x
stmtToStringPrec n f (a ⇒ b) = showParens (does (n >? ⇒prec)) (a′ ++ " ⇒ " ++ b′)
  where a′ = stmtToStringPrec (suc ⇒prec) f a
        b′ = stmtToStringPrec (suc ⇒prec) f b
stmtToStringPrec n f (¬ a) = showParens (does (n >? ¬prec)) ("¬ " ++ stmtToStringPrec ¬prec f a)

stmtToString : (ℕ → String) → Stmt → String
stmtToString = stmtToStringPrec 0

postulate showNat : ℕ → String
{-# COMPILE GHC showNat = \x -> Data.Text.pack (show x) #-}

stmtToString′ : Stmt → String
stmtToString′ = stmtToString (λ n → "B" ++ showNat n)

-- Line numbers are 1-indexed
LineNumber : Set
LineNumber = ℕ

data Justification : Set where
  JAxiom : ℕ → Justification            -- Axiom number
  JModusPonens : ℕ → ℕ → Justification -- Line numbers
  JAssumption : ℕ → Justification       -- Assumption number

record ProofLine : Set where
  constructor Line
  field
    line : ℕ
    stmt : Stmt
    justification : Justification

WrittenProof : Set
WrittenProof = DiffList ProofLine

ProofCache : Set
ProofCache = Map ℕ

record ProofState : Set where
  constructor PState
  field
    nextLine : ℕ
    cache : ProofCache
    written : WrittenProof

open RawMonadState (StateMonadState ProofState)

addLineUnchecked : Stmt → Justification → State ProofState ℕ
addLineUnchecked s j = get >>= λ state →
                       let line = Line (nextLine state) s j in
                       put (PState (suc (nextLine state))
                           (insert (ProofLine.stmt line) (nextLine state) (cache state))
                           (written state ∷ʳ line)) >>
                       pure (nextLine state)
  where open ProofState

addLine : Stmt → Justification → State ProofState ℕ
addLine s j = get >>= λ state →
              case lookup s (ProofState.cache state) of λ
            { nothing → addLineUnchecked s j
            ; (just n) → pure n }

axiomToℕ : {b : Stmt} → Axiom b → ℕ
axiomToℕ A1-axiom = 1
axiomToℕ A2-axiom = 2
axiomToℕ A3-axiom = 3

toWrittenProofState : {Γ : List Stmt} {b : Stmt} → Γ ⊢ b → State ProofState ℕ
toWrittenProofState {Γ} {b} (AxIsThm x) =
  addLine b (JAxiom (axiomToℕ x))
toWrittenProofState {Γ} {b} (pf₁ $ pf₂) =
  toWrittenProofState pf₁ >>= λ line₁ →
  toWrittenProofState pf₂ >>= λ line₂ →
  addLine b (JModusPonens line₁ line₂)
toWrittenProofState {Γ} {b} (AsmIsThm x) =
  let idx = suc (toℕ (index x)) in
  addLine b (JAssumption idx)

emptyState : ProofState
ProofState.nextLine emptyState = 1
ProofState.cache emptyState = empty
ProofState.written emptyState = DList.[]

toWrittenProof : {Γ : List Stmt} {b : Stmt} → Γ ⊢ b → WrittenProof
toWrittenProof pf = ProofState.written (proj₂ (toWrittenProofState pf emptyState))

outputJustification : Justification → String
outputJustification (JAxiom n) = "(A" ++ showNat n ++ ")"
outputJustification (JModusPonens f x) = "(MP " ++ showNat f ++ " " ++ showNat x ++ ")"
outputJustification (JAssumption n) = "(Assumption " ++ showNat n ++ ")"

outputProofLine : ProofLine → String
outputProofLine (Line line stmt justification) =
  "(" ++ showNat line ++ ") " ++ stmtToString′ stmt ++ " " ++ outputJustification justification

outputWrittenProof : WrittenProof → String
outputWrittenProof pf = foldr (λ line acc → outputProofLine line ++ "\n" ++ acc) "" (DList.toList pf)
