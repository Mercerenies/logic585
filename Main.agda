
module Main where

open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Theorem
open import Logic585.PropCalc.Rule
open import Logic585.PropCalc.Output

open import IO
open import Data.Unit
open import Data.List
import IO.Primitive as Prim

main : Prim.IO ⊤
main = run (putStrLn (outputWrittenProof (toWrittenProof {Γ = []} (¬⇒thm {var 1} {var 2}))))
