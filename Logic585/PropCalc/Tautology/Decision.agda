
module Logic585.PropCalc.Tautology.Decision where

open import Logic585.PropCalc.Tautology
open import Logic585.PropCalc.Tautology.Finite
open import Logic585.PropCalc.Stmt
open import Logic585.StdLib.List
open import Logic585.FinitePrefix using (extrapolate-fin)

open import Function.Equivalence using (equivalence)
open import Function using (_∘_; case_of_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to mapᵈ)
open import Relation.Unary using (Decidable)
open import Data.Unit

open import Reflection hiding (name; Type)

extend₀ : {n : ℕ} → Bool → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
extend₀ b f Fin.zero = b
extend₀ b f (Fin.suc x) = f x

extendᶠ : {n : ℕ} → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
extendᶠ = extend₀ false

extendᵗ : {n : ℕ} → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
extendᵗ = extend₀ true

all-assignments : (n : ℕ) → List (Fin n → Bool)
all-assignments ℕ.zero = (λ ()) ∷ []
all-assignments (ℕ.suc n) =
  let all-prior = all-assignments n in
  map extendᶠ all-prior ++ map extendᵗ all-prior

all-assignments-exhaustive : (n : ℕ) → (f : Fin n → Bool) →
  ∃[ g ] (g ∈ (all-assignments n) × (∀ (x : Fin n) → f x ≡ g x))
all-assignments-exhaustive ℕ.zero f = (λ ()) , (here refl , λ ())
all-assignments-exhaustive (ℕ.suc n) f with f Fin.zero | inspect f Fin.zero | all-assignments-exhaustive n (f ∘ Fin.suc)
... | false | [ eq ] | g , (elt , feq) =
  extendᶠ g , (++⁺ˡ (map-injective {f = extendᶠ} elt) ,
               λ { Fin.zero → eq
                 ; (Fin.suc x) → feq x })
... | true | [ eq ] | g , (elt , feq) =
  extendᵗ g , (++⁺ʳ _ (map-injective {f = extendᵗ} elt) ,
               λ { Fin.zero → eq
                 ; (Fin.suc x) → feq x })

lift-extrapolate : {n : ℕ} (b : Bool) (f g : Fin n → Bool) →
                   (∀ (x : Fin n) → f x ≡ g x) →
                   (∀ (x : ℕ) → extrapolate-fin b f x ≡ extrapolate-fin b g x)
lift-extrapolate {ℕ.zero} b f g eq x = refl
lift-extrapolate {ℕ.suc n} b f g eq ℕ.zero = eq Fin.zero
lift-extrapolate {ℕ.suc n} b f g eq (ℕ.suc x) = lift-extrapolate {n} _ _ _ (eq ∘ Fin.suc) _

assign-lemma : {n : ℕ} (f g : Fin n → Bool) (b : Stmt) → (∀ (x : Fin n) → f x ≡ g x) → assign′ f b ≡ assign′ g b
assign-lemma f g (var x) eq = lift-extrapolate false f g eq x
assign-lemma f g (b ⇒ b₁) eq = cong₂ _log⇒_ (assign-lemma f g b eq) (assign-lemma f g b₁ eq)
assign-lemma f g (Stmt.¬ b) eq = cong Bool.not (assign-lemma f g b eq)

all-is-finrel-on : (Γ : List Stmt) (b : Stmt) (n : ℕ) →
                   All (λ f → all (assign′ f) Γ ≡ true → assign′ f b ≡ true) (all-assignments n) →
                   FinRelTautologyOn n Γ b
all-is-finrel-on Γ b n all f eq =
  let g , (elt , eq₁) = all-assignments-exhaustive n f in
  trans (assign-lemma f g b eq₁)
        (all-elt elt all (trans (all≡lemma {ℓ = Γ} {assign′ g} {assign′ f}
                                           λ x _ → assign-lemma g f x (sym ∘ eq₁))
                                eq))

finrel-on-is-all : (Γ : List Stmt) (b : Stmt) (n : ℕ) →
                   FinRelTautologyOn n Γ b →
                   All (λ f → all (assign′ f) Γ ≡ true → assign′ f b ≡ true) (all-assignments n)
finrel-on-is-all Γ b n finrel = All.tabulate λ {f} _ asn → finrel f asn

assignment-is-dec : (Γ : List Stmt) (b : Stmt) (n : ℕ) →
                    Decidable (λ f → all (assign′ {n} f) Γ ≡ true → assign′ f b ≡ true)
assignment-is-dec Γ b n f with all (assign′ f) Γ | assign′ f b
assignment-is-dec Γ b n f | false | _ = yes (λ ())
assignment-is-dec Γ b n f | true | false = no (λ impl → case impl refl of λ ())
assignment-is-dec Γ b n f | true | true = yes (λ eq → eq)

finrel-on-decidable : (Γ : List Stmt) (b : Stmt) (n : ℕ) → Dec (FinRelTautologyOn n Γ b)
finrel-on-decidable Γ b n = mapᵈ (equivalence (all-is-finrel-on Γ b n) (finrel-on-is-all Γ b n))
                                 (All.all (assignment-is-dec Γ b n) _)

finrel-decidable : (Γ : List Stmt) (b : Stmt) → Dec (FinRelTautology Γ b)
finrel-decidable Γ b = finrel-on-decidable Γ b _

rel-decidable : (Γ : List Stmt) (b : Stmt) → Dec (RelTautology Γ b)
rel-decidable Γ b = mapᵈ (equivalence (fin-rel-is-rel {Γ} {b}) (rel-is-fin-rel {Γ} {b})) (finrel-decidable Γ b)

taut-decidable : (b : Stmt) → Dec (Tautology b)
taut-decidable b = mapᵈ (equivalence (empty-rel-taut {b}) (tautologies-are-rel {[]} {b})) (rel-decidable [] b)

{- ///// Figure this out
macro
  do-tautology : Term → Term → TC ⊤
  do-tautology b₀ t = unquoteTC b₀ >>= λ b →
                      case taut-decidable b of λ
                      { (no ¬pf) → typeError (strErr "Not a tautology" ∷ termErr b₀ ∷ [])
                      ; (yes pf) → unify t (quoteTerm pf) }
-}
