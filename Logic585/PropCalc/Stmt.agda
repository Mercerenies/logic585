
module Logic585.PropCalc.Stmt where

open import Logic585.StdLib
open import Logic585.FinitePrefix

open import Function using (_∘_)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary using (does; no; yes)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Data.Nat as ℕ using (ℕ)
open import Data.Product hiding (map)
open import Data.Bool as 𝔹 using (Bool; true; false)
open import Data.List
import Data.Nat.Properties as ℕProps
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FinProps

data Stmt : Set where
  var : ℕ → Stmt
  _⇒_ : Stmt → Stmt → Stmt
  ¬_ : Stmt → Stmt

infixr 10 _⇔_
infixr 20 _⇒_
infixr 20 _log⇒_
infix 30 ¬_
infixr 26 _∧_
infixr 25 _∨_

var-injective : ∀ {m n} → var m ≡ var n → m ≡ n
var-injective refl = refl

¬-injective : ∀ {a b} → ¬ a ≡ ¬ b → a ≡ b
¬-injective refl = refl

⇒-injective : ∀ {b b₁ c c₁} → (b ⇒ b₁) ≡ (c ⇒ c₁) → (b ≡ c) × (b₁ ≡ c₁)
⇒-injective refl = refl , refl

_≟_ : Decidable {A = Stmt} _≡_
var x ≟ var y = map′ (cong var) var-injective (x ℕ.≟ y)
var _ ≟ (_ ⇒ _) = no λ ()
var _ ≟ (¬ _) = no λ ()
(_ ⇒ _) ≟ var _ = no λ ()
(b ⇒ b₁) ≟ (c ⇒ c₁) = map′ (uncurry (cong₂ _⇒_)) ⇒-injective (b ≟ c ×-dec b₁ ≟ c₁)
(_ ⇒ _) ≟ (¬ _) = no λ ()
(¬ _) ≟ var _ = no λ ()
(¬ _) ≟ (_ ⇒ _) = no λ ()
(¬ b) ≟ (¬ c) = map′ (cong ¬_) ¬-injective (b ≟ c)

infix 4 _≟_

_∧_ : Stmt → Stmt → Stmt
b ∧ c = ¬ (b ⇒ ¬ c)

_∨_ : Stmt → Stmt → Stmt
b ∨ c = ¬ b ⇒ c

_⇔_ : Stmt → Stmt → Stmt
b ⇔ c = (b ⇒ c) ∧ (c ⇒ b)

_log⇒_ : Bool → Bool → Bool
_log⇒_ = does ∘₂ 𝔹._≤?_

cata : {A : Set} → (ℕ → A) → (A → A → A) → (A → A) → Stmt → A
cata f _ _ (var x) = f x
cata f g h (x ⇒ x₁) = g (cata f g h x) (cata f g h x₁)
cata f g h (¬ x) = h (cata f g h x)

substitute : (ℕ → Stmt) → Stmt → Stmt
substitute f = cata f _⇒_ ¬_

assign : (ℕ → Bool) → Stmt → Bool
assign f = cata f _log⇒_ 𝔹.not

vars-of : Stmt → ℕ
vars-of (var x) = ℕ.suc x
vars-of (s ⇒ s₁) = vars-of s ℕ.⊔ vars-of s₁
vars-of (¬ s) = vars-of s

assignment-uses-prefix : {f g : ℕ → Bool} {c : Stmt} → AgreesPrefix (vars-of c) f g → assign f c ≡ assign g c
assignment-uses-prefix {f} {g} {var x} agree with agree (Fin.fromℕ x)
... | u = trans (cong f (sym (FinProps.toℕ-fromℕ _))) (trans u (cong g (FinProps.toℕ-fromℕ _)))
assignment-uses-prefix {f} {g} {c ⇒ c₁} agree with assign f c | assign g c | assign f c₁ | assign g c₁ | assignment-uses-prefix {f} {g} {c} (agrees-shorter {f = f} {g = g} (ℕProps.m≤m⊔n _ _) agree) | assignment-uses-prefix {f} {g} {c₁} (agrees-shorter {f = f} {g = g} (ℕProps.n≤m⊔n _ _) agree)
assignment-uses-prefix {f} {g} {c ⇒ c₁} agree | false | false | false | false | refl | refl = refl
assignment-uses-prefix {f} {g} {c ⇒ c₁} agree | false | false | true | true | refl | refl = refl
assignment-uses-prefix {f} {g} {c ⇒ c₁} agree | true | true | false | false | refl | refl = refl
assignment-uses-prefix {f} {g} {c ⇒ c₁} agree | true | true | true | true | refl | refl = refl
assignment-uses-prefix {f} {g} {¬ c} agree with assign f c | assign g c | assignment-uses-prefix {f} {g} {c} agree
assignment-uses-prefix {f} {g} {¬ c} agree | false | false | refl = refl
assignment-uses-prefix {f} {g} {¬ c} agree | true | true | refl = refl

agrees-all : {A : Set} {Δ : List Stmt} {m : ℕ} {f g : ℕ → Bool} →
             AgreesPrefix (foldr ℕ._⊔_ m (map vars-of Δ)) f g → all (assign f) Δ ≡ all (assign g) Δ
agrees-all {_} {[]} {_} {_} {_} _ = refl
agrees-all {A} {x ∷ Δ} {m} {f} {g} agrees = all-lemma {_} {x} {Δ} agree₁ agree₂
  where agree₁ : assign f x ≡ assign g x
        agree₁ = assignment-uses-prefix {f} {g} {x} (agrees-shorter {f = f} {g = g} (ℕProps.m≤m⊔n _ _) agrees)
        agree₂ : all (assign f) Δ ≡ all (assign g) Δ
        agree₂ = agrees-all {A} {Δ} {m} {f} {g} (agrees-shorter {f = f} {g = g} (ℕProps.n≤m⊔n _ _) agrees)
        all-lemma : {B : Set} {y : B} {Δ₁ : List B} {h₁ h₂ : B → Bool} →
                    h₁ y ≡ h₂ y → all h₁ Δ₁ ≡ all h₂ Δ₁ → all h₁ (y ∷ Δ₁) ≡ all h₂ (y ∷ Δ₁)
        all-lemma {_} {y} {Δ₁} {h₁} {h₂} eq₁ eq₂ with h₁ y | h₂ y | all h₁ Δ₁ | all h₂ Δ₁
        all-lemma {_} {y} {Δ₁} {h₁} {h₂} refl _ | false | false | _ | _ = refl
        all-lemma {_} {y} {Δ₁} {h₁} {h₂} refl refl | true | true | false | false = refl
        all-lemma {_} {y} {Δ₁} {h₁} {h₂} refl refl | true | true | true | true = refl

assign′ : {n : ℕ} → (Fin n → Bool) → Stmt → Bool
assign′ f = assign (extrapolate-fin false f)
