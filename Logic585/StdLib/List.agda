
module Logic585.StdLib.List where

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List
open import Function using (id; _∘_)
open import Function.Definitions using (Injective)
open import Data.List.Properties
import Data.List.Membership.Propositional as PropMembership
import Data.List.Membership.DecPropositional as DecPropMembership
open import Relation.Unary using (Pred)
open import Data.List.Relation.Unary.Any hiding (map)
import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Bool
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty
open import Data.Sum as Sum hiding (map)

-- Some helpers for standard lib lists that I couldn't find provided
-- directly. It's entirely possible these are available in the
-- standard lib and I just missed them.

module _ {a} {A : Set a} where

  open PropMembership {A = A}

  ∈≡lemma : {ℓ : List A} {x y : A} → x ∈ ℓ → x ≡ y → y ∈ ℓ
  ∈≡lemma elt refl = elt

  ∈≡lemma₂ : {ℓ ℓ₁ : List A} {x : A} → x ∈ ℓ → ℓ ≡ ℓ₁ → x ∈ ℓ₁
  ∈≡lemma₂ elt refl = elt

module _ {a} {p} {A : Set a} where
  open PropMembership {A = A}

  all-elt : {ℓ : List A} {x : A} {P : Pred A p} → x ∈ ℓ → All P ℓ → P x
  all-elt (here refl) (fst All.∷ rest) = fst
  all-elt (there elt) (fst All.∷ rest) = all-elt elt rest

module _ {a} {A : Set a} where
  open PropMembership {A = A}

  all≡lemma : {ℓ : List A} {f g : A → Bool} → (∀ (x : A) → (x ∈ ℓ) → f x ≡ g x) → all f ℓ ≡ all g ℓ
  all≡lemma {[]} _ = refl
  all≡lemma {x ∷ ℓ} {f} {g} eq with f x | g x | eq x (here refl) | all≡lemma {ℓ} λ x eq₀ → eq x (there eq₀)
  all≡lemma {x ∷ ℓ} {f} {g} eq | false | false | refl | _ = refl
  all≡lemma {x ∷ ℓ} {f} {g} eq | true | true | refl | eq₂ = eq₂

module _ {a b} {A : Set a} {B : Set b} where

  private
    _∈A_ : A → List A → Set _
    _∈A_ = PropMembership._∈_

  private
    _∈B_ : B → List B → Set _
    _∈B_ = PropMembership._∈_

  map-injective : {ℓ : List A} {f : A → B} {x : A} → x ∈A ℓ → f x ∈B map f ℓ
  map-injective (here refl) = here refl
  map-injective (there elt) = there (map-injective elt)

  map-injective′ : {ℓ : List A} {f : A → B} {x : A} {y : B} → x ∈A ℓ → y ≡ f x → y ∈B map f ℓ
  map-injective′ elt refl = map-injective elt

  map-resp-inj : {ℓ : List A} {f : A → B} {x : A} → (_≟_ : ∀ (b b₁ : B) → Dec (b ≡ b₁)) → Injective _≡_ _≡_ f → f x ∈B map f ℓ → x ∈A ℓ
  map-resp-inj {x₀ ∷ ℓ} {f} {x} dec inj elt with dec (f x) (f x₀)
  map-resp-inj {x₀ ∷ ℓ} {f} {x} dec inj (here eq) | no ¬proof = ⊥-elim (¬proof eq)
  map-resp-inj {x₀ ∷ ℓ} {f} {x} dec inj (there elt) | no ¬proof = there (map-resp-inj dec inj elt)
  map-resp-inj {x₀ ∷ ℓ} {f} {x} dec inj elt | yes proof = here (inj proof)

  map⊆ : {ℓ₁ ℓ₂ : List A} {f : A → B} → (_≟_ : ∀ (b b₁ : B) → Dec (b ≡ b₁)) → ℓ₁ ⊆ ℓ₂ → map f ℓ₁ ⊆ map f ℓ₂
  map⊆ {x₁ ∷ ℓ₁} {[]} dec sub elt with sub (here refl)
  ... | ()
  map⊆ {x₁ ∷ ℓ₁} {x₂ ∷ ℓ₂} {f} dec sub (here px) = ∈≡lemma (map-injective (sub (here refl))) (sym px)
  map⊆ {x₁ ∷ ℓ₁} {x₂ ∷ ℓ₂} dec sub (there elt) = map⊆ {ℓ₁} dec (sub ∘ there) elt

module _ {a} {A : Set a} where

  build-list≡ : {x x₁ : A} {ℓ ℓ₁ : List A} → x ≡ x₁ → ℓ ≡ ℓ₁ → (x ∷ ℓ) ≡ (x₁ ∷ ℓ₁)
  build-list≡ refl refl = refl

module _ {a b c} {A : Set a} {B B₁ : Set b} {C : Set c} where

  private
    _∈A_ : A → List A → Set _
    _∈A_ = PropMembership._∈_

  map-commute : {ℓ : List A} (f′ : A → B₁) (g′ : B₁ → C) (g : A → B) (f : B → C) →
                (∀ (x : A) → (x ∈A ℓ) → f (g x) ≡ g′ (f′ x)) →
                map f (map g ℓ) ≡ map g′ (map f′ ℓ)
  map-commute {[]} _ _ _ _ _ = refl
  map-commute {x ∷ ℓ} f′ g′ g f all-eq with all-eq x (here refl) | map-commute {ℓ} f′ g′ g f (λ x elt → all-eq x (there elt))
  ... | eq₁ | eq₂ = build-list≡ eq₁ eq₂

module _ {a} {A : Set a} where

  open DecPropMembership _≟_

  all-false : {ℓ : List A} {f : A → Bool} → false ∈ map f ℓ → all f ℓ ≡ false
  all-false {ℓ = x ∷ _} {f} _ with f x
  all-false {_ ∷ _} {_} _ | false = refl
  all-false {_ ∷ _} {_} (there elt) | true = all-false elt

module _ {a} {A : Set a} where

  all⊆ : {ℓ₁ ℓ₂ : List A} {f : A → Bool} → ℓ₁ ⊆ ℓ₂ → all f ℓ₂ ≡ true → all f ℓ₁ ≡ true
  all⊆ {ℓ₁ = []} sub pf = refl
  all⊆ {ℓ₁ = x ∷ ℓ₁} {f = f} sub pf with f x | inspect f x
  all⊆ {x ∷ ℓ₁} {ℓ₂} {f} sub pf | false | Reveal_·_is_.[ fx≡false ] =
    trans (sym (all-false {f = f} (∈≡lemma (map-injective (sub (here refl))) fx≡false))) pf
  all⊆ {x ∷ ℓ₁} {ℓ₂} {f} sub pf | true | Reveal_·_is_.[ fx≡true ] = all⊆ (sub ∘ there) pf

-- This whole module is shamelessly copied from a newer version of the stdlib
module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  reverseAcc⁺ : ∀ acc xs → Any P acc ⊎ Any P xs → Any P (reverseAcc acc xs)
  reverseAcc⁺ acc [] (inj₁ ps) = ps
  reverseAcc⁺ acc (x ∷ xs) (inj₁ ps) = reverseAcc⁺ (x ∷ acc) xs (inj₁ (there ps))
  reverseAcc⁺ acc (x ∷ xs) (inj₂ (here px)) = reverseAcc⁺ (x ∷ acc) xs (inj₁ (here px))
  reverseAcc⁺ acc (x ∷ xs) (inj₂ (there y)) = reverseAcc⁺ (x ∷ acc) xs (inj₂ y)

  reverseAcc⁻ : ∀ acc xs → Any P (reverseAcc acc xs) -> Any P acc ⊎ Any P xs
  reverseAcc⁻ acc [] ps = inj₁ ps
  reverseAcc⁻ acc (x ∷ xs) ps rewrite ʳ++-defn xs {x ∷ acc} with ++⁻ (reverseAcc [] xs) {x ∷ acc} ps
  reverseAcc⁻ acc (x ∷ xs) ps | inj₁ ps' with reverseAcc⁻ [] xs ps'
  reverseAcc⁻ acc (x ∷ xs) ps | inj₁ ps' | inj₂ ps'' = inj₂ (there ps'')
  reverseAcc⁻ acc (x ∷ xs) ps | inj₂ (here p') = inj₂ (here p')
  reverseAcc⁻ acc (x ∷ xs) ps | inj₂ (there ps') = inj₁ ps'

  reverse⁺ : ∀ {xs} → Any P xs → Any P (reverse xs)
  reverse⁺ ps = reverseAcc⁺ [] _ (inj₂ ps)

  reverse⁻ : ∀ {xs} → Any P (reverse xs) → Any P xs
  reverse⁻ ps with reverseAcc⁻ [] _ ps
  reverse⁻ ps | inj₂ ps' = ps'

module _ {a} {A : Set a} where

  open PropMembership {A = A}

  all-true : {x : A} {ℓ : List A} {f : A → Bool} → x ∈ ℓ → all f ℓ ≡ true → f x ≡ true
  all-true {x} {_} {f} (here refl) eq with f x
  all-true {_} {.(_ ∷ _)} {f} (here refl) eq | true = refl
  all-true {x} {x₁ ∷ ℓ} {f} (there elt) eq = all-true {x} {ℓ} {f} elt (all⊆ {ℓ₁ = ℓ} there eq)

  unfold-reverse′ : ∀ (x : A) (xs : List A) → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
  unfold-reverse′ x xs =          begin
    rev (xs ∷ʳ x)                 ≡˘⟨ cong (λ ys → rev (ys ∷ʳ x)) (reverse-involutive xs) ⟩
    rev (rev (rev xs) ∷ʳ x)       ≡˘⟨ cong rev (unfold-reverse x (rev xs)) ⟩
    rev (rev (x ∷ rev xs))        ≡⟨ reverse-involutive _ ⟩
    x ∷ rev xs                    ∎
   where rev = reverse

  ∷-∷ʳ : (x : A) (ℓ : List A) (y : A) → (x ∷ ℓ) ∷ʳ y ≡ x ∷ (ℓ ∷ʳ y)
  ∷-∷ʳ x ℓ y = refl

  []⊆ : {A : Set} {ℓ : List A} → [] ⊆ ℓ
  []⊆ ()

  ∈≡ : {x : A} {ℓ₁ ℓ₂ : List A} → (ℓ₁ ≡ ℓ₂) → x ∈ ℓ₁ → x ∈ ℓ₂
  ∈≡ refl elt = elt

module _ {a b} {A : Set a} {B : Set b} where

  private
    _∈A_ : A → List A → Set _
    _∈A_ = PropMembership._∈_

  private
    _∈B_ : B → List B → Set _
    _∈B_ = PropMembership._∈_

  map-build : (x : A) (ℓ : List A) (f : A → B) → map f (x ∷ ℓ) ≡ (f x) ∷ map f ℓ
  map-build _ _ _ = refl

  map-buildʳ : (x : A) (ℓ : List A) (f : A → B) → map f (ℓ ∷ʳ x) ≡ map f ℓ ∷ʳ f x
  map-buildʳ x ℓ f =            begin
    map f (ℓ ∷ʳ x)              ≡˘⟨ reverse-involutive _ ⟩
    rev (rev (map f (ℓ ∷ʳ x)))  ≡˘⟨ cong rev (reverse-map-commute f (ℓ ∷ʳ x)) ⟩
    rev (map f (rev (ℓ ∷ʳ x)))  ≡⟨ cong (rev ∘ map f) (unfold-reverse′ x ℓ) ⟩
    rev (map f (x ∷ rev ℓ))     ≡⟨⟩
    rev (f x ∷ map f (rev ℓ))   ≡⟨ unfold-reverse (f x) (map f (rev ℓ)) ⟩
    rev (map f (rev ℓ)) ∷ʳ f x  ≡˘⟨ cong (λ y → y ∷ʳ f x) (reverse-map-commute f (rev ℓ)) ⟩
    map f (rev (rev ℓ)) ∷ʳ f x  ≡⟨ cong (λ y → map f y ∷ʳ f x) (reverse-involutive ℓ) ⟩
    map f ℓ ∷ʳ f x              ∎
   where rev = reverse
