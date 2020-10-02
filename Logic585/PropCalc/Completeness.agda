
module Logic585.PropCalc.Completeness where

open import Logic585.PropCalc.Tautology
open import Logic585.PropCalc.Tautology.Finite
open import Logic585.FinitePrefix using (extrapolate-fin; extrapolate-agrees)
open import Logic585.PropCalc.Stmt
open import Logic585.PropCalc.Theorem
open import Logic585.PropCalc.Rule hiding (_∘_)
open import Logic585.StdLib.List

open import Function using (_∘_; case_of_)
open import Data.Bool hiding (_≟_)
open import Data.Nat as ℕ using (ℕ; _∸_)
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FinProps
open import Data.List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.All.Properties as AllProps
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
import Data.List.Membership.DecPropositional as DecPropMembership
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Binary.Subset.Propositional
import Data.Nat.Properties as ℕProps
import Data.List.Properties as ListProps
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _,_; proj₂)
open import Relation.Nullary using (does; yes; no)

-- This function will return b for any statement b which is true under
-- the assignment, or ¬ b for any statement which is false.
under : (Stmt → Bool) → Stmt → Stmt
under f b with f b
under f b | false = ¬ b
under f b | true = b

all-fin : {n : ℕ} → List (Fin n)
all-fin {ℕ.zero} = []
all-fin {ℕ.suc _} = Fin.zero ∷ map Fin.suc all-fin

all-fin-exhaustive : {n : ℕ} → (m : Fin n) → DecPropMembership._∈_ (Fin._≟_ {n}) m all-fin
all-fin-exhaustive Fin.zero = here refl
all-fin-exhaustive (Fin.suc m) = there (map-injective (all-fin-exhaustive m))

toℕ-suc : {n : ℕ} {m : Fin n} → Fin.toℕ (Fin.suc m) ≡ ℕ.suc (Fin.toℕ m)
toℕ-suc = refl

module _ where

  open DecPropMembership ℕ._≟_

  suc-map-lemma : {x : ℕ} {ℓ : List ℕ} → ℕ.suc x ∈ map ℕ.suc ℓ → x ∈ ℓ
  suc-map-lemma = map-resp-inj ℕ._≟_ ℕProps.suc-injective

all-fin⊆ : {n m : ℕ} → n ℕ.≤ m → map Fin.toℕ (all-fin {n}) ⊆ map Fin.toℕ (all-fin {m})
all-fin⊆ ℕ.z≤n ()
all-fin⊆ (ℕ.s≤s leq) (here px) = here px
all-fin⊆ {.(ℕ.suc _)} (ℕ.s≤s leq) {ℕ.zero} (there elt) = here refl
all-fin⊆ {.(ℕ.suc _)} (ℕ.s≤s leq) {ℕ.suc x} (there elt) =
  there (∈≡lemma₂ (map-injective (all-fin⊆ leq (suc-map-lemma (∈≡lemma₂ elt (sym commute₂)))))
                  commute₁)
 where commute₁ = map-commute Fin.suc Fin.toℕ Fin.toℕ ℕ.suc λ x₁ elt → toℕ-suc {m = x₁}
       commute₂ = map-commute Fin.suc Fin.toℕ Fin.toℕ ℕ.suc λ x₁ elt → toℕ-suc {m = x₁}

open DecPropMembership _≟_

under-var : (Stmt → Bool) → ℕ → Stmt
under-var f n = under f (var n)

to-assumptions : {n : ℕ} → (Fin n → Bool) → List Stmt
to-assumptions {n} f = map (under-var (assign′ f)) (map Fin.toℕ (all-fin {n}))

var-in-asm-lemma : {n m : ℕ} → (n ℕ.< m) → (f : Fin m → Bool) → under-var (assign′ f) n ∈ to-assumptions f
var-in-asm-lemma {n} {m} leq f =
  map-injective (map-injective′ (all-fin-exhaustive {m} _) (sym (FinProps.toℕ-fromℕ< leq)))

equal-value-pf : {Γ : List Stmt} {b c : Stmt} → (b ≡ c) → Γ ⊢ b → Γ ⊢ c
equal-value-pf refl x = x

equal-asm-pf : {Γ Δ : List Stmt} {b : Stmt} → (Γ ≡ Δ) → Γ ⊢ b → Δ ⊢ b
equal-asm-pf refl x = x

vars⇒₁ : {b b₁ : Stmt} → vars-of b ℕ.≤ vars-of (b ⇒ b₁)
vars⇒₁ = ℕProps.m≤m⊔n _ _

vars⇒₂ : {b b₁ : Stmt} → vars-of b₁ ℕ.≤ vars-of (b ⇒ b₁)
vars⇒₂ = ℕProps.n≤m⊔n _ _

-- This is referred to as Lemma 1.13 in the book.
assigned-asm-lemma : {b : Stmt} {n : ℕ} → (vars-of b ℕ.≤ n) → (f : Fin n → Bool) →
                     to-assumptions f ⊢ under (assign′ f) b
assigned-asm-lemma {var x} leq f = AsmIsThm (var-in-asm-lemma leq f)
assigned-asm-lemma {b ⇒ b₁} leq f with assign′ f b | inspect (under (assign′ f)) b | assign′ f b₁ | inspect (under (assign′ f)) b₁
assigned-asm-lemma {b ⇒ b₁} leq f | false | [ eq ] | b₁asn | [ eq₁ ] =
  contra₁ $ +ante (equal-value-pf eq (assigned-asm-lemma {b} (ℕProps.≤-trans (vars⇒₁ {b} {b₁}) leq) f))
assigned-asm-lemma {b ⇒ b₁} leq f | true | [ eq ] | false | [ eq₁ ] =
  ¬⇒thm $ equal-value-pf eq (assigned-asm-lemma {b} (ℕProps.≤-trans (vars⇒₁ {b} {b₁}) leq) f)
        $ equal-value-pf eq₁ (assigned-asm-lemma {b₁} (ℕProps.≤-trans (vars⇒₂ {b} {b₁}) leq) f)
assigned-asm-lemma {b ⇒ b₁} leq f | true | [ eq ] | true | [ eq₁ ] =
  +ante (equal-value-pf eq₁ (assigned-asm-lemma {b₁} (ℕProps.≤-trans (vars⇒₂ {b} {b₁}) leq) f))
assigned-asm-lemma {¬ b} leq f with assign′ f b | inspect (under (assign′ f)) b
assigned-asm-lemma {¬ b} leq f | false | [ eq ] = equal-value-pf eq (assigned-asm-lemma {b} leq f)
assigned-asm-lemma {¬ b} leq f | true | [ eq ] = ¬¬intro $ equal-value-pf eq (assigned-asm-lemma {b} leq f)

assigned-asm-lemma′ : {b : Stmt} → (f : Fin (vars-of b) → Bool) →
                      to-assumptions f ⊢ under (assign′ f) b
assigned-asm-lemma′ {b} = assigned-asm-lemma {b} ℕProps.≤-refl

reversed-pf⁻ : {Γ : List Stmt} {b : Stmt} →
               reverse Γ ⊢ b →
               Γ ⊢ b
reversed-pf⁻ = +asm reverse⁻

reversed-pf⁺ : {Γ : List Stmt} {b : Stmt} →
               Γ ⊢ b →
               reverse Γ ⊢ b
reversed-pf⁺ = +asm reverse⁺

common-asm-elim : {Γ : List Stmt} {b c : Stmt} → c ∷ Γ ⊢ b → ¬ c ∷ Γ ⊢ b → Γ ⊢ b
common-asm-elim b₁ b₂ = in-any-case $ with-asm b₁ $ with-asm b₂

common-asm-elimʳ : {Γ : List Stmt} {b c : Stmt} → Γ ∷ʳ c ⊢ b →  Γ ∷ʳ ¬ c ⊢ b → Γ ⊢ b
common-asm-elimʳ {Γ} {b} {c} b₁ b₂ =
  reversed-pf⁻ (common-asm-elim (equal-asm-pf (unfold-reverse′ _ Γ) (reversed-pf⁺ b₁))
                                (equal-asm-pf (unfold-reverse′ _ Γ) (reversed-pf⁺ b₂)))

true≡false⊥ : true ≡ false → ⊥
true≡false⊥ ()

length≡0 : {A : Set} {ℓ : List A} → length ℓ ≡ 0 → ℓ ≡ []
length≡0 {ℓ = []} refl = refl

drop-[] : {A : Set} {ℓ : List A} {n : ℕ} → ℓ ≡ [] → drop n ℓ ≡ []
drop-[] {n = ℕ.zero} refl = refl
drop-[] {n = ℕ.suc n} refl = refl

drop-suc : {A : Set} (x : A) (ℓ : List A) (n : ℕ) → drop (ℕ.suc n) (x ∷ ℓ) ≡ drop n ℓ
drop-suc x ℓ ℕ.zero = refl
drop-suc x ℓ (ℕ.suc n) = refl

drop-suc₁ : {A : Set} (x : A) (ℓ ℓ₁ : List A) (n : ℕ) → drop n ℓ ≡ (x ∷ ℓ₁) → drop (ℕ.suc n) ℓ ≡ ℓ₁
drop-suc₁ x .(x ∷ ℓ₁) ℓ₁ ℕ.zero refl = refl
drop-suc₁ x (y ∷ []) ℓ₁ (ℕ.suc ℕ.zero) ()
drop-suc₁ x (y ∷ []) ℓ₁ (ℕ.suc (ℕ.suc n)) ()
drop-suc₁ x (y ∷ y₁ ∷ ℓ) ℓ₁ (ℕ.suc n) eq = drop-suc₁ _ _ ℓ₁ n eq

drop-suc-[] : {A : Set} (ℓ : List A) (n : ℕ) → drop n ℓ ≡ [] → drop (ℕ.suc n) ℓ ≡ []
drop-suc-[] .[] ℕ.zero refl = refl
drop-suc-[] [] (ℕ.suc n) eq = refl
drop-suc-[] (x ∷ ℓ) (ℕ.suc n) eq = drop-suc-[] ℓ n eq

under-taut : {b : Stmt} → (f : Fin (vars-of b) → Bool) → FinRelTautology [] b → under (assign′ f) b ≡ b
under-taut {b} f taut with taut f refl | assign′ f b | inspect (assign′ f) b
under-taut {b} f taut | eq | false | [ eq₁ ] = ⊥-elim (true≡false⊥ (trans (sym eq) eq₁))
under-taut {b} f taut | eq | true | [ eq₁ ] = refl

⊔0₁ : {a b : ℕ} → a ℕ.⊔ b ≡ 0 → a ≡ 0
⊔0₁ {ℕ.zero} {b} refl = refl
⊔0₁ {ℕ.suc a} {ℕ.zero} ()
⊔0₁ {ℕ.suc a} {ℕ.suc b} ()

⊔0₂ : {a b : ℕ} → a ℕ.⊔ b ≡ 0 → b ≡ 0
⊔0₂ {ℕ.zero} {ℕ.zero} refl = refl
⊔0₂ {ℕ.suc a} {ℕ.zero} ()
⊔0₂ {ℕ.suc a} {ℕ.suc b} ()

under-tautology : {b : Stmt} → (f : Fin (vars-of b) → Bool) → FinRelTautology [] b → under (assign′ f) b ≡ b
under-tautology {b} f finrel with finrel f refl | assign′ f b | inspect (assign′ f) b | inspect (under (assign′ f)) b
... | eq | false | [ eq₁ ] | [ eq₂ ] = ⊥-elim (true≡false⊥ (trans (sym eq) eq₁))
... | eq | true | [ eq₁ ] | [ eq₂ ] = refl

vars-of≢0 : {b : Stmt} → vars-of b ≡ 0 → ⊥
vars-of≢0 {b ⇒ b₁} eq = vars-of≢0 {b} (⊔0₁ eq)
vars-of≢0 {¬ b} eq = vars-of≢0 {b} eq

next₀ : {n : ℕ} → Bool → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
next₀ {n} b f i with n ℕ.≟ Fin.toℕ i
next₀ {n} b f i | yes _ = b
next₀ {n} b f i | no ¬pf = f (Fin.lower₁ i ¬pf)

nextᵗ : {n : ℕ} → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
nextᵗ = next₀ true

nextᶠ : {n : ℕ} → (Fin n → Bool) → (Fin (ℕ.suc n) → Bool)
nextᶠ = next₀ false

extend-fins : (n : ℕ) → map Fin.toℕ (all-fin {n}) ∷ʳ n ≡ map Fin.toℕ (all-fin {ℕ.suc n})
extend-fins ℕ.zero = refl
extend-fins (ℕ.suc n) =                                    begin
  map Fin.toℕ (all-fin {ℕ.suc n}) ∷ʳ ℕ.suc n              ≡⟨⟩
  (0 ∷ map Fin.toℕ (map Fin.suc (all-fin {n}))) ∷ʳ ℕ.suc n ≡⟨⟩
  0 ∷ (map Fin.toℕ (map Fin.suc (all-fin {n})) ∷ʳ ℕ.suc n) ≡˘⟨ cong (λ y → 0 ∷ (y ∷ʳ ℕ.suc n)) commute₁ ⟩
  0 ∷ (map ℕ.suc (map Fin.toℕ (all-fin {n})) ∷ʳ ℕ.suc n)   ≡˘⟨ cong (λ y → 0 ∷ y) (map-buildʳ _ _ _) ⟩
  0 ∷ (map ℕ.suc ((map Fin.toℕ (all-fin {n})) ∷ʳ n))       ≡⟨ cong (λ y → 0 ∷ (map ℕ.suc y)) (extend-fins n) ⟩
  0 ∷ (map ℕ.suc (map Fin.toℕ (all-fin {ℕ.suc n})))       ≡⟨ cong (λ y → 0 ∷ y) commute₂ ⟩
  0 ∷ map Fin.toℕ (map Fin.suc (all-fin {ℕ.suc n}))        ≡⟨⟩
  map Fin.toℕ (all-fin {ℕ.suc (ℕ.suc n)})                  ∎
 where commute₁ = map-commute Fin.suc Fin.toℕ Fin.toℕ ℕ.suc λ x₁ elt → toℕ-suc {m = x₁}
       commute₂ = map-commute Fin.suc Fin.toℕ Fin.toℕ ℕ.suc λ x₁ elt → toℕ-suc {m = x₁}

--trans (∷-∷ʳ 0 _ (ℕ.suc n)) (build-list≡ refl {!extend-fins n!})

toℕ≢ : {n : ℕ} (i : Fin n) → Fin.toℕ i ≢ n
toℕ≢ i = ℕProps.<⇒≢ (FinProps.toℕ<n i)

sym′ : {A : Set} {a b : A} → a ≢ b → b ≢ a
sym′ neq eq = ⊥-elim (neq (sym eq))

next-assign-lemma₀ : (n : ℕ) (f : Fin n → Bool) (b : Bool) (k : Fin (ℕ.suc n)) →
                     (pf : n ≢ Fin.toℕ k) →
                     f (Fin.lower₁ k pf) ≡ next₀ b f k
next-assign-lemma₀ n f b k ¬pf with n ℕ.≟ Fin.toℕ k
next-assign-lemma₀ n f b k ¬pf | yes pf₁ = ⊥-elim (¬pf pf₁)
next-assign-lemma₀ n f b k ¬pf | no ¬pf₁ = cong f (FinProps.lower₁-irrelevant _ _ _)

next-assign-lemma₁ : (n m : ℕ) (f : Fin n → Bool) (g : Fin m → Bool) (b : Stmt) →
                     assign′ f b ≡ assign′ g b →
                     under (assign′ f) b ≡ under (assign′ g) b
next-assign-lemma₁ n m f g b eq with assign′ f b | assign′ g b
next-assign-lemma₁ n m f g b refl | false | false = refl
next-assign-lemma₁ n m f g b refl | true | true = refl

extrapolate-lemma : (n : ℕ) (f : Fin n → Bool) (b : Bool) (k : Fin n) →
                    extrapolate-fin b f (Fin.toℕ k) ≡ f k
extrapolate-lemma ℕ.zero f b ()
extrapolate-lemma (ℕ.suc n) f b Fin.zero = refl
extrapolate-lemma (ℕ.suc n) f b (Fin.suc k) = extrapolate-lemma n (f ∘ Fin.suc) b k

next-lower-lemma : (n : ℕ) (f : Fin n → Bool) (b : Bool) (k : Fin (ℕ.suc n)) →
                   (n≢k : n ≢ Fin.toℕ k) →
                   f (Fin.lower₁ k n≢k) ≡ next₀ b f k
next-lower-lemma n f b k neq with n ℕ.≟ Fin.toℕ k
... | no ¬eq = cong f (FinProps.lower₁-irrelevant k neq ¬eq)
... | yes eq = ⊥-elim (neq eq)

next-assign-lemma₂ : (n : ℕ) (f : Fin n → Bool) (b : Bool) (k : Fin n) →
                     assign′ f (var (Fin.toℕ k)) ≡ assign′ (next₀ b f) (var (Fin.toℕ k))
next-assign-lemma₂ n f b k =                          begin
  assign′ f (var (Fin.toℕ k))                        ≡⟨⟩
  extrapolate-fin false f (Fin.toℕ k)                ≡⟨ extrapolate-lemma n f false k ⟩
  f k                                                ≡˘⟨ cong f (FinProps.lower₁-inject₁ k) ⟩
  f (Fin.lower₁ (Fin.inject₁ k) inj≢)                ≡⟨ next-lower-lemma n f b (Fin.inject₁ k) inj≢ ⟩
  f′ (Fin.inject₁ k)                                 ≡˘⟨ extrapolate-lemma (ℕ.suc n) f′ false (Fin.inject₁ k) ⟩
  extrapolate-fin false f′ (Fin.toℕ (Fin.inject₁ k)) ≡⟨ cong (extrapolate-fin false f′) (FinProps.toℕ-inject₁ k) ⟩
  extrapolate-fin false f′ (Fin.toℕ k)               ≡⟨⟩
  assign′ f′ (var (Fin.toℕ k))                       ∎
 where f′ = next₀ b f
       inj≢ = FinProps.toℕ-inject₁-≢ k

next-assign-lemma : (n : ℕ) (f : Fin n → Bool) (b : Bool) (k : Fin n) →
                    under-var (assign′ f) (Fin.toℕ k) ≡ under-var (assign′ (next₀ b f)) (Fin.toℕ k)
next-assign-lemma n f b k =             begin
  under-var (assign′ f) (Fin.toℕ k)    ≡⟨⟩
  under (assign′ f) (var (Fin.toℕ k))  ≡⟨ next-assign-lemma₁ n (ℕ.suc n) f f′ (var (Fin.toℕ k))
                                                             (next-assign-lemma₂ n f b k) ⟩
  under (assign′ f′) (var (Fin.toℕ k)) ≡⟨⟩
  under-var (assign′ f′) (Fin.toℕ k)   ∎
 where f′ = next₀ b f

all-lemma₁ : (n : ℕ) (f : Fin n → Bool) (b : Bool) →
             All (λ x₁ → under-var (assign′ (next₀ b f)) x₁ ≡ under-var (assign′ f) x₁) (map Fin.toℕ (all-fin {n}))
all-lemma₁ n f b = AllProps.map⁺ (All.tabulate λ {y} _ →
                                                 next-assign-lemma₁ (ℕ.suc n) n f′ f (var (Fin.toℕ y))
                                                                    (sym (next-assign-lemma₂ n f b y)))
 where f′ = next₀ b f

snoc-extend : {n : ℕ} (f : Fin n → Bool) (x : Bool) →
              to-assumptions (next₀ x f) ≡ to-assumptions f ∷ʳ under-var (assign′ (next₀ x f)) n
snoc-extend {n} f x =                                           begin
  to-assumptions f′                                             ≡⟨⟩
  map (under-var (assign′ f′)) fins′                            ≡˘⟨ cong m (extend-fins n) ⟩
  map (under-var (assign′ f′)) (fins ∷ʳ n)                      ≡⟨ map-buildʳ n fins (under-var (assign′ f′)) ⟩
  map (under-var (assign′ f′)) fins ∷ʳ under-var (assign′ f′) n ≡⟨ cong (λ y → y ∷ʳ under-var (assign′ f′) n)
                                                                        (ListProps.map-cong₂ (all-lemma₁ n f x)) ⟩
  map (under-var (assign′ f)) fins ∷ʳ under-var (assign′ f′) n  ≡⟨⟩
  to-assumptions f ∷ʳ under-var (assign′ f′) n                  ∎
 where fins  = map Fin.toℕ (all-fin {n})
       fins′ = map Fin.toℕ (all-fin {ℕ.suc n})
       f′ = next₀ x f
       m = map (under-var (assign′ (next₀ x f)))

under-lemma₀′ : {n : ℕ} (f : Fin n → Bool) (b : Bool) → next₀ b f (Fin.fromℕ n) ≡ b
under-lemma₀′ {n} f b with n ℕ.≟ Fin.toℕ (Fin.fromℕ n)
under-lemma₀′ {n} f b | no ¬proof = ⊥-elim (¬proof (sym (FinProps.toℕ-fromℕ n)))
under-lemma₀′ {n} f b | yes proof = refl

under-lemma₀ : {n : ℕ} (f : Fin n → Bool) (b : Bool) → assign′ (next₀ b f) (var n) ≡ b
under-lemma₀ {n} f b =                                       begin
  assign′ (next₀ b f) (var n)                                ≡⟨⟩
  assign (extrapolate-fin false (next₀ b f)) (var n)         ≡⟨⟩
  extrapolate-fin false (next₀ b f) n                        ≡⟨ cong (extrapolate-fin false (next₀ b f))
                                                                     (sym (FinProps.toℕ-fromℕ n)) ⟩
  extrapolate-fin false (next₀ b f) (Fin.toℕ (Fin.fromℕ n)) ≡⟨ extrapolate-lemma (ℕ.suc n) (next₀ b f) false
                                                                                 (Fin.fromℕ n) ⟩
  next₀ b f (Fin.fromℕ n)                                   ≡⟨ under-lemma₀′ f b ⟩
  b                                                          ∎

next-lemma : {n : ℕ} (f : Fin n → Bool) (b : Bool) (k : Fin (ℕ.suc n)) → (n ≡ Fin.toℕ k) →
             next₀ b f k ≡ b
next-lemma {n} f b k eq with n ℕ.≟ Fin.toℕ k
... | no ¬pf = ⊥-elim (¬pf eq)
... | yes pf = refl

under-var-lemmaᶠ′ : {n : ℕ} (f : Fin (ℕ.suc n) → Bool) →
                    assign′ f (var n) ≡ false → under-var (assign′ f) n ≡ ¬ var n
under-var-lemmaᶠ′ {n} f eq with assign′ f (var n)
under-var-lemmaᶠ′ {n} f refl | false = refl

under-var-lemmaᶠ : {n : ℕ} (f : Fin n → Bool) → under-var (assign′ (next₀ false f)) n ≡ ¬ var n
under-var-lemmaᶠ {n} f = under-var-lemmaᶠ′ (next₀ false f) (under-lemma₀ f false)

under-var-lemmaᵗ′ : {n : ℕ} (f : Fin (ℕ.suc n) → Bool) →
                    assign′ f (var n) ≡ true → under-var (assign′ f) n ≡ var n
under-var-lemmaᵗ′ {n} f eq with assign′ f (var n)
under-var-lemmaᵗ′ {n} f refl | true = refl

under-var-lemmaᵗ : {n : ℕ} (f : Fin n → Bool) → under-var (assign′ (next₀ true f)) n ≡ var n
under-var-lemmaᵗ {n} f = under-var-lemmaᵗ′ (next₀ true f) (under-lemma₀ f true)

-- /////
snoc-extend′ : {n : ℕ} (f : Fin n → Bool) (x : Bool) →
               to-assumptions (next₀ x f) ≡ to-assumptions f ∷ʳ (if x then var n else ¬ var n)
snoc-extend′ {n} f false =                                  begin
  to-assumptions (next₀ false f)                            ≡⟨ snoc-extend f false ⟩
  to-assumptions f ∷ʳ under-var (assign′ (next₀ false f)) n ≡⟨ cong (λ y → to-assumptions f ∷ʳ y)
                                                                    (under-var-lemmaᶠ f) ⟩
  to-assumptions f ∷ʳ ¬ var n                               ∎
snoc-extend′ {n} f true =                                   begin
  to-assumptions (next₀ true f)                             ≡⟨ snoc-extend f true ⟩
  to-assumptions f ∷ʳ under-var (assign′ (next₀ true f)) n  ≡⟨ cong (λ y → to-assumptions f ∷ʳ y)
                                                                    (under-var-lemmaᵗ f) ⟩
  to-assumptions f ∷ʳ var n                                 ∎

without-next-asm : (b : Stmt) (n : ℕ) (f : Fin n → Bool) →
                   to-assumptions (nextᵗ f) ⊢ b →
                   to-assumptions (nextᶠ f) ⊢ b →
                   to-assumptions f ⊢ b
without-next-asm b n f caseᵗ caseᶠ =
  common-asm-elimʳ (equal-asm-pf (snoc-extend′ f true) caseᵗ) (equal-asm-pf (snoc-extend′ f false) caseᶠ)

-- I have four very similar versions of this lemma because I'm trying
-- to make the termination checker happy.

ℕ-eq-lemma₁ : (k n : ℕ) → ∃[ m ] (ℕ.suc (k ∸ n) ≡ ℕ.suc k ∸ m)
ℕ-eq-lemma₁ k ℕ.zero = 0 , refl
ℕ-eq-lemma₁ ℕ.zero (ℕ.suc n) = 0 , refl
ℕ-eq-lemma₁ (ℕ.suc k) (ℕ.suc n) =
  let m , eq = ℕ-eq-lemma₁ k n in
  ℕ.suc m , eq

ℕ-eq-lemma₂ : (k n : ℕ) → (ℕ.suc (k ∸ n) ≡ ℕ.suc k ∸ (k ℕ.⊓ n))
ℕ-eq-lemma₂ k ℕ.zero = cong (λ y → ℕ.suc k ∸ y) (sym (ℕProps.⊓-zeroʳ k))
ℕ-eq-lemma₂ ℕ.zero (ℕ.suc n) = refl
ℕ-eq-lemma₂ (ℕ.suc k) (ℕ.suc n) = ℕ-eq-lemma₂ k n

ℕ-eq-lemma₃ : (k n : ℕ) → (ℕ.suc (k ∸ n) ≡ ℕ.suc k ∸ k) ⊎ (ℕ.suc (k ∸ n) ≡ ℕ.suc k ∸ n)
ℕ-eq-lemma₃ k ℕ.zero = inj₂ refl
ℕ-eq-lemma₃ ℕ.zero (ℕ.suc n) = inj₁ refl
ℕ-eq-lemma₃ (ℕ.suc k) (ℕ.suc n) = ℕ-eq-lemma₃ k n

ℕ-eq-lemma₄ : (k n : ℕ) → (n ℕ.> k) ⊎ (ℕ.suc (k ∸ n) ≡ ℕ.suc k ∸ n)
ℕ-eq-lemma₄ k ℕ.zero = inj₂ refl
ℕ-eq-lemma₄ ℕ.zero (ℕ.suc n) = inj₁ (ℕ.s≤s ℕ.z≤n)
ℕ-eq-lemma₄ (ℕ.suc k) (ℕ.suc n) with ℕ-eq-lemma₄ k n
ℕ-eq-lemma₄ (ℕ.suc k) (ℕ.suc n) | inj₁ lt = inj₁ (ℕ.s≤s lt)
ℕ-eq-lemma₄ (ℕ.suc k) (ℕ.suc n) | inj₂ eq = inj₂ eq

eq-fin-lemma : {n m : ℕ} → n ≡ m → (Fin n → Bool) → (Fin m → Bool)
eq-fin-lemma refl f = f

asm-lemma : {n m : ℕ} (f : Fin n → Bool) (eq : n ≡ m) → to-assumptions (eq-fin-lemma eq f) ≡ to-assumptions f
asm-lemma f refl = refl

finrel-lemma : {n m : ℕ} (Γ : List Stmt) (b : Stmt) → n ≡ m → FinRelTautologyOn n Γ b → FinRelTautologyOn m Γ b
finrel-lemma Γ b refl finrel = finrel

∸lemma : {k n : ℕ} → k ℕ.< n → k ∸ n ≡ ℕ.suc k ∸ n
∸lemma {ℕ.zero} {ℕ.suc n} (ℕ.s≤s lt) = sym (ℕProps.0∸n≡0 n)
∸lemma {ℕ.suc k} {ℕ.suc n} (ℕ.s≤s lt) = ∸lemma lt

without-some-asm : (b : Stmt) (n : ℕ) (f : Fin (vars-of b ∸ n) → Bool) →
                   FinRelTautology [] b →
                   to-assumptions f ⊢ b
without-some-asm b ℕ.zero f finrel =
   equal-value-pf (under-tautology {b} f finrel) (assigned-asm-lemma′ {b} f)
without-some-asm b (ℕ.suc n) f finrel with vars-of b | inspect vars-of b
without-some-asm b (ℕ.suc n) f finrel | ℕ.zero | [ eq ] = ⊥-elim (vars-of≢0 {b} eq)
without-some-asm b (ℕ.suc n) f finrel | ℕ.suc k | [ eq ] =
  case ℕ-eq-lemma₄ k n of λ
  { (inj₁ g) →
      -- This case is actually trivial. We're removing more
      -- assumptions than we have, so we can safely remove one fewer
      -- and get the same result.
      let finrel′ = finrel-lemma [] b (sym eq) finrel in
      let eq₁ : ℕ.suc k ∸ ℕ.suc n ≡ vars-of b ∸ n
          eq₁ = trans (∸lemma g) (cong (λ y → y ∸ n) (sym eq)) in
      equal-asm-pf (asm-lemma f eq₁) (without-some-asm b n (eq-fin-lemma eq₁ f) finrel′)
  ; (inj₂ eq₁) →
      let eq₂ : ℕ.suc (k ∸ n) ≡ vars-of b ∸ n
          eq₂ = trans eq₁ (cong (λ y → y ∸ n) (sym eq)) in
      let finrel′ = finrel-lemma [] b (sym eq) finrel in
      without-next-asm b (k ∸ n) f
                         (equal-asm-pf (asm-lemma (nextᵗ f) eq₂)
                                       (without-some-asm b n (eq-fin-lemma eq₂ (nextᵗ f)) finrel′))
                         (equal-asm-pf (asm-lemma (nextᶠ f) eq₂)
                                       (without-some-asm b n (eq-fin-lemma eq₂ (nextᶠ f)) finrel′))
  }

completeness : (b : Stmt) → FinRelTautology [] b → ⊢ b
completeness b finrel = +asm asm-helper (without-some-asm b (vars-of b) f finrel)
  where f₀ : Fin 0 → Bool
        f₀ ()
        f : Fin (vars-of b ∸ vars-of b) → Bool
        f = eq-fin-lemma (sym (ℕProps.n∸n≡0 (vars-of b))) f₀
        asm-helper : {Γ : List Stmt} → to-assumptions f ⊆ Γ
        asm-helper elt with ∈≡ (asm-lemma f₀ (sym (ℕProps.n∸n≡0 (vars-of b)))) elt
        asm-helper elt | ()
