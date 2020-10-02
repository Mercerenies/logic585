
module Logic585.PropCalc.Stmt.Order where

open import Logic585.PropCalc.Stmt

open import Level
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕProps
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

-- An arbitrary total order on Stmt, so I can use them as keys in AVL
-- trees.

infix 4 _<_

data _<_ : Stmt → Stmt → Set where
  var<⇒ : {n : ℕ} {a b : Stmt} → var n < a ⇒ b
  var<¬ : {n : ℕ} {a : Stmt} → var n < ¬ a
  ⇒<¬ : {a b c : Stmt} → a ⇒ b < ¬ c
  var<var : {n m : ℕ} → n ℕ.< m → var n < var m
  ⇒<⇒₁ : {a b a′ b′ : Stmt} → a < a′ → a ⇒ b < a′ ⇒ b′
  ⇒<⇒₂ : {a b a′ b′ : Stmt} → a ≡ a′ → b < b′ → a ⇒ b < a ⇒ b′
  ¬<¬ : {a a′ : Stmt} → a < a′ → ¬ a < ¬ a′

<-trans : Transitive _<_
<-trans var<⇒ ⇒<¬ = var<¬
<-trans var<⇒ (⇒<⇒₁ _) = var<⇒
<-trans var<⇒ (⇒<⇒₂ _ _) = var<⇒
<-trans var<¬ (¬<¬ _) = var<¬
<-trans ⇒<¬ (¬<¬ _) = ⇒<¬
<-trans (var<var _) var<⇒ = var<⇒
<-trans (var<var _) var<¬ = var<¬
<-trans (var<var n<m) (var<var m<k) = var<var (ℕProps.<-trans n<m m<k)
<-trans (⇒<⇒₁ _) ⇒<¬ = ⇒<¬
<-trans (⇒<⇒₁ a<b) (⇒<⇒₁ b<c) = ⇒<⇒₁ (<-trans a<b b<c)
<-trans (⇒<⇒₁ a<b) (⇒<⇒₂ refl _) = ⇒<⇒₁ a<b
<-trans (⇒<⇒₂ refl _) ⇒<¬ = ⇒<¬
<-trans (⇒<⇒₂ refl _) (⇒<⇒₁ b<c) = ⇒<⇒₁ b<c
<-trans (⇒<⇒₂ refl a<b) (⇒<⇒₂ refl b<c) = ⇒<⇒₂ refl (<-trans a<b b<c)
<-trans (¬<¬ a<b) (¬<¬ b<c) = ¬<¬ (<-trans a<b b<c)

<-cmp : Trichotomous _≡_ _<_
<-cmp (var x) (var y) with ℕProps.<-cmp x y
<-cmp (var x) (var y) | tri< a ¬b ¬c = tri< (var<var a) (λ { refl → ¬b refl }) (λ { (var<var pf) → ¬c pf })
<-cmp (var x) (var .x) | tri≈ ¬a refl ¬c = tri≈ (λ { (var<var pf) → ¬a pf }) refl (λ { (var<var pf) → ¬c pf})
<-cmp (var x) (var y) | tri> ¬a ¬b c = tri> (λ { (var<var pf) → ¬a pf }) (λ { refl → ¬b refl }) (var<var c)
<-cmp (var x) (b ⇒ b₁) = tri< var<⇒ (λ ()) (λ ())
<-cmp (var x) (¬ b) = tri< var<¬ (λ ()) (λ ())
<-cmp (a ⇒ a₁) (var x) = tri> (λ ()) (λ ()) var<⇒
<-cmp (a ⇒ a₁) (b ⇒ b₁) with <-cmp a b
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri< a ¬b ¬c = tri< (⇒<⇒₁ a) (λ { refl → ¬b refl }) (λ { (⇒<⇒₁ pf) → ¬c pf
                                                                                 ; (⇒<⇒₂ refl _) → ¬b refl })
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri≈ ¬a refl ¬c with <-cmp a₁ b₁
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri≈ ¬a refl ¬c | tri< a₀ ¬b₀ ¬c₀ =
  tri< (⇒<⇒₂ refl a₀) (λ { refl → ¬b₀ refl }) (λ { (⇒<⇒₁ pf) → ¬a pf ; (⇒<⇒₂ refl pf) → ¬c₀ pf })
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri≈ ¬a refl ¬c | tri≈ ¬a₀ refl ¬c₀ =
  tri≈ (λ { (⇒<⇒₁ pf) → ¬c pf ; (⇒<⇒₂ refl pf) → ¬a₀ pf })
       refl
       (λ { (⇒<⇒₁ pf) → ¬a pf ; (⇒<⇒₂ refl pf) → ¬c₀ pf })
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri≈ ¬a refl ¬c | tri> ¬a₀ ¬b₀ c₀ =
  tri> (λ { (⇒<⇒₁ pf) → ¬c pf ; (⇒<⇒₂ refl pf) → ¬a₀ pf }) (λ { refl → ¬b₀ refl }) (⇒<⇒₂ refl c₀)
<-cmp (_ ⇒ a₁) (_ ⇒ b₁) | tri> ¬a ¬b c = tri> (λ { (⇒<⇒₁ pf) → ¬a pf
                                                 ; (⇒<⇒₂ refl _) → ¬b refl }) (λ { refl → ¬b refl }) (⇒<⇒₁ c)
<-cmp (a ⇒ a₁) (¬ b) = tri< ⇒<¬ (λ ()) (λ ())
<-cmp (¬ a) (var x) = tri> (λ ()) (λ ()) var<¬
<-cmp (¬ a) (b ⇒ b₁) = tri> (λ ()) (λ ()) ⇒<¬
<-cmp (¬ a) (¬ b) with <-cmp a b
<-cmp (¬ _) (¬ _) | tri< a ¬b ¬c = tri< (¬<¬ a) (λ { refl → ¬b refl }) (λ { (¬<¬ pf) → ¬c pf })
<-cmp (¬ _) (¬ _) | tri≈ ¬a refl ¬c = tri≈ (λ { (¬<¬ pf) → ¬a pf }) refl (λ { (¬<¬ pf) → ¬c pf })
<-cmp (¬ _) (¬ _) | tri> ¬a ¬b c = tri> (λ { (¬<¬ pf) → ¬a pf }) (λ { refl → ¬b refl }) (¬<¬ c)

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
IsStrictTotalOrder.isEquivalence <-isStrictTotalOrder = isEquivalence
IsStrictTotalOrder.trans <-isStrictTotalOrder = <-trans
IsStrictTotalOrder.compare <-isStrictTotalOrder = <-cmp

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
StrictTotalOrder.Carrier <-strictTotalOrder = _
StrictTotalOrder._≈_ <-strictTotalOrder = _
StrictTotalOrder._<_ <-strictTotalOrder = _
StrictTotalOrder.isStrictTotalOrder <-strictTotalOrder = <-isStrictTotalOrder
