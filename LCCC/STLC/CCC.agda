module CCC where
open import Data.Nat renaming (ℕ to Nat) hiding (_*_)
open import Data.Bool
open import Data.Unit renaming (⊤ to Unit)
open import Data.Product

data type : Set where
    𝕌 ℕ 𝔹 : type 
    _⇒_ _*_ : type → type → type
    
⦅_⦆ : type → Set 
⦅ 𝕌 ⦆ = Unit
⦅ ℕ ⦆ = Nat
⦅ 𝔹 ⦆ = Bool
⦅ x ⇒ y ⦆ = ⦅ x ⦆ → ⦅ y ⦆
⦅ x * y ⦆ = ⦅ x ⦆ × ⦅ y ⦆


module Phoas (El : type → Set) where 

    data term  : type → Set where 
        var : {t : type} → (El t → term t)
        -- ⇒-Elim
        _∙_ : {dom ran : type} → term (dom ⇒ ran) → term dom → term ran
        -- ⇒-Intro
        Λ : {dom ran : type} → (El dom → term ran) → term (dom ⇒ ran)
        -- *- Intro
        ⟨_,_⟩ : {A B : type} → term A → term B → term (A * B)
        -- *-Elim₁
        π₁ : {A B : type} → term (A * B) → term A
        -- *-Elim₂
        π₂ : {A B : type} → term (A * B) → term B

    {-}
    _⊹_ : term ℕ → term ℕ → term ℕ 
    var x ⊹ y = {!   !}
    (x ∙ x₁) ⊹ y = {!   !}
    π₁ x ⊹ y = {!   !}
    π₂ x ⊹ y = {!   !}
    -}

open Phoas ⦅_⦆

open import CatLib
open import Level
open Category renaming (_⇒_ to Hom )
open import Cubical.Core.Everything using (_≡_)
open import Cubical.Foundations.Prelude using (refl)

STLC-Cat : Category Level.zero Level.zero 
STLC-Cat .Ob = type
STLC-Cat .Hom x y = ⦅ x ⇒ y ⦆
STLC-Cat .id = λ x → x
STLC-Cat ._∘_ = λ g f x → g(f(x))
STLC-Cat .idr = refl
STLC-Cat .idl = refl
STLC-Cat .assoc = refl

open Terminal STLC-Cat
open TerminalT
open IsTerminal

STLC-Term : TerminalT
STLC-Term .⊤ = 𝕌
STLC-Term .⊤-is-terminal = record { ! = λ x → tt; !-unique = λ f i x → tt }

open BinaryProducts STLC-Cat
open BinaryProductsT
STLC-Prod : BinaryProductsT 
STLC-Prod .product = prod
    where 
        open ObjectProduct STLC-Cat
        open Product renaming (π₁ to proj₁; π₂ to proj₂ ; ⟨_,_⟩ to [_,_])
        prod : {A B : type} → Product A B
        prod {A} {B} .A×B = A * B
        prod .proj₁ (fst , snd) = fst
        prod .proj₂ (fst , snd) = snd
        prod .[_,_] = <_,_>
        prod .project₁ = refl
        prod .project₂ = refl
        prod .unique p q = {!   !}

open Exponentials STLC-Cat
open ExponentialsT
STLC-Exp : ExponentialsT
STLC-Exp .exponential {A} {B} = exp
    where 
        open ObjectExponential STLC-Cat
        open ExponentialOb
        open BinaryProductsT STLC-Prod renaming (product to prod)

        exp : ExponentialOb A B
        exp .B^A = A ⇒ B
        exp .product = prod
        exp .eval (f , a) = f a
        exp .λg = {!   !}


open CartesianClosed STLC-Cat
open CartesianClosedT
STLC-CC : CartesianClosedT 
STLC-CC .terminal = STLC-Term
STLC-CC .products = STLC-Prod
STLC-CC .exponentials = STLC-Exp
