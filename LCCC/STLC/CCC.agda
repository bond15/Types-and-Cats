module CCC where
open import Data.Nat renaming (β to Nat) hiding (_*_)
open import Data.Bool
open import Data.Unit renaming (β€ to Unit)
open import Data.Product

data type : Set where
    π β πΉ : type 
    _β_ _*_ : type β type β type
    
β¦_β¦ : type β Set 
β¦ π β¦ = Unit
β¦ β β¦ = Nat
β¦ πΉ β¦ = Bool
β¦ x β y β¦ = β¦ x β¦ β β¦ y β¦
β¦ x * y β¦ = β¦ x β¦ Γ β¦ y β¦


module Phoas (El : type β Set) where 

    data term  : type β Set where 
        var : {t : type} β (El t β term t)
        -- β-Elim
        _β_ : {dom ran : type} β term (dom β ran) β term dom β term ran
        -- β-Intro
        Ξ : {dom ran : type} β (El dom β term ran) β term (dom β ran)
        -- *- Intro
        β¨_,_β© : {A B : type} β term A β term B β term (A * B)
        -- *-Elimβ
        Οβ : {A B : type} β term (A * B) β term A
        -- *-Elimβ
        Οβ : {A B : type} β term (A * B) β term B

    {-}
    _βΉ_ : term β β term β β term β 
    var x βΉ y = {!   !}
    (x β xβ) βΉ y = {!   !}
    Οβ x βΉ y = {!   !}
    Οβ x βΉ y = {!   !}
    -}

open Phoas β¦_β¦

open import CatLib
open import Level
open Category renaming (_β_ to Hom )
open import Cubical.Core.Everything using (_β‘_)
open import Cubical.Foundations.Prelude using (refl)

STLC-Cat : Category Level.zero Level.zero 
STLC-Cat .Ob = type
STLC-Cat .Hom x y = β¦ x β y β¦
STLC-Cat .id = Ξ» x β x
STLC-Cat ._β_ = Ξ» g f x β g(f(x))
STLC-Cat .idr = refl
STLC-Cat .idl = refl
STLC-Cat .assoc = refl

open Terminal STLC-Cat
open TerminalT
open IsTerminal

STLC-Term : TerminalT
STLC-Term .β€ = π
STLC-Term .β€-is-terminal = record { ! = Ξ» x β tt; !-unique = Ξ» f i x β tt }

open BinaryProducts STLC-Cat
open BinaryProductsT
STLC-Prod : BinaryProductsT 
STLC-Prod .product = prod
    where 
        open ObjectProduct STLC-Cat
        open Product renaming (Οβ to projβ; Οβ to projβ ; β¨_,_β© to [_,_])
        prod : {A B : type} β Product A B
        prod {A} {B} .AΓB = A * B
        prod .projβ (fst , snd) = fst
        prod .projβ (fst , snd) = snd
        prod .[_,_] = <_,_>
        prod .projectβ = refl
        prod .projectβ = refl
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
        exp .B^A = A β B
        exp .product = prod
        exp .eval (f , a) = f a
        exp .Ξ»g = {!   !}


open CartesianClosed STLC-Cat
open CartesianClosedT
STLC-CC : CartesianClosedT 
STLC-CC .terminal = STLC-Term
STLC-CC .products = STLC-Prod
STLC-CC .exponentials = STLC-Exp
