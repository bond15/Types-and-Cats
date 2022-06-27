module mltt where 
--https://arxiv.org/pdf/1904.00827.pdf

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)

{-
1/29/22
Martin-Lof substitution calculus

usual judgement forms
    Γ ⊢ A type
    Γ ⊢ A = A'
    Γ ⊢ a : A 
    Γ ⊢ a = a' : A


subsitution calculus, additional judgement forms
    Γ context
    Γ = Γ'
    Δ → γ : Γ 
    Δ → γ = γ' : Γ

Given Γ = x₁ : A₁,.., xₙ : A ₙ, 
    "Δ → γ : Γ" means
        γ is a substitution (free variables -> terms)
            x₁ = a₁,..., xₙ = aₙ
    
        a₁ : A₁,..,aₙ : A­ₙ are in Δ


"2.1.2 Inference rules
The inference rules of intuitionistic type theory can be separated into two
kinds. The first kind are the general rules, the most basic rules for reason-
ing with dependent types. They deal with substitution, context formation,
assumption, and general equality reasoning. They form the backbone of the
dependently typed structure, and carry no information yet about specific
term and type formers. The second kind consists of the rules for type form-
ers, such as Π, Σ, and identity types. These rules are divided into formation,
introduction, elimination, and equality rules (also called computation rules).
Categories with families capture models of the first kind of rules: the back-
bone of Martin-L ̈of type theory which is independent of type and term con-
structors."


2.2.1 Definition
The definition uses the category Fam of families of sets. Its objects are fami-
lies (Ux)x∈X . A morphism with source (Ux)x∈X and target (Vy )y∈Y is a pair
consisting of a reindexing function f : X → Y , and a family (gx)x∈X where
for each x ∈ X, gx : Ux → Vf (x) is a function

^ so this is Poly but using `Charts` instead of `Lenses` for morphisms?
https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=10
-}
open import Data.Product
-- 
module Fam where 
    Ob : Set → Set₁
    Ob X = (x : X) → Set

    record Morph {X Y : Set}(ox : Ob X)(oy : Ob Y) : Set where 
        field 
            pos : X → Y 
            dir : ∀(x : X) → ox x → oy (pos x)

module CatTerm where
    REL : Set -> Set -> Set₁ 
    REL A B = A -> B -> Set 

    Rel : Set -> Set₁ 
    Rel A = REL A A 

    -- Precategory (need to parameterize with equality)
    record CategoryWTerm : Set₁ where
        field
            Ob : Set 
            _⇒_ : Rel Ob
            --_≋_ : ∀{A B : Ob} → Rel (A ⇒ B) 
            _∘_  : ∀ {x y z : Ob} -> y ⇒ z -> x ⇒ y -> x ⇒ z
            id : ∀ {o : Ob} -> o ⇒ o
            ⊤ : Ob 
            ⊤-map : ∀{ob : Ob} → ob ⇒ ⊤
            {- idˡ : ∀ {x y : Ob} (f : x ⇒ y) -> f ∘ (id {x}) ≡ f
            idʳ : ∀ {x y : Ob} (f : x ⇒ y) -> (id {y}) ∘ f ≡ f
            ∘-assoc : ∀ {x y z w : Ob} (f : x ⇒ y) (g : y ⇒ z) (h : z ⇒ w) -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f 
            -- prf ⊤ is terminal
            -}



module CwF where
    open CatTerm
    open CategoryWTerm renaming (Ob to Obc)
    postulate C : CategoryWTerm
    postulate Γ Δ : C .Obc
    postulate γ δ : (_⇒_ C) Δ Γ
    postulate op : CategoryWTerm → CategoryWTerm
    

 