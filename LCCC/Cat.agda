module Cat where
-- definitions taken from 1Lab

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Agda.Primitive using (Level ; lsuc ; _⊔_)

-- hlevels

record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
    constructor contr 
    field 
        centre : A 
        paths : (x : A) → centre ≡ x
open is-contr public

is-prop : ∀{ℓ} → Set ℓ → Set _ 
is-prop A = (x y : A) → x ≡ y  

is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
is-hlevel A 0 = is-contr A
is-hlevel A 1 = is-prop A
is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

is-set : ∀{ℓ} → Set ℓ → Set ℓ 
is-set A = is-hlevel A 2

is-groupoid : ∀{ℓ} → Set ℓ → Set ℓ 
is-groupoid A = is-hlevel A 3


module hlevelExamples where 
    data ⊤ : Set where 
        t : ⊤

    _ : is-contr ⊤
    _ = contr t λ{ t → refl}

    _ : is-prop ⊤
    _ = λ{ t t → refl}

    _ : is-set ⊤ -- how do you prove this?
    _ = λ{ t t x≡y₁ x≡y₂ → {! refl !}}

{-
    i0,j1          i1,j1


    i0,j0          i1, j0


    left wall is specified by i = 0, j varies
    right wall is specified by i = 1, j varies
    bottom is specified by j = 0 , i varies
-}

    eq-centre : {A : Set} → (C : is-contr A) → (x : A) → C .centre ≡ x
    eq-centre C x = C .paths x

    is-contr→is-prop : {A : Set} → is-contr A → is-prop A 
    is-contr→is-prop C x y i = hcomp (λ{ j → λ{ (i = i0) → eq-centre C x j
                                             ;  (i = i1) → eq-centre C y j}}) (C .centre) 
                                             -- show x ≡ y when you have that centre ≡ x , centre ≡ y , and centre ≡ centre, fill in the lid of the square

    is-prop→is-set : {A : Set} → is-prop A → is-set A 
    is-prop→is-set h x y p q i j = hcomp (λ k → λ{ (i = i0) → h x (p j) k 
                                                    ; (i = i1) → h x (q j) k 
                                                    ; (j = i0) → h x x k
                                                    ; (j = i1) → h x y k }) x 

module partial where 
    -- learn all of this https://1lab.dev/1Lab.Path.html#2069
    open import Cubical.Data.Bool using (Bool ; true ; false)
    -- uhm what?
    -- Partial : I → Type → SSet (proof irrelevent Set?)
    _ : (i : I) → Partial (~ i ∨ i) Bool 
    _ = λ i → λ{ (i = i0) → true
                ;(i = i1) → false }

    i1-is-true : (i : I) → Partial i Bool 
    i1-is-true i (i = i1) = true

    i0-is-true : (i : I) → Partial (~ i) Bool 
    i0-is-true i (i = i0) = true

    

record PreCat (o h : Level) : Set (lsuc (o ⊔ h)) where 
    field 
        Ob : Set o
        Hom : Ob → Ob → Set h
        Hom-set : (x y : Ob) → is-set (Hom x y) -- if p : x ≡ y, q : x ≡ y, then p ≡ q
        id : ∀ {x} → Hom x x
        _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

        idr : ∀{x y} → (f : Hom x y) → f ∘ id ≡ f 
        idl : ∀{x y} → (f : Hom x y) → id ∘ f ≡ f
        assoc : ∀{w x y z} → (f : Hom y z)(g : Hom x y)(h : Hom w x) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
    infixr 40 _∘_

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = (sym p) ∙ q

-- tools for reasoning about composition of "2 morphisms"/ commuting squares
module CompSqr {o ℓ} (C : PreCat o ℓ) where 
    open PreCat C

    private variable
        x y : Ob 
        f g h i a b c : Hom x y

    module _ (ab≡c : a ∘ b ≡ c) where 
        pulll : a ∘ (b ∘ f) ≡ c ∘ f
        pulll {f = f} = 
            (a ∘ (b ∘ f)) ≡⟨ assoc a b f ⟩ 
            ((a ∘ b) ∘ f ) ≡⟨ cong (_∘ f) ab≡c ⟩ 
            c ∘ f ∎

        pullr : (f ∘ a) ∘ b ≡ f ∘ c 
        pullr {f = f} = 
            ((f ∘ a) ∘ b) ≡˘⟨ assoc f a b ⟩ 
            ((f ∘ (a ∘ b)) ≡⟨ cong (f ∘_) ab≡c ⟩ 
            f ∘ c ∎)

    module _ (p :  f ∘ h ≡ g ∘ i) where
        extendl : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)
        extendl {b = b} = 
            (f ∘ (h ∘ b)) ≡⟨ assoc f h b ⟩ 
            ((f ∘ h) ∘ b) ≡⟨ cong (_∘ b) p ⟩ 
            (((g ∘ i) ∘ b) ≡˘⟨ assoc g i b ⟩ 
            (g ∘ (i ∘ b) ∎))

        extendr : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i 
        extendr {a = a} = 
            ((a ∘ f) ∘ h) ≡˘⟨ assoc a f h ⟩ 
            ((a ∘ (f ∘ h)) ≡⟨ cong (a ∘_) p ⟩ 
            (a ∘ (g ∘ i)) ≡⟨ assoc a g i ⟩ 
            (a ∘ g) ∘ i ∎)




record Functor {o₁ h₁ o₂ h₂} (C : PreCat o₁ h₁) (D : PreCat o₂ h₂) : Set (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where 
    no-eta-equality 
    private 
        module C = PreCat C 
        module D = PreCat D
    field
        F₀ : C.Ob → D.Ob 
        F₁ : ∀{x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)

        F-id : ∀{x} → F₁ (C.id {x}) ≡ D.id
        F-∘ : ∀{x y z} → (f : C.Hom y z)(g : C.Hom x y ) → F₁ (f C.∘ g) ≡ (F₁ f) D.∘ (F₁ g)

record _⇒_ {o₁ h₁ o₂ h₂} {C : PreCat o₁ h₁}{D : PreCat o₂ h₂}(F G : Functor C D) : Set (o₁ ⊔ h₁ ⊔ h₂) where 
    no-eta-equality
    constructor NT 
    private 
        open Functor F 
        open Functor G renaming (F₀ to G₀ ; F₁ to G₁)
        module D = PreCat D 
        module C = PreCat C 
    field 
        η : (x : C.Ob) → D.Hom (F₀ x) (G₀ x)
        is-natural : (x y : C.Ob) (f : C.Hom x y) → (η y) D.∘ (F₁ f) ≡ (G₁ f) D.∘ (η x)


_F∘_ : {o₁ h₁ o₂ h₂ o₃ h₃ : Level} → {B : PreCat o₁ h₁}{C : PreCat o₂ h₂}{D : PreCat o₃ h₃}
    → Functor C D → Functor B C → Functor B D 
_F∘_ {B = B} {C} {D} F G = comps -- note usage of {B = B} here starts the implicit arguments at B 
                                 -- instead of o₁
    where 
        module B = PreCat B
        module C = PreCat C 
        module D = PreCat D 

        open Functor F 
        open Functor G renaming (F₀ to G₀ ; F₁ to G₁ ; F-id to G-id ; F-∘ to G-∘ )

        comp₀ : B.Ob → D.Ob 
        comp₀ x = F₀ (G₀ x)

        comp₁ : {x y : B.Ob} → B.Hom x y → D.Hom (comp₀ x) (comp₀ y)
        comp₁ f = F₁ (G₁ f)
        
        abstract -- makes the definition like a postulate? doesn't unfold in type checking?
            comp-id : {x : B.Ob} → comp₁ (B.id {x}) ≡ D.id {comp₀ x}
            comp-id {x} = 
                F₁ (G₁ B.id) ≡⟨ cong F₁ (G-id) ⟩ 
                F₁ C.id ≡⟨ F-id ⟩ 
                D.id ∎

            comp-∘ : {x y z : B.Ob} → (f : B.Hom y z) → (g : B.Hom x y) → 
                comp₁ (f B.∘ g) ≡ (comp₁ f D.∘ comp₁ g)
            comp-∘ f g = F₁ (G₁ (f B.∘ g))       ≡⟨ cong F₁ (G-∘ f g) ⟩ 
                         F₁ ((G₁ f) C.∘ G₁ g )   ≡⟨ F-∘ (G₁ f) (G₁ g)  ⟩  
                         F₁ (G₁ f) D.∘ F₁ (G₁ g) ∎

        comps : Functor B D 
        comps .Functor.F₀ = comp₀
        comps .Functor.F₁ = comp₁
        comps .Functor.F-id = comp-id
        comps .Functor.F-∘ = comp-∘

adj-level : ∀ {o₁ h₁ o₂ h₂} (C : PreCat o₁ h₁) (D : PreCat o₂ h₂) → Level
adj-level {o₁ = o₁} {h₁} {o₂} {h₂} _ _ = o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂

Id : {o₁ h₁ : Level} → {Cat : PreCat o₁ h₁} → Functor Cat Cat  
Id = record { F₀ = λ x → x ; F₁ = λ x → x ; F-id = refl ; F-∘ = λ f g → refl}

record _⊣_ {o₁ h₁ o₂ h₂}{C : PreCat o₁ h₁}{D : PreCat o₂ h₂}
            (L : Functor C D )(R : Functor D C) : Type (adj-level C D) where 
    private
        module C = PreCat C 
        module D = PreCat D
        open Functor L renaming (F₀ to L₀ ; F₁ to L₁)
        open Functor R renaming (F₀ to R₀ ; F₁ to R₁)
    field 
        unit : Id {Cat = C} ⇒ (R F∘ L)  
        counit : (L F∘ R) ⇒ Id {Cat = D} 
    {-
        unit : 

            note that  Id {C}   : Functor C C
            and 
                       (R F∘ L) : Functor C C    
            
            unit is a natural transformation from Id {C} to (R F∘ L)
            thus there is an η where 
                η : (x : C.Ob) → (C.Hom (Id₀ x) ((R F∘ L) x))
                or 
                    (x : C.Ob) → (C.Hom x ((R F∘ L) x))

        likewise

        counit :
            note that Id {D} : Functor D D 
            and 
                    (L F∘ R) : Functor D D 
    
            counit is a natrual transformation from (L F∘ R) to Id {D}
            thus ther is an η where 
                ε : (x : D.Ob) → (D.Hom ((L F∘ R) x) x)
    
        unit and counit must obey these laws
    -}
    module unit = _⇒_ unit
    open unit  
    module counit = _⇒_ counit renaming (η to ε)
    open counit
    field 
        zig : ∀{A : C.Ob} → ε (L₀ A) D.∘ L₁ (η A) ≡ D.id
        zag : ∀{B : D.Ob} → R₁ (ε B) C.∘ η (R₀ B) ≡ C.id






-- Displayed Categories
-- https://arxiv.org/pdf/1705.04296.pdf
-- https://1lab.dev/Cat.Displayed.Base.html#682

-- idea, add structure to some base category
-- example: Sets & functions -> monoids & monoid homs

record Displayed {o ℓ} (B : PreCat o ℓ) (o' ℓ' : Level) : Set (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where 
    open PreCat B
    -- data 
    field 
        Ob[_] : Ob → Set o'
        Hom[_] : ∀{x y : Ob} → Hom x y → Ob[ x ] → Ob[ y ] → Set ℓ'
        id' : ∀ {a : Ob} {x : Ob[ a ]} → Hom[ id ] x x  
        _∘'_ : ∀ {a b c x y z}{f : Hom b c}{g : Hom a b} → 
            Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

    infixr 40 _∘'_

    -- equalities in the displayed category should respect equalities in the base?
    -- not quite what this is
    _≡[_]_ : ∀ {a b x y}{f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
    _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

    infix 30 _≡[_]_

    -- laws 
    field 
        Hom[_]-set : ∀{a b : Ob} (f : Hom a b) → (x : Ob[ a ]) → (y : Ob[ b ]) → is-set (Hom[ f ] x y)
        idr' : ∀ {a b x y}{f : Hom a b} → (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
        idl' : ∀ {a b x y}{f : Hom a b} → (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
        assoc' : ∀ {a b c d w x y z}{f : Hom c d} {g : Hom b c}{h : Hom a b} → 
            (f' : Hom[ f ] y z) → (g' : Hom[ g ] x y) → (h' : Hom[ h ] w x) → 
            f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h' )


-- is there a map from Displayed to PreCat??
module maybe where 
    open Displayed
    open PreCat

    postulate
        o ℓ : Level 
        C : PreCat o ℓ
    {-
    huh : Displayed C o ℓ → PreCat o ℓ
    huh record 
            { Ob[_] = Ob[_] ; 
            Hom[_] = Hom[_] ; 
            id' = id' ; 
            _∘'_ = _∘'_ ; 
            Hom[_]-set = Hom[_]-set ; 
            idr' = idr' ; 
            idl' = idl' ; 
            assoc' = assoc' } = record
                                    { Ob = ∀{O} → Ob[_] O
                                    ; Hom = λ x x₁ → {! Hom[_]  !}
                                    ; Hom-set = {!   !}
                                    ; id = {!   !}
                                    ; _∘_ = {!   !}
                                    ; idr = {!   !}
                                    ; idl = {!   !}
                                    ; assoc = {!   !}
                                    }
-}
module coercion where 
    coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
    coe0→1 A a = transp (λ i → A i) i0 a
    
    coe0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i0 → A i
    coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

    to-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → coe0→1 A x ≡ y
         → PathP A x y
    to-pathp {A = A} {x} p i =
        hcomp (λ j → λ { (i = i0) → x
                    ; (i = i1) → p j })
            (coe0→i A i x)

    is-prop→pathp : ∀ {ℓ}{B : I → Set ℓ} → ((i : I) → is-prop (B i))
        → (b0 : B i0)(b1 : B i1)
        → PathP (λ i → B i) b0 b1 
    is-prop→pathp {B = B} hB b0 b1 = to-pathp (hB _ _ _)

-- as a displayed category
module DisplaySliceCat {o ℓ} (C : PreCat o ℓ) where 
    open PreCat C


    -- a morphism into x
    record Slice (x : Ob) : Set (o ⊔ ℓ) where 
        constructor slice 
        field 
            over : Ob 
            index : Hom over x
    open Slice

    -- why is this one parameterized by f ?
    record Slice-hom {x y} (f : Hom x y) (px : Slice x) (py : Slice y) : Set (o ⊔ ℓ) where
        constructor slice-hom 
        private
            module px = Slice px -- some map O₁ -> x
            module py = Slice py -- some map O₂ -> y
        field
            to : Hom px.over py.over
            commute : f ∘ px.index ≡ py.index ∘ to

    open Slice-hom


    {-} idea, a Slice Category is an kind of displayed category

        for C : PreCat 

        Ob[_] := (X : Ob) → Slice X
        Hom[_] := {X Y : Ob}{f : Hom X Y} → 
                    (A : Ob[ X ]) → (B : Ob[ Y ]) → Slice-hom {X Y} f A B 
    
    -}

    -- need a type for equality of slice morphisms
    module spp {x y}{f g : Hom x y}{px : Slice x}{py : Slice y}
             {f' : Slice-hom f px py}{g' : Slice-hom g px py} where
        
        -- if the underlying morphisms f and g are the same..
        -- and the .to components are the same..
        -- then the commuting diagram should be the same and you have an equality of 
        -- slice homomorphisms
        Slice-pathp : (p : f ≡ g) → (f' .to ≡ g' .to) → PathP (λ i → Slice-hom (p i) px py) f' g'
        Slice-pathp = {!   !}
        --Slice-pathp p p' i .to = p' i
        --Slice-pathp p p' i .commute = {!   !}

    open Displayed
    open CompSqr C
    open coercion
    open spp

    Slices : Displayed C (o ⊔ ℓ) (o ⊔ ℓ)
    Slices .Ob[_] = Slice
    Slices .Hom[_] = Slice-hom
    Slices .id' {x = x} = 
        slice-hom id 
            ((id ∘ index x) ≡⟨ idl _ ⟩ 
            index x ≡⟨ sym (idr _) ⟩ 
            index x ∘ id ∎)
    Slices ._∘'_ {x = x}{y = y}{z = z}{f = f}{g = g} px py = 
        slice-hom (px .to ∘ py .to) 
            (((f ∘ g) ∘ (x .index)) ≡⟨ pullr (py .commute) ⟩ 
            f ∘ y .index ∘ py .to ≡⟨ extendl (px .commute) ⟩ 
            z .index ∘ px .to ∘ py .to ∎)
    Slices .Hom[_]-set = {!   !} -- The tricky one...
    Slices .idr' {f = f} f' = Slice-pathp (idr f) (idr (f' .to))
    Slices .idl' {f = f} f' = Slice-pathp (idl f) (idl (f' .to))
    Slices .assoc' {f = f} {g = g} {h = h} f′ g′ h′ =
        Slice-pathp (assoc f g h) (assoc (f′ .to) (g′ .to) (h′ .to))
 
module SliceCat {o h} (C : PreCat o h) where 
    open PreCat C
    
    record /-Obj (c : Ob) : Set (o ⊔ h) where 
        no-eta-equality 
        constructor cut 
        field
            {domain} : Ob 
            map : Hom domain c

    open /-Obj

    record /-Hom {c : Ob} (a b : /-Obj c) : Set h where 
        no-eta-equality
        private
            module a = /-Obj a 
            module b = /-Obj b 
        field
            hmap : Hom a.domain b.domain
            commutes : b.map ∘ hmap ≡ a.map

    open /-Hom 

    _∘c_ : {a b c : Set} → (b → c)→ (a → b) → a → c
    g ∘c f = λ x → g ( f x)

    lemma : ∀ {a b c : Set} → (f : b → c) → (g g' : a → b) → (p : g ≡ g') → f ∘c g ≡ f ∘c g' 
    lemma f g g' p = cong (f ∘c_) p

    lemma'' : ∀ {a b c d : Set} → (p : a ≡ c) → (q : b ≡ c) → (r : a ≡ b) → (a ≡ c) ≡ (b ≡ c)
    lemma'' {c = c} p q r =  cong (_≡ c) r

    lemma' : ∀ {a b c : Set}(f f' : a → b)(g : b → c)(h : a → c)(p : f ≡ f') → (g ∘c f ≡ h) ≡ (g ∘c f' ≡ h)
    lemma' f f' g h p = cong (_≡ h) (lemma g f f' p) 

    -- equality of /-Hom 
    open coercion

    /-Hom-pathp : ∀ {c a a' b b'} (p : a ≡ a') (q : b ≡ b') 
                    {f : /-Hom {c = c} a b}{f' : /-Hom {c = c} a' b'}
                    → PathP (λ i → Hom (p i .domain) (q i .domain)) (f .hmap) (f' .hmap) 
                    → PathP (λ i → /-Hom (p i) (q i)) f f'
    /-Hom-pathp {c = c}p q {f} {f'} r = path where 
        path : PathP (λ i → /-Hom (p i) (q i)) f f'
        path i .hmap = r i -- got this equation..
        -- but wtf is this...
        path i .commutes = wat where 

            prp : (i : I) → is-prop (q i .map ∘ r i ≡ p i .map)
            prp i = Hom-set (p i .domain) c 
                    (q i .map ∘ r i)
                    -- = 
                    (p i .map)

            wat : _ 
            wat = is-prop→pathp prp (f .commutes) (f' .commutes) i
            -- recall if something is a prop, then its inhabitants are equal

    /-Hom-Path : ∀ {c a b}{f g : /-Hom {c = c} a b}
        → (f .hmap ≡ g .hmap)
        → f ≡ g
    /-Hom-Path = /-Hom-pathp refl refl

    module wtf where 
        postulate
            c : Ob
            x y x' y' : /-Obj c
            p : x ≡ x'
            q : y ≡ y' 
            i : I
            f : /-Hom x y 
            f' : /-Hom x' y'
            r : PathP (λ i → Hom (p i .domain) (q i .domain)) (f .hmap) (f' .hmap) 

        is : is-set (Hom (p i .domain) c)
        is = Hom-set (p i .domain) c

        _ : Hom (domain (p i)) c
        _ = p i .map

        _ : is-prop (q i .map ∘ r i ≡ p i .map)
        _ = is (q i .map ∘ r i) (p i .map) -- this is the equation I needed 
        -- but it was the special case
        -- y .map ∘ r i ≡ x .map
        -- where q := refl {y} and p := refl {x}

        -- so
        _ : is-prop (q i .map ∘ r i ≡ p i .map)
        _ = Hom-set (p i .domain) c (q i .map ∘ r i) (p i .map)

        -- so what if that's a prop.. why did we use is-prop→pathp ?



    open CompSqr C
    Slice : Ob → PreCat _ _ 
    Slice c = p where 
        p : PreCat _ _ 
        p .Ob = /-Obj c
        p .Hom = /-Hom
        p .Hom-set = {!   !}
        -- nested copatterns ??
        p .id .hmap = id
        p .id .commutes = idr _
        ----------------
        p ._∘_ {x} {y} {z} g f = fog where
            open /-Obj z renaming (map to zm)
            open /-Obj y renaming (map to ym)
            open /-Obj x renaming (map to xm)
            open /-Hom f renaming (hmap to f-hmap ; commutes to f-commutes)
            open /-Hom g renaming (hmap to g-hmap ; commutes to g-commutes) 
            fog : /-Hom _ _ 
            fog .hmap = g-hmap ∘ f-hmap
            fog .commutes = (zm ∘ g-hmap ∘ f-hmap) ≡⟨ pulll g-commutes ⟩ 
                            (ym ∘ f-hmap) ≡⟨ f-commutes ⟩ 
                            xm ∎
        p .idl f = /-Hom-Path (idl (f .hmap))
        p .idr f = /-Hom-Path (idr (f .hmap))
        p .assoc f g h = /-Hom-Path (assoc (f .hmap) (g .hmap) (h .hmap))

module ObjectProduct{o ℓ : Level} (𝒞 : PreCat o ℓ) where
        open PreCat 𝒞

        private 
            variable
                A B C D : Ob 
                h i j : A ⇒ B

        record Product (A B : Ob) : Set (o ⊔ ℓ) where
            infix 10 ⟨_,_⟩

            field
                A×B   : Ob
                π₁    : A×B ⇒ A
                π₂    : A×B ⇒ B
                ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

                project₁ : π₁ ∘ ⟨ h , i ⟩ ≡ h
                project₂ : π₂ ∘ ⟨ h , i ⟩ ≡ i
                unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h 

        
        module Morphisms where 

            open Product
            infix 10 [_]⟨_,_⟩ [_⇒_]_×_
            infix 12 [[_]] [_]π₁ [_]π₂

            [[_]] : Product A B → Ob 
            [[ p ]] = p .A×B

            [_]⟨_,_⟩ : ∀(p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
            [ p ]⟨ f , g ⟩ = ⟨_,_⟩ p f g

            [_]π₁ : ∀(p : Product A B) → [[ p ]] ⇒ A 
            [ p ]π₁ = π₁ p

            [_]π₂ : ∀(p : Product A B) → [[ p ]] ⇒ B
            [ p ]π₂ = π₂ p

            [_⇒_]_×_ : ∀(p₁ : Product A C)(p₂ : Product B D) → (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
            [ p₁ ⇒ p₂ ] f × g = [ p₂ ]⟨ f ∘ [ p₁ ]π₁ , g ∘ [ p₁ ]π₂ ⟩ 

module BinaryProducts {o h} (𝒞 : PreCat o h) where
        open ObjectProduct 𝒞
        open PreCat 𝒞
        open import Level using (levelOfTerm)
        private 
            variable
                A B C D : Ob 

        record BinaryProductsT : Set (levelOfTerm 𝒞) where
            infixr 7 _×_

            field
                product : ∀ {A B : Ob} → Product A B

            _×_ : Ob → Ob → Ob
            A × B = Product.A×B (product {A} {B})


            
            --_⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D

module Terminal {o h} (𝒞 : PreCat o h) where
    open PreCat 𝒞
        
    record IsTerminal(⊤ : Ob) : Set (o ⊔ h) where
        field
            ! : {A : Ob} → (A ⇒ ⊤)
            !-unique : ∀{A : Ob} → (f : A ⇒ ⊤) → ! ≡ f

    record TerminalT : Set (o ⊔ h) where 
        field 
            ⊤ : Ob 
            ⊤-is-terminal : IsTerminal ⊤

module Equalizer {o ℓ} (𝒞 : PreCat o ℓ) where 
    open PreCat 𝒞

    private 
        variable
            A B X : Ob 
            h i l : A ⇒ B

    record IsEqualizer {E : Ob} (arr : E ⇒ A) (f g : A ⇒ B) : Set (o ⊔ ℓ) where  
        field 
            equality : f ∘ arr ≡ g ∘ arr 
            equalize : ∀{h : X ⇒ A} → f ∘ h ≡ g ∘ h → X ⇒ E
            universal : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ equalize eq
            unique : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ i → i ≡ equalize eq

    record EqualizerT (f g : A ⇒ B) : Set (o ⊔ ℓ) where 
        field 
            {obj} : Ob 
            arr : obj ⇒ A 
            isEqualizer : IsEqualizer arr f g

            
module Cartesian {o h} (𝒞 : PreCat o h) where 
    open import Level using (levelOfTerm)
    open Terminal 𝒞 using (TerminalT)
    open BinaryProducts 𝒞 using (BinaryProductsT)

    record CartesianT : Set (levelOfTerm 𝒞) where 
        field 
            terminal : TerminalT
            products : BinaryProductsT


module Pullback {o ℓ}(𝒞 : PreCat o ℓ) where
    open PreCat 𝒞 
    private
        variable
            A B X Y Z  : Ob
            h₁ h₂ i f g : A ⇒ B 

    record IsPullback {P : Ob} (p₁ : P ⇒ X) (p₂ : P ⇒ Y)(f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
        field
            commute : f ∘ p₁ ≡ g ∘ p₂
            universal : ∀{h₁ : A ⇒ X}{h₂ : A ⇒ Y} → f ∘ h₁ ≡ g ∘ h₂ → A ⇒ P 
            unique : ∀{eq : f ∘ h₁ ≡ g ∘ h₂} → 
                        p₁ ∘ i ≡ h₁ → p₂ ∘ i ≡ h₂ → 
                        i ≡ universal eq
            p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                     p₁ ∘ universal eq ≡ h₁
            p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                     p₂ ∘ universal eq ≡ h₂

    record PullbackT (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
        field 
            {P} : Ob 
            p₁ : P ⇒ X 
            p₂ : P ⇒ Y 
            isPullback : IsPullback p₁ p₂ f g 



    open ObjectProduct 𝒞 
    open Equalizer 𝒞 
        -- do this proof later
    Product×Equalizer⇒Pullback : (p : Product A B) → EqualizerT (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) → PullbackT f g
    Product×Equalizer⇒Pullback = {!   !}

module Finitely {o ℓ} (𝒞 : PreCat o ℓ) where 
        open import Level using (levelOfTerm)

        open PreCat 𝒞 
        open BinaryProducts 𝒞 using (BinaryProductsT)
        open Cartesian 𝒞 using (CartesianT)
        open Equalizer 𝒞 using (EqualizerT)
        open Pullback 𝒞 using (PullbackT; Product×Equalizer⇒Pullback)

        record FinitelyComplete : Set (levelOfTerm 𝒞) where 
            field 
                cartesian : CartesianT
                equalizer : ∀ {A B : Ob} → (f g : A ⇒ B) → EqualizerT f g

            pullback : ∀{X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g  
            pullback f g = Product×Equalizer⇒Pullback (BinaryProductsT.product (CartesianT.products cartesian)) (equalizer _ _)
module LCC {o ℓ} (C : PreCat o ℓ) where 


module testing-unnamed-modules where
    open import Cubical.Data.Bool
    data F : Set where f : F

    module _{test : Bool} where 
        value : F 
        value = f
    
    module named {test : Bool} where 
        value' : F 
        value' = f

    module use where 
        _ : F 
        _ = value {true} -- Did not have to open the module above to access 'value'
                         -- but 'value' needed an implicit bool arg

        _ : F 
        _ = named.value' {true}


   -- https://1lab.dev/Cat.Instances.Slice.html#2190
    -- alternative definition of slice category
    --https://1lab.dev/Cat.Instances.Slice.html

    --https://1lab.dev/Cat.Functor.Pullback.html
    --https://1lab.dev/Cat.Diagram.Pullback.html   
{-}
module Pullback {ℓ ℓ'} (C : PreCat ℓ ℓ') where 
    open PreCat C

    private variable
        P' X Y Z : Ob 
        h p₁' p₂' : Hom X Y

        
    record is-pullback {P} (p₁ : Hom P X) (f : Hom X Z) (p₂ : Hom P Y) (g : Hom Y Z) : Set (ℓ ⊔ ℓ') where
        field
            square : f ∘ p₁ ≡ g ∘ p₂

            limiting : ∀ {P'} {p₁' : Hom P' X} {p₂' : Hom P' Y} 
                → f ∘ p₁' ≡ g ∘ p₂' → Hom P' P

            p₁∘limiting : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₁ ∘ limiting p ≡ p₁'
            p₂∘limiting : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₂ ∘ limiting p ≡ p₂'

            unique : {p : f ∘ p₁' ≡ g ∘ p₂'} {lim' : Hom P' P}
                → p₁ ∘ lim' ≡ p₁'
                → p₂ ∘ lim' ≡ p₂'
                → lim' ≡ limiting p

    record Pullback {X Y Z : Ob} (f : Hom X Z) (g : Hom Y Z) : Set (ℓ ⊔ ℓ') where 
        field
            {apex} : Ob 
            p₁ : Hom apex X 
            p₂ : Hom apex Y 
            has-is-pb : is-pullback p₁ f p₂ g

-- pullbacks in Agda
module pullagda where
    open import Agda.Primitive
    open PreCat
    open Pullback
    open Pullback.Pullback
    open Pullback.is-pullback

    Agda : PreCat (lsuc lzero) lzero 
    Agda .Ob = Set₀
    Agda .Hom = λ X Y → X → Y
    Agda .Hom-set = λ X Y → λ f g f≡g₁ f≡g₂ → {!   !}
    Agda ._∘_ = λ f g x → f (g x)
    Agda .id = λ x → x
    Agda .idr = λ f → refl
    Agda .idl = λ f → refl
    Agda .assoc = λ f g h → refl 


    open PreCat Agda
    open import Cubical.Data.Prod
    open import Cubical.Foundations.Everything using (_≡_; Σ)

    pbAgda  : {X Y Z : Set₀} (f : X → Z) (g : Y → Z) → Set₀
    pbAgda {X} {Y} f g =  Σ (X × Y) λ xy → f (proj₁ xy) ≡ g (proj₂ xy)

    pullbacks : ∀ {X Y Z} f g → Pullback Agda {X} {Y} {Z} f g
    pullbacks {X} {Y} {Z} f g = pb where 
        pb : Pullback Agda f g
        pb .apex = pbAgda f g  
        pb .p₁ = λ x → {! proj₁ x  !} --proj₁ (proj₁ x)
        pb .p₂ = λ x → {!   !} -- proj₂ (proj₁ x)
        pb .has-is-pb = ipb where 
            ipb : is-pullback Agda (pb .p₁) f (pb .p₂) g
            ipb .square = {!   !} -- funExt λ x → proj₂ x 
            ipb .limiting = λ p → λ P' → {! p  !} , {!  !} -- universal property of products
            ipb .p₁∘limiting = {!   !}
            ipb .p₂∘limiting = {!   !}
            ipb .unique = {!   !}

open Pullback
module ChangeBase{o ℓ}{C : PreCat o ℓ}
   (pullbacks : ∀{X Y Z} f g → Pullback C {X} {Y} {Z} f g) where 
    -- ^ how to provide this function for Precat Agda for example?

    open PreCat C
    open SliceCat C
    open Functor
    open SliceCat./-Obj
    open SliceCat./-Hom
    open Pullback.Pullback 

    module _ {X Y : Ob}(f : Hom Y X) where 
        Base-Change : Functor (Slice X) (Slice Y)
        Base-Change .F₀ x = ob where 
            ob : /-Obj Y 
            ob .domain = pullbacks (x .map) f .apex
            ob .map    = pullbacks (x .map) f .p₂
            
        Base-Change .F₁ {x} {y} f = fn where 
            fn : /-Hom (Base-Change .F₀ x) (Base-Change .F₀ y) 
            fn .hmap = {!   !}
            fn .commutes = {!   !}

        Base-Change .F-id = {!   !}
        Base-Change .F-∘ = {!   !} 
  -}