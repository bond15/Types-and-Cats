module MLT where 

open import Cubical.Data.Unit
open import Cubical.Foundations.Everything using (_≡_; Σ)

data ML : Set  
⦅_⦆ : ML → Set 

data ML where 
    ⊤ : ML 
    Id : (x : ML) → (t t' : ⦅ x ⦆) → ML
    Π Σ' : (x : ML) → (⦅ x ⦆ → ML) → ML

⦅ ⊤ ⦆ = Unit
⦅ Id A x y ⦆ = x ≡ y
⦅ Π a B ⦆ = (x : ⦅ a ⦆) → ⦅ B x ⦆
⦅ Σ' a B ⦆ = Σ ⦅ a ⦆ (λ x → ⦅ B x ⦆)
