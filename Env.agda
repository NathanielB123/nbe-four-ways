open import Syntax
open import Subst

module Env (Val     : Ctx → Ty → Set) 
           (_[_]val : ∀ {Γ Δ A} → Val Γ A → Vars Δ Γ → Val Δ A)  
           (vz-val  : ∀ {Γ A} → Val (Γ , A) A)
           where

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

_[_]env : Env Δ Γ → Vars Θ Δ → Env Θ Γ
ε       [ δ ]env = ε
(ρ , t) [ δ ]env = (ρ [ δ ]env) , (t [ δ ]val)

_^ᴱ_ : Env Δ Γ → ∀ A → Env (Δ , A) (Γ , A)
ρ ^ᴱ A = (ρ [ id ⁺ ]env) , vz-val

idᴱ : Env Γ Γ
idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ ^ᴱ A
