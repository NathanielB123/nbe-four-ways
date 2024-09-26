{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst

module Env (Val     : Ctx → Ty → Set) 
           (wk*-val : ∀ {Γ A} Δ → Val Γ A → Val (Γ ++ Δ) A)  
           (vz-val  : ∀ {Γ A} → Val (Γ , A) A)
           where

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

wk*-env : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ
wk*-env Θ ε       = ε
wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

_^ᴱ_ : Env Δ Γ → ∀ A → Env (Δ , A) (Γ , A)
ρ ^ᴱ A = wk*-env (ε , A) ρ , vz-val

idᴱ : Env Γ Γ
idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ ^ᴱ A
