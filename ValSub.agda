{-# OPTIONS --rewriting --local-confluence-check #-}


open import Utils
open import Syntax
open import Subst

-- A demonstration of how to implement structurally recursive substitutions
-- over 'Val'ues WITHOUT directly calling 'reify'!

-- I think this could have some really exciting applications towards NbE for
-- dependent types...
module ValSub where

ℕVal : Ctx → Set

data ℕPreVal (Γ : Ctx) : Set where
  ze  : ℕPreVal Γ
  su  : ℕVal Γ → ℕPreVal Γ

ℕVal Γ = ℕPreVal Γ ⊎ Ne Γ ℕ'

Val    : Ctx → Ty → Set
PreVal : Ctx → Ty → Set

PreVal Γ ⊤'      = ⊤
PreVal Γ ℕ'      = ℕPreVal Γ
-- Functions
PreVal Γ (A ⇒ B) = ∀ {Δ} → Vars Δ Γ → Val Δ A → Val Δ B

Val Γ A = PreVal Γ A ⊎ Ne Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

_∋_[_]val-ren : ∀ A → Val Γ A → Vars Δ Γ → Val Δ A
A       ∋ reflect t  [ δ ]val-ren = reflect (t [ δ ]ne)
⊤'      ∋ val t      [ δ ]val-ren = val t
ℕ'      ∋ val ze     [ δ ]val-ren = val ze
ℕ'      ∋ val (su n) [ δ ]val-ren = val (su (ℕ' ∋ n [ δ ]val-ren))
(A ⇒ B) ∋ val t      [ δ ]val-ren = val λ σ u → t (δ ⨾ σ) u

_[_]env-ren : Env Δ Γ → Vars Θ Δ → Env Θ Γ
ε       [ σ ]env-ren = ε
(δ , t) [ σ ]env-ren = δ [ σ ]env-ren , _ ∋ t [ σ ]val-ren

-- Evaluation isn't the main focus of this module, but we need it to do
-- substitutions on neutrals...
module Eval where
  reify : Val Γ A → Nf Γ A
  reify             (reflect t)  = ne t
  reify {A = ⊤'}    (val tt)     = tt
  reify {A = ℕ'}    (val ze)     = ze
  reify {A = ℕ'}    (val (su n)) = su (reify n)
  reify {A = A ⇒ B} (val t)      = ƛ reify (t (id ⁺) (reflect (` vz)))

  eval      : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  app-val   : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

  eval ρ (` i)         = eval ρ i
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)         = val (λ δ u → eval (ρ [ δ ]env-ren , u) t)
  eval ρ tt            = val tt
  eval ρ ze            = val ze
  eval ρ (su n)        = val (su (eval ρ n))
  eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

  ℕ-rec-val z s (val ze)     = z
  ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s n)
  ℕ-rec-val z s (reflect t)  = reflect (ℕ-rec (reify z) (reify s) t)

  app-val (val t)     u = t id u
  app-val (reflect t) u = reflect (t · reify u)

open Eval using (eval)

_⋄ᴱ_ : Env Δ Γ → Vars Δ Θ → Env Δ (Γ ++ Θ)
δ ⋄ᴱ ε       = δ
δ ⋄ᴱ (σ , i) = (δ ⋄ᴱ σ) , reflect (` i)

_∋_[_]val : ∀ A → Val Γ A → Env Δ Γ → Val Δ A

-- Can just inject back into `Tm` and re-`eval`, easy!
A       ∋ reflect t  [ δ ]val = eval δ (ne→tm t)

⊤'      ∋ val t      [ δ ]val = val t
ℕ'      ∋ val ze     [ δ ]val = val ze
ℕ'      ∋ val (su n) [ δ ]val = val (su (ℕ' ∋ n [ δ ]val))

-- The interesting case!
(A ⇒ B) ∋ val t [ δ ]val
  = val λ σ u → B ∋ (t (wk* _) (A ∋ u [ *wk _ ]val-ren) ) 
                    [ (δ [ σ ]env-ren) ⋄ᴱ id ]val 
