{-# OPTIONS --rewriting --local-confluence-check #-}


open import Utils
open import Syntax
open import Subst

-- A demonstration of how to implement structurally recursive substitutions
-- over 'Val'ues WITHOUT calling 'reify'!

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
PreVal Γ (A ⇒ B) = ∀ Δ → Vars Δ Γ → Val Δ A → Val Δ B

Val Γ A = PreVal Γ A ⊎ Ne Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

-- Refer to 'Choice12' for how we would actually implement 'eval'uation (just
-- recursion over terms). I will skip over the definition here
postulate eval : Env Δ Γ → Tm Γ A → Val Δ A

_∋_[_]val : ∀ A → Val Γ A → Env Δ Γ → Val Δ A

_⨾v_ : Vars Δ Γ → Vars Θ Δ → Vars Θ Γ
ε ⨾v σ       = ε
(δ , i) ⨾v σ = (δ ⨾v σ) , i [ σ ]

_∋_[_]val-ren : ∀ A → Val Γ A → Vars Δ Γ → Val Δ A
A       ∋ reflect t  [ δ ]val-ren = reflect (t [ δ ]ne)
⊤'      ∋ val t      [ δ ]val-ren = val t
ℕ'      ∋ val ze     [ δ ]val-ren = val ze
ℕ'      ∋ val (su n) [ δ ]val-ren = val (su (ℕ' ∋ n [ δ ]val-ren))
(A ⇒ B) ∋ val t      [ δ ]val-ren = val λ Δ σ u → t _ (δ ⨾v σ) u

_[_]env-ren : Env Δ Γ → Vars Θ Δ → Env Θ Γ
ε       [ σ ]env-ren = ε
(δ , t) [ σ ]env-ren = δ [ σ ]env-ren , _ ∋ t [ σ ]val-ren

wk*-front : ∀ Δ → Vars (Δ ++ Γ) Γ
wk*-front {Γ = ε}     Δ = ε
wk*-front {Γ = Γ , A} Δ = wk*-front Δ ^ A

_^ᴱ_ : Env Δ Γ → ∀ A → Env (Δ , A) (Γ , A)
δ ^ᴱ A = δ [ wk* (ε , A) ]env-ren , reflect (` vz)

_^ᴱ*_   : Env Δ Γ → ∀ Θ → Env (Δ ++ Θ) (Γ ++ Θ)
δ ^ᴱ* ε       = δ
δ ^ᴱ* (Θ , A) = (δ ^ᴱ* Θ) ^ᴱ A

_^*_      : Vars Δ Γ → ∀ Θ → Vars (Δ ++ Θ) (Γ ++ Θ)
δ ^* ε       = δ
δ ^* (Θ , A) = (δ ^* Θ) ^ A

_++v_ : Vars Δ Γ → Vars Δ Θ → Vars Δ (Γ ++ Θ)
δ ++v ε       = δ
δ ++v (σ , i) = (δ ++v σ) , i

collapse : Vars Γ (Γ ++ Γ)
collapse = id ++v id

-- Can just inject back into `Tm` and re-`eval`, easy!
A       ∋ reflect t  [ δ ]val = eval δ (ne→tm t)

⊤'      ∋ val t      [ δ ]val = val t
ℕ'      ∋ val ze     [ δ ]val = val ze
ℕ'      ∋ val (su n) [ δ ]val = val (su (ℕ' ∋ n [ δ ]val))

_∋_[_]val {Γ = Γ} {Δ = Δ} (A ⇒ B) (val t) δ
  = val λ Θ σ u → B ∋ (B ∋ t (Γ ++ Θ) (wk* Θ) (A ∋ u [ wk*-front Γ ]val-ren) 
                         [ δ ^ᴱ* Θ ]val) 
                    [ (σ ^* Θ) ⨾v collapse ]val-ren
