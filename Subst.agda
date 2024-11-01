open import Utils
open import Syntax

module Subst where

-- Technically, we only *really* need weakening, but we might as well define 
-- substitutions in their full generality!
-- Thorsten Altenkirch originally came up with the trick that lets us do this
-- without copy and paste.
data Tms[_] (q : Sort) : Ctx → Ctx → Set where
  ε   : Tms[ q ] Δ ε
  _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

Vars = Tms[ V ]
Tms  = Tms[ T ]

vz[_] : ∀ q → Tm[ q ] (Γ , A) A
vz[ V ] = vz
vz[ T ] = ` vz


suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ , A) B
_⁺     : Tms[ q ] Δ Γ → Tms[ q ] (Δ , A) Γ
_^_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) (Γ , A)
_[_]   : Tm[ q ] Γ A → Tms[ s ] Δ Γ → Tm[ q ⊔ s ] Δ A 
id[_]  : ∀ q → Tms[ q ] Γ Γ

id     : Vars Γ Γ
id = id[ V ]
{-# INLINE id #-} 

suc[ V ]   = vs
suc[ T ] t = t [ id ⁺ ]

ε ⁺       = ε
(δ , t) ⁺ = δ ⁺ , suc[ _ ] t

δ ^ A = δ ⁺ , vz[ _ ]

id[_] {Γ = ε} _     = ε
id[_] {Γ = Γ , A} _ = id[ _ ] ^ A

vz          [ δ , t ] = t
vs i        [ δ , t ] = i [ δ ]
(` i)       [ δ ]     = tm⊑ (i [ δ ])
(t · u)     [ δ ]     = t [ δ ] · u [ δ ]
(ƛ t)       [ δ ]     = ƛ (t [ δ ^ _ ])
tt          [ δ ]     = tt
ze          [ δ ]     = ze
su n        [ δ ]     = su (n [ δ ])
ℕ-rec z s n [ δ ]     = ℕ-rec (z [ δ ]) (s [ δ ]) (n [ δ ])

_[_]ne : Ne Γ A → Vars Δ Γ → Ne Δ A
_[_]nf : Nf Γ A → Vars Δ Γ → Nf Δ A

(` i)       [ δ ]ne = ` (i [ δ ])
(t · u)     [ δ ]ne = t [ δ ]ne · u [ δ ]nf
ℕ-rec z s n [ δ ]ne = ℕ-rec (z [ δ ]nf) (s [ δ ]nf) (n [ δ ]ne)

ne t  [ δ ]nf = ne (t [ δ ]ne)
(ƛ t) [ δ ]nf = ƛ  (t [ δ ^ _ ]nf)
tt    [ δ ]nf = tt
ze    [ δ ]nf = ze
su n  [ δ ]nf = su (n [ δ ]nf)

_⨾_ : Tms[ q ] Δ Γ → Tms[ r ] Θ Δ → Tms[ q ⊔ r ] Θ Γ
ε ⨾ σ       = ε
(δ , x) ⨾ σ = (δ ⨾ σ) , (x [ σ ])

_++_ : Ctx → Ctx → Ctx
Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

wk*[_] : ∀ q Δ → Tms[ q ] (Γ ++ Δ) Γ
wk*[ q ] ε       = id[ q ]
wk*[ q ] (Δ , A) = wk*[ q ] Δ ⁺

wk* : ∀ Δ → Vars (Γ ++ Δ) Γ
wk* = wk*[ V ]

*wk[_] : ∀ q Γ → Tms[ q ] (Δ ++ Γ) Γ
*wk[ q ] ε       = ε
*wk[ q ] (Γ , A) = *wk[ q ] Γ ^ A

*wk : ∀ Γ → Vars (Δ ++ Γ) Γ
*wk = *wk[ _ ]
