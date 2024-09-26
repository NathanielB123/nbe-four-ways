{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import Examples

module FirstAttempts where

module Attempt1 where
  -- We must define 'Val' recursively to satisfy Agda's positivity checking.
  -- This can be seen as a non-dependent version of a logical relation: i.e.
  -- we compute a predicate by recursion on types (only the predicate doesn't
  -- need to depend on the term, because we are not trying to prove stability/
  -- completeness... yet)
  Val : Ty → Set
  Val ⊤'      = ⊤
  Val ℕ'      = ℕ
  Val (A ⇒ B) = (Val A → Val B)

  data Env : Ctx → Set where
    ε   : Env ε
    _,_ : Env Γ → Val A → Env (Γ , A)

  ℕ-recurse : ∀ {A : Set} → A → (A → A) → ℕ → A
  ℕ-recurse z s ze     = z
  ℕ-recurse z s (su n) = s (ℕ-recurse z s n)

  eval : Env Γ → Tm[ q ] Γ A → Val A
  eval ρ (` i)         = eval ρ i
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (t · u)       = (eval ρ t) (eval ρ u)
  eval ρ (ƛ t) u       = eval (ρ , u) t
  eval ρ tt            = tt
  eval ρ ze            = ze
  eval ρ (su n)        = su (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-recurse (eval ρ z) (eval ρ s) (eval ρ n)

  module Example-ChurchNatEval where
    open Example-ChurchNats

    test : eval ε (Ctwo {A = A}) ≡ λ s z → s (s z)
    test = refl

  reify   : Val A → Nf Γ A
  reflect : Ne Γ A → Val A 

  reify {A = ⊤'}    tt     = tt
  reify {A = ℕ'}    ze     = ze
  reify {A = ℕ'}    (su n) = su (reify n)
  -- The original post gives up here, but we'll try and go a bit further and
  -- try to implement a way to convert 'Ne'utrals (like '` vz') to 'Val'ues.
  reify {A = A ⇒ B} t      = ƛ reify (t (reflect (` vz {Γ = ε})))

  reflect {A = ⊤'}    t   = tt
  reflect {A = A ⇒ B} t u = reflect (t · reify u)
  -- Unfortunately, we still get stuck. The η-rule for 'ℕ' isn't structurally
  -- recursive on 'Ty'pes like '⊤' and '_⇒_'.
  -- However, if we stick to an object theory with only negative types, then 
  -- we actually can make this sort-of work - see 'ExtremeEta'
  reflect {A = ℕ'}    t   = reflect (ℕ-rec ze (ƛ su (ne (` vz))) t)

module Attempt2 where
  Val    : Ctx → Ty → Set
  PreVal : Ctx → Ty → Set
  
  -- In the second attempt, we try to only add 'Var'iables to 'Val'ues (i.e. not
  -- full-blown 'Ne'utrals)
  Val Γ A = PreVal Γ A ⊎ Var Γ A
  PreVal Γ ⊤'      = ⊤
  PreVal Γ ℕ'      = ℕ
  PreVal Γ (A ⇒ B) = Val Γ A → Val Γ B

  pattern var i = inj₂ i
  pattern val t = inj₁ t

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  app-val   : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  suc-val   : Val Γ ℕ' → Val Γ ℕ'
  ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

  eval : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  eval ρ (` i)         = eval ρ i
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)         = val λ u → eval (ρ , u) t
  eval ρ tt            = val tt
  eval ρ ze            = val ze
  eval ρ (su n)        = suc-val (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

  -- Of course, we get stuck again. The only way to apply a 'Var'iable to
  -- something is to build a 'Ne'utral (note if we try to implement 'reflect' 
  -- we will hit exactly the same trouble as before).
  app-val (val t) u = t u
  app-val (var i) u = {!!}

  -- We also get stuck implementing the 'ℕ' constructor/recursor on 'Val's. 
  -- We need 'Val'ue 'su' to accept neutrals.
  suc-val (val n) = val (su n)
  suc-val (var i) = {!!}

  ℕ-rec-val z s (val ze)    = z
  ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s (val n))
  ℕ-rec-val z s (var i)       = {!!}
