{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import PHOAS

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
  ℕ-recurse z s zero    = z
  ℕ-recurse z s (suc n) = s (ℕ-recurse z s n)

  eval : Env Γ → Tm[ q ] Γ A → Val A
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (` i)         = eval ρ i
  eval ρ (t · u)       = (eval ρ t) (eval ρ u)
  eval ρ (ƛ t) u       = eval (ρ , u) t
  eval ρ tt            = tt
  eval ρ ze            = zero
  eval ρ (su n)        = suc (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-recurse (eval ρ z) (eval ρ s) (eval ρ n)

  module Example-ChurchEval where
    open Example-Church

    church-two : Val (Cℕ A)
    church-two = eval ε (C+ · (Csuc · Czero)  · (Csuc · Czero))

    test : church-two {A = A} ≡ λ s z → s (s z)
    test = refl

  -- Doesn't work! Var'iables are not 'Val'ues
  -- Though... if we stuck with just '⊤' and '_⇒_' type formers, I think we
  -- could actually implement a 'reflect : Ne Γ A → Val Γ A'. I'll give this
  -- a try in a bit...
  reify : Val A → Nf Γ A
  reify {A = ⊤'}    tt     = tt
  reify {A = ℕ'}    zero   = ze
  reify {A = ℕ'}   (suc n) = su (reify n)
  reify {A = A ⇒ B} t      = ƛ reify (t {!vz!})


module Attempt2 where
  Val    : Ctx → Ty → Set
  PreVal : Ctx → Ty → Set
  
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
  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)        = val λ u → eval (ρ , u) t
  eval ρ tt           = val tt
  eval ρ ze            = val zero
  eval ρ (su n)        = suc-val (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

  -- Stuck again! 'Ne'utrals are *also* not 'Val'ues
  app-val (val t) u = t u
  app-val (var i) u = {!!}

  -- Also stuck implementing the 'ℕ' constructor/recursor on 'Val's. We need
  -- 'suc' to accept neutrals
  suc-val (val n) = val (suc n)
  suc-val (var i) = {!!}

  ℕ-rec-val z s (val zero)    = z
  ℕ-rec-val z s (val (suc n)) = app-val s (ℕ-rec-val z s (val n))
  ℕ-rec-val z s (var i) = {!!}
