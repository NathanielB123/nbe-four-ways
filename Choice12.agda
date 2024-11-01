{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import Subst

module Choice12 where 

ℕVal : Ctx → Set

data ℕPreVal (Γ : Ctx) : Set where
  ze  : ℕPreVal Γ
  su  : ℕVal Γ → ℕPreVal Γ

ℕVal Γ = ℕPreVal Γ ⊎ Ne Γ ℕ'

Val    : Ctx → Ty → Set
PreVal : Ctx → Ty → Set

PreVal Γ ⊤'      = ⊤
PreVal Γ ℕ'      = ℕPreVal Γ
-- To enable weakening 'Val's, we parameterise the '_⇒_' case over a renaming 
-- The original lisp code avoids this complexity by using named variables
PreVal Γ (A ⇒ B) = ∀ {Δ} (δ : Vars Δ Γ) → Val Δ A → Val Δ B

Val Γ A = PreVal Γ A ⊎ Ne Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

_∋_[_]val : ∀ A → Val Γ A → Vars Δ Γ → Val Δ A
A       ∋ reflect t  [ δ ]val = reflect (t [ δ ]ne)
⊤'      ∋ val tt     [ δ ]val = val tt
ℕ'      ∋ val ze     [ δ ]val = val ze
ℕ'      ∋ val (su n) [ δ ]val = val (su (ℕ' ∋ n [ δ ]val))
(A ⇒ B) ∋ val t      [ δ ]val = val λ σ u → t (δ ⨾ σ) u

open import Env Val (_ ∋_[_]val) (reflect (` vz))

-- We parameterise over 'reify' implementation here because there are actually
-- two reasonable alternatives
module Eval (reify : ∀ {Γ A} → Val Γ A → Nf Γ A) where
  eval      : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  app-val   : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

  eval ρ (` i)         = eval ρ i
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)         = val (λ δ u → eval ((ρ [ δ ]env) , u) t)
  eval ρ tt            = val tt
  eval ρ ze            = val ze
  eval ρ (su n)        = val (su (eval ρ n))
  eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

  ℕ-rec-val z s (val ze)     = z
  ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s n)
  ℕ-rec-val z s (reflect t)  = reflect (ℕ-rec (reify z) (reify s) t)

  app-val (val t)     u = t id u
  app-val (reflect t) u = reflect (t · reify u)

-- Simple 'reify'. Avoids blocking on the type of 'Ne'utrals and produces 
-- β-normal forms
reify : Val Γ A → Nf Γ A
reify             (reflect t)  = ne t
reify {A = ⊤'}    (val tt)     = tt
reify {A = ℕ'}    (val ze)     = ze
reify {A = ℕ'}    (val (su n)) = su (reify n)
reify {A = A ⇒ B} (val t)      = ƛ reify (t (id ⁺) (reflect (` vz)))

-- 'reify' which implements 'η' reductions. Always blocks on the type.
reify-η : Val Γ A → Nf Γ A
reify-η {A = ℕ'}    (val ze)     = ze
reify-η {A = ℕ'}    (val (su n)) = su (reify-η n)
reify-η {A = A ⇒ B} (val t)      = ƛ reify-η (t (id ⁺) (reflect (` vz)))
-- η for '⊤'
reify-η {A = ⊤'}    _            = tt
-- η for '_⇒_'
reify-η {A = A ⇒ B} (reflect t)  = ƛ ne ((t [ id ⁺ ]ne) · ne (` vz))
reify-η {A = ℕ'}    (reflect t)  = ne t

open Eval reify   using    (eval)           public
open Eval reify-η renaming (eval to eval-η) public

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)

norm-η : Tm Γ A → Nf Γ A
norm-η t = reify-η (eval-η idᴱ t)

module Example-Norm where
  open import Examples
  open Example-ChurchNats

  test-Ctwo : norm (Ctwo {Γ = Γ} {A = A}) 
            ≡ ƛ (ƛ ne (` vs vz · ne (` vs vz · ne (` vz))))
  test-Ctwo = refl

module Example-Norm-η where
  open import Examples
  open Example-ChurchNats

  -- 'reify-η' always blocks on the type, we have to instantiate with a 
  -- concrete type (e.g. 'ℕ') to normalise a term
  test-Ctwo-ℕ : norm (Ctwo {Γ = Γ} {A = ℕ'}) 
              ≡ ƛ (ƛ ne (` vs vz · ne (` vs vz · ne (` vz))))
  test-Ctwo-ℕ = refl

  -- On the upside, blocking on the type means we can implement type-directed
  -- reductions; in other words, we can respect eta-equalities!
  test-Ctwo-⊤ : norm-η (Ctwo {Γ = Γ} {A = ⊤'}) 
              ≡ ƛ ƛ tt
  test-Ctwo-⊤ = refl

  open Example-Apply
  
  test-apply1 : norm-η (apply {Γ = Γ} {A = ℕ'} {B = ℕ'})
              ≡ ƛ (ƛ ne (` vs vz · ne (` vz)))
  test-apply1 = refl

  test-apply2 : norm-η (apply {Γ = Γ} {A = ℕ' ⇒ ℕ'} {B = ℕ' ⇒ ℕ'})
              ≡ ƛ ƛ ƛ ne (` vs (vs vz) · (ƛ ne (` vs (vs vz) 
                                       · ne (` vz))) · ne (` vz))
  test-apply2 = refl
 