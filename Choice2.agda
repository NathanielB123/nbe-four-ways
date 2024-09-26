{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst

module Choice2 where 

data ⊤Val (Γ : Ctx) : Set where
  tt : ⊤Val Γ
  -- We could also remove the 'Ne'utral case here to get η for '⊤'
  -- In fact, whether we allow 'Ne'utral values for each type former can be seen
  -- as a decision of whether we want η or not (though, we can't just get
  -- η for every type - specifically just the ones where 'reflect' can stay
  -- structurally recursive)
  ne : Ne Γ ⊤' → ⊤Val Γ

data ℕVal (Γ : Ctx) : Set where
  ze : ℕVal Γ
  su : ℕVal Γ → ℕVal Γ
  ne : Ne Γ ℕ' → ℕVal Γ

Val : Ctx → Ty → Set
Val Γ ⊤'      = ⊤Val Γ
Val Γ ℕ'      = ℕVal Γ
-- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
-- a sequence of additional 'Var'iables which can be thrown onto the front
-- of the context
-- The original lisp code avoids this complexity by using named variables
Val Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

wk*-val {A = ⊤'}    Δ tt     = tt
wk*-val {A = ℕ'}    Δ ze     = ze
wk*-val {A = ℕ'}    Δ (su n) = su (wk*-val Δ n)
wk*-val {A = A ⇒ B} Δ t Θ u  = t (Δ ++ Θ) u
wk*-val {A = ⊤'}    Δ (ne t) = ne (wk*-ne Δ t)
wk*-val {A = ℕ'}    Δ (ne t) = ne (wk*-ne Δ t)

wk*-env Θ ε       = ε
wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

eval : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
ℕ-rec-val : Val Γ A → (Val Γ (A ⇒ A)) → Val Γ ℕ' → Val Γ A
reify   : Val Γ A → Nf Γ A
reflect : Ne Γ A → Val Γ A

eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (` i)         = eval ρ i
eval ρ (t · u)       = (eval ρ t) ε (eval ρ u)
eval ρ (ƛ t)         = λ Δ u → eval (wk*-env Δ ρ , u) t
eval ρ tt            = tt
eval ρ ze            = ze
eval ρ (su n)        = su (eval ρ n)
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

ℕ-rec-val z s ze     = z
ℕ-rec-val z s (su n) = s ε (ℕ-rec-val z s n)
ℕ-rec-val z s (ne t) = reflect (ℕ-rec (reify z) (reify s) t)

reify {A = ⊤'}    tt     = tt
reify {A = ⊤'}    (ne t) = ne t
reify {A = ℕ'}    ze     = ze
reify {A = ℕ'}    (su n) = su (reify n)
reify {A = ℕ'}    (ne n) = ne n
reify {A = A ⇒ B} t      = ƛ (reify (t (ε , A) (reflect (` vz))))

reflect {A = ⊤'}    t     = ne t
reflect {A = ℕ'}    n     = ne n
reflect {A = A ⇒ B} t Δ u = reflect (wk*-ne Δ t · reify u)
