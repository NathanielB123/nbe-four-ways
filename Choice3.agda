{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst
open import Utils

module Choice3 where 

Val    : Ctx → Ty → Set
PreVal : Ctx → Ty → Set
data Env (Δ : Ctx) : Ctx → Set

ℕVal : Ctx → Set

data ℕPreVal (Γ : Ctx) : Set where
  ze  : ℕPreVal Γ
  su  : ℕVal Γ → ℕPreVal Γ

ℕVal Γ = ℕPreVal Γ ⊎ Ne Γ ℕ'

record ⇒PreVal (Γ : Ctx) (A B : Ty) : Set where
  constructor clo
  inductive
  field
    {ctx} : Ctx
    env   : Env Γ ctx
    body  : Tm (ctx , A) B

PreVal Γ ⊤'      = ⊤
PreVal Γ ℕ'      = ℕPreVal Γ
-- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
-- a sequence of additional 'Var'iables which can be thrown onto the front
-- of the context
-- The original lisp code avoids this complexity by using named variables
PreVal Γ (A ⇒ B) = ⇒PreVal Γ A B

Val Γ A = PreVal Γ A ⊎ Ne Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

-- Unfortunately we can't use the abstract 'Env' module here because 'wk*' for
-- 'Val'ues and 'Env'ironments here is mutually recursive 
data Env Δ where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

wk*-val             Δ (reflect t)     = reflect (wk*-ne Δ t)
wk*-val {A = ⊤'}    Δ (val tt)        = val tt
wk*-val {A = ℕ'}    Δ (val ze)        = val ze
wk*-val {A = ℕ'}    Δ (val (su n))    = val (su (wk*-val Δ n))
wk*-val {A = A ⇒ B} Δ (val (clo ρ t)) = val (clo (wk*-env Δ ρ) t)

wk*-env Θ ε       = ε
wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

_^ᴱ_ : Env Δ Γ → ∀ A → Env (Δ , A) (Γ , A)
ρ ^ᴱ A = wk*-env (ε , A) ρ , reflect (` vz)

idᴱ : Env Γ Γ
idᴱ {Γ = ε}     = ε
idᴱ {Γ = Γ , A} = idᴱ ^ᴱ A

-- I don't know how to make 'Choice3' work without asserting termination.
-- It sort-of makes sense why this approach isn't structurally recursive: the
-- LHS of an application could 'eval' to a 'Clo'sure, but applying a 'Clo'sure
-- requires an additional 'eval' on the body. We have no guarantee that the 
-- term inside a 'Clo'sure produced by 'eval' is any smaller than the 
-- original 'eval'-ed term (e.g. consider variables, where 'eval' looks up a 
-- 'Val'ue in the 'Env'ironment).

-- If we had structurally recursive substitutions (on 'Val's specifically), 
-- another approach could be to store the body of 'Clo'sures as a 'Val'
-- instead of a 'Tm' (conceptually neater anyway IMO) and then 'app-val'
-- would apply the substitution 'ρ , t' to the closure body. Of course, 'Val's
-- contain 'Ne'utrals, so attempting to implement recursive substitutions
-- naively will hit a variation on the same problem (LHS 'Ne'utral could 
-- become unblocked after a substitution)

{-# TERMINATING #-}
eval    : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
reify   : Val Γ A → Nf Γ A
ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

eval ρ (` i)         = eval ρ i
eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = val (clo ρ t) 
eval ρ tt            = val tt
eval ρ ze            = val ze
eval ρ (su n)        = val (su (eval ρ n))
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

app-val (val (clo ρ t)) u = eval (ρ , u) t
app-val (reflect t)     u = reflect (t · reify u)

ℕ-rec-val z s (val ze)     = z
ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (reflect t)  = reflect (ℕ-rec (reify z) (reify s) t)

reify             (reflect t)     = ne t
reify {A = ⊤'}    (val tt)        = tt
reify {A = ℕ'}    (val ze)        = ze
reify {A = ℕ'}    (val (su n))    = su (reify n)
reify {A = A ⇒ B} (val (clo ρ t)) = ƛ reify (eval (ρ ^ᴱ A) t)

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)
