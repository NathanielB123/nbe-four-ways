{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst

module Choice3 where 

Val : Ctx → Ty → Set
data Env (Δ : Ctx) : Ctx → Set

data ⊤Val (Γ : Ctx) : Set where
  tt    : ⊤Val Γ
  ne    : Ne Γ ⊤' → ⊤Val Γ

data ℕVal (Γ : Ctx) : Set where
  ze  : ℕVal Γ
  su  : ℕVal Γ → ℕVal Γ
  ne  : Ne Γ ℕ' → ℕVal Γ

data ⇒Val (Γ : Ctx) (A B : Ty) : Set where
  clo : Env Γ Δ → Tm (Δ , A) B → ⇒Val Γ A B
  ne  : Ne Γ (A ⇒ B) → ⇒Val Γ A B

Val Γ ⊤'      = ⊤Val Γ
Val Γ ℕ'      = ℕVal Γ
Val Γ (A ⇒ B) = ⇒Val Γ A B

reflect : Ne Γ A → Val Γ A
reflect {A = ⊤'}    = ne
reflect {A = ℕ'}    = ne
reflect {A = A ⇒ B} = ne

-- Unfortunately we can't use the abstract 'Env' module here because 'wk*' for
-- 'Val'ues and 'Env'ironments here is mutually recursive 
data Env Δ where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

wk*-val {A = ⊤'}    Δ tt        = tt
wk*-val {A = ℕ'}    Δ ze        = ze
wk*-val {A = ℕ'}    Δ (su n)    = su (wk*-val Δ n)
wk*-val {A = A ⇒ B} Δ (clo ρ t) = clo (wk*-env Δ ρ) t
wk*-val {A = ⊤'}    Δ (ne t)    = ne (wk*-ne Δ t)
wk*-val {A = ℕ'}    Δ (ne t)    = ne (wk*-ne Δ t)
wk*-val {A = A ⇒ B} Δ (ne t)    = ne (wk*-ne Δ t)

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

eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (` i)         = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = clo ρ t 
eval ρ tt            = tt
eval ρ ze            = ze
eval ρ (su n)        = su (eval ρ n)
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

app-val (clo ρ t) u = eval (ρ , u) t
app-val (ne t) u    = reflect (t · reify u)

ℕ-rec-val z s ze     = z
ℕ-rec-val z s (su n) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (ne t) = reflect (ℕ-rec (reify z) (reify s) t)

reify {A = ⊤'}    tt        = tt
reify {A = ℕ'}    ze        = ze
reify {A = ℕ'}    (su n)    = su (reify n)
reify {A = A ⇒ B} (clo ρ t) = ƛ reify (eval (ρ ^ᴱ A) t)
reify {A = ⊤'}    (ne t)     = ne t
reify {A = ℕ'}    (ne t)     = ne t
reify {A = A ⇒ B} (ne t)     = ne t

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)
