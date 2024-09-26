{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst

module Choice12 where 

data ⊤Val (Γ : Ctx) : Set where
  tt    : ⊤Val Γ
  ne    : Ne Γ ⊤' → ⊤Val Γ

data ℕVal (Γ : Ctx) : Set where
  ze  : ℕVal Γ
  su  : ℕVal Γ → ℕVal Γ
  ne  : Ne Γ ℕ' → ℕVal Γ

data ⇒Val (Γ : Ctx) (A B : Ty) (ValA ValB : Ctx → Set) : Set where
  lam : (∀ Δ → ValA (Γ ++ Δ) → ValB (Γ ++ Δ)) → ⇒Val Γ A B ValA ValB
  ne  : Ne Γ (A ⇒ B) → ⇒Val Γ A B ValA ValB

Val : Ctx → Ty → Set

Val Γ ⊤'      = ⊤Val Γ
Val Γ ℕ'      = ℕVal Γ
Val Γ (A ⇒ B) = ⇒Val Γ A B (λ Γ → Val Γ A) (λ Γ → Val Γ B)

reflect : Ne Γ A → Val Γ A
reflect {A = ⊤'}    = ne
reflect {A = ℕ'}    = ne
reflect {A = A ⇒ B} = ne

data Env (Δ : Ctx) : Ctx → Set where
  ε   : Env Δ ε
  _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

wk*-val {A = ⊤'}    Δ tt      = tt
wk*-val {A = ℕ'}    Δ ze      = ze
wk*-val {A = ℕ'}    Δ (su n)  = su (wk*-val Δ n)
wk*-val {A = A ⇒ B} Δ (lam t) = lam λ Θ u → t (Δ ++ Θ) u
wk*-val {A = ⊤'}    Δ (ne t)  = ne (wk*-ne Δ t)
wk*-val {A = ℕ'}    Δ (ne t)  = ne (wk*-ne Δ t)
wk*-val {A = A ⇒ B} Δ (ne t)  = ne (wk*-ne Δ t)

wk*-env Θ ε       = ε
wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
reify : Val Γ A → Nf Γ A

eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (` i)         = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = lam (λ Δ u → eval (wk*-env Δ ρ , u) t)
eval ρ tt            = tt
eval ρ ze            = ze
eval ρ (su n)        = su (eval ρ n)
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

ℕ-rec-val z s ze     = z
ℕ-rec-val z s (su n) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (ne t) = reflect (ℕ-rec (reify z) (reify s) t)

app-val (lam t) u = t ε u
app-val (ne  t) u = reflect (t · reify u)

reify {A = ⊤'}    tt      = tt
reify {A = ℕ'}    ze      = ze
reify {A = ℕ'}    (su n)  = su (reify n)
reify {A = A ⇒ B} (lam t) = ƛ reify (t (ε , A) (reflect (` vz)))
reify {A = ⊤'}    (ne t)  = ne t
reify {A = ℕ'}    (ne t)  = ne t
reify {A = A ⇒ B} (ne t)  = ne t
