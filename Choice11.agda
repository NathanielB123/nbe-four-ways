{-# OPTIONS --rewriting --local-confluence-check #-}

open import Syntax
open import Subst

module Choice11 where 

-- I don't know how to encode the 'Val'ues of 'Choice {1,1}' in Agda without
-- disabling positivity checking. Putting 'Val' in neutrals is quite cursed.
Val        : Ctx → Ty → Set
data NeVal : Ctx → Ty → Set

data ⊤Val (Γ : Ctx) : Set where
  tt : ⊤Val Γ
  ne : NeVal Γ ⊤' → ⊤Val Γ

data ℕVal (Γ : Ctx) : Set where
  ze : ℕVal Γ
  su : ℕVal Γ → ℕVal Γ
  ne : NeVal Γ ℕ' → ℕVal Γ

data ⇒Val (Γ : Ctx) (A B : Ty) (ValA ValB : Ctx → Set) : Set where
  lam : (∀ Δ → ValA (Γ ++ Δ) → ValB (Γ ++ Δ)) → ⇒Val Γ A B ValA ValB
  ne  : NeVal Γ (A ⇒ B) → ⇒Val Γ A B ValA ValB

Val Γ ⊤'      = ⊤Val Γ
Val Γ ℕ'      = ℕVal Γ
Val Γ (A ⇒ B) = ⇒Val Γ A B (λ Γ → Val Γ A) (λ Γ → Val Γ B)

{-# NO_POSITIVITY_CHECK #-}
data NeVal where
  `_    : Var Γ A → NeVal Γ A
  _·_   : NeVal Γ (A ⇒ B) → Val Γ A → NeVal Γ B
  ℕ-rec : Val Γ A → Val Γ (A ⇒ A) → NeVal Γ ℕ' → NeVal Γ A 

reflect : NeVal Γ A → Val Γ A
reflect {A = ⊤'}    = ne
reflect {A = ℕ'}    = ne
reflect {A = A ⇒ B} = ne 


wk*-val   : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-neval : ∀ Δ → NeVal Γ A → NeVal (Γ ++ Δ) A

wk*-val {A = ⊤'}    Δ tt      = tt
wk*-val {A = ℕ'}    Δ ze      = ze
wk*-val {A = ℕ'}    Δ (su n)  = su (wk*-val Δ n)
wk*-val {A = A ⇒ B} Δ (lam t) = lam λ Θ u → t (Δ ++ Θ) u
wk*-val {A = ⊤'}    Δ (ne t)  = ne (wk*-neval Δ t)
wk*-val {A = ℕ'}    Δ (ne t)  = ne (wk*-neval Δ t)
wk*-val {A = A ⇒ B} Δ (ne t)  = ne (wk*-neval Δ t)

wk*-neval Δ (` i)         = ` (i [ wk* Δ ])
wk*-neval Δ (t · u)       = wk*-neval Δ t · wk*-val Δ u
wk*-neval Δ (ℕ-rec z s n) = ℕ-rec (wk*-val Δ z) (wk*-val Δ s) (wk*-neval Δ n)

open import Env Val wk*-val (reflect (` vz))

app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
app-val (lam t) u = t ε u
app-val (ne  t) u = reflect (t · u)

ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

ℕ-rec-val z s ze     = z
ℕ-rec-val z s (su n) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (ne t) = reflect (ℕ-rec z s t)

eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (` i)         = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = lam (λ Δ u → eval (wk*-env Δ ρ , u) t)
eval ρ tt            = tt
eval ρ ze            = ze
eval ρ (su n)        = su (eval ρ n)
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

reify    : Val Γ A → Nf Γ A
reify-ne : NeVal Γ A → Ne Γ A

reify {A = ⊤'}    tt      = tt
reify {A = ℕ'}    ze      = ze
reify {A = ℕ'}    (su n)  = su (reify n)
reify {A = A ⇒ B} (lam t) = ƛ reify (t (ε , A) (reflect (` vz)))
reify {A = ⊤'}    (ne t)  = ne (reify-ne t)
reify {A = ℕ'}    (ne t)  = ne (reify-ne t)
reify {A = A ⇒ B} (ne t)  = ne (reify-ne t)

reify-ne (` i)         = ` i
reify-ne (t · u)       = reify-ne t · reify u
reify-ne (ℕ-rec z s n) = ℕ-rec (reify z) (reify s) (reify-ne n)

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)
