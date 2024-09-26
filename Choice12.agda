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
-- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
-- a sequence of additional 'Var'iables which can be thrown onto the front
-- of the context
-- The original lisp code avoids this complexity by using named variables
PreVal Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

Val Γ A = PreVal Γ A ⊎ Ne Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A

wk*-val             Δ (reflect t)  = reflect (wk*-ne Δ t)
wk*-val {A = ⊤'}    Δ (val tt)     = val tt
wk*-val {A = ℕ'}    Δ (val ze)     = val ze
wk*-val {A = ℕ'}    Δ (val (su n)) = val (su (wk*-val Δ n))
wk*-val {A = A ⇒ B} Δ (val t)      = val λ Θ u → t (Δ ++ Θ) u

open import Env Val wk*-val (reflect (` vz))

app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
reify : Val Γ A → Nf Γ A

eval ρ (` i)         = eval ρ i
eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = val (λ Δ u → eval (wk*-env Δ ρ , u) t)
eval ρ tt            = val tt
eval ρ ze            = val ze
eval ρ (su n)        = val (su (eval ρ n))
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

ℕ-rec-val z s (val ze)     = z
ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (reflect t)  = reflect (ℕ-rec (reify z) (reify s) t)

app-val (val t)     u = t ε u
app-val (reflect t) u = reflect (t · reify u)

reify             (reflect t)  = ne t
reify {A = ⊤'}    (val tt)     = tt
reify {A = ℕ'}    (val ze)     = ze
reify {A = ℕ'}    (val (su n)) = su (reify n)
reify {A = A ⇒ B} (val t)      = ƛ reify (t (ε , A) (reflect (` vz)))

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)

module Example-Norm where
  open import Examples
  open Example-ChurchNats

  test-Ctwo : norm (Ctwo {Γ = Γ} {A = A}) 
            ≡ ƛ (ƛ ne (` vs vz · ne (` vs vz · ne (` vz))))
  test-Ctwo = refl
