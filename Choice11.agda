{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import Subst

module Choice11 where 

-- I don't know how to encode the 'Val'ues of 'Choice {1,1}' in Agda without
-- disabling positivity checking. Putting 'Val' in neutrals is quite cursed.
Val        : Ctx → Ty → Set
PreVal     : Ctx → Ty → Set
data NeVal : Ctx → Ty → Set

ℕVal : Ctx → Set

data ℕPreVal (Γ : Ctx) : Set where
  ze  : ℕPreVal Γ
  su  : ℕVal Γ → ℕPreVal Γ

ℕVal Γ = ℕPreVal Γ ⊎ NeVal Γ ℕ'

PreVal Γ ⊤'      = ⊤
PreVal Γ ℕ'      = ℕPreVal Γ
PreVal Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

Val Γ A = PreVal Γ A ⊎ NeVal Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

{-# NO_POSITIVITY_CHECK #-}
data NeVal where
  `_    : Var Γ A → NeVal Γ A
  _·_   : NeVal Γ (A ⇒ B) → Val Γ A → NeVal Γ B
  ℕ-rec : Val Γ A → Val Γ (A ⇒ A) → NeVal Γ ℕ' → NeVal Γ A 

wk*-val   : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
wk*-neval : ∀ Δ → NeVal Γ A → NeVal (Γ ++ Δ) A

wk*-val             Δ (reflect t)  = reflect (wk*-neval Δ t)
wk*-val {A = ⊤'}    Δ (val tt)     = val tt
wk*-val {A = ℕ'}    Δ (val ze)     = val ze
wk*-val {A = ℕ'}    Δ (val (su n)) = val (su (wk*-val Δ n))
wk*-val {A = A ⇒ B} Δ (val t)      = val λ Θ u → t (Δ ++ Θ) u

wk*-neval Δ (` i)         = ` (i [ wk* Δ ])
wk*-neval Δ (t · u)       = wk*-neval Δ t · wk*-val Δ u
wk*-neval Δ (ℕ-rec z s n) = ℕ-rec (wk*-val Δ z) (wk*-val Δ s) (wk*-neval Δ n)

open import Env Val wk*-val (reflect (` vz))

app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
app-val (val t)     u = t ε u
app-val (reflect t) u = reflect (t · u)

ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

ℕ-rec-val z s (val ze)     = z
ℕ-rec-val z s (val (su n)) = app-val s (ℕ-rec-val z s n)
ℕ-rec-val z s (reflect t)  = reflect (ℕ-rec z s t)

eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
eval ρ (` i)         = eval ρ i
eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
eval ρ (t · u)       = app-val (eval ρ t) (eval ρ u)
eval ρ (ƛ t)         = val (λ Δ u → eval (wk*-env Δ ρ , u) t)
eval ρ tt            = val tt
eval ρ ze            = val ze
eval ρ (su n)        = val (su (eval ρ n))
eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

reify    : Val Γ A → Nf Γ A
reify-ne : NeVal Γ A → Ne Γ A

reify             (reflect t)  = ne (reify-ne t)
reify {A = ⊤'}    (val tt)     = tt
reify {A = ℕ'}    (val ze)     = ze
reify {A = ℕ'}    (val (su n)) = su (reify n)
reify {A = A ⇒ B} (val t)      = ƛ reify (t (ε , A) (reflect (` vz)))

reify-ne (` i)         = ` i
reify-ne (t · u)       = reify-ne t · reify u
reify-ne (ℕ-rec z s n) = ℕ-rec (reify z) (reify s) (reify-ne n)

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)
