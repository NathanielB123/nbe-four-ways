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
PreVal Γ (A ⇒ B) = ∀ {Δ} (δ : Vars Δ Γ) → Val Δ A → Val Δ B

Val Γ A = PreVal Γ A ⊎ NeVal Γ A

pattern val     t = inj₁ t
pattern reflect t = inj₂ t

{-# NO_POSITIVITY_CHECK #-}
data NeVal where
  `_    : Var Γ A → NeVal Γ A
  _·_   : NeVal Γ (A ⇒ B) → Val Γ A → NeVal Γ B
  ℕ-rec : Val Γ A → Val Γ (A ⇒ A) → NeVal Γ ℕ' → NeVal Γ A 

_∋_[_]val : ∀ A → Val Γ A → Vars Δ Γ → Val Δ A
_[_]neval : NeVal Γ A → Vars Δ Γ → NeVal Δ A

A       ∋ reflect t  [ δ ]val = reflect (t [ δ ]neval)
⊤'      ∋ val tt     [ δ ]val = val tt
ℕ'      ∋ val ze     [ δ ]val = val ze
ℕ'      ∋ val (su n) [ δ ]val = val (su (ℕ' ∋ n [ δ ]val))
(A ⇒ B) ∋ val t      [ δ ]val = val λ σ u → t (δ ⨾ σ) u

(` i)       [ δ ]neval = ` (i [ δ ])
(t · u)     [ δ ]neval = (t [ δ ]neval) · (_ ∋ u [ δ ]val)
ℕ-rec z s n [ δ ]neval = ℕ-rec (_ ∋ z [ δ ]val) (_ ∋ s [ δ ]val) (n [ δ ]neval)

open import Env Val (_ ∋_[_]val) (reflect (` vz))

app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
app-val (val t)     u = t id u
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
eval ρ (ƛ t)         = val (λ δ u → eval ((ρ [ δ ]env) , u) t)
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
reify {A = A ⇒ B} (val t)      = ƛ reify (t (id ⁺) (reflect (` vz)))

reify-ne (` i)         = ` i
reify-ne (t · u)       = reify-ne t · reify u
reify-ne (ℕ-rec z s n) = ℕ-rec (reify z) (reify s) (reify-ne n)

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)
