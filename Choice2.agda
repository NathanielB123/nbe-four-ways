{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import Subst

module Choice2 where 

data ℕVal (Γ : Ctx) : Set where
  ze : ℕVal Γ
  su : ℕVal Γ → ℕVal Γ
  ne : Ne Γ ℕ' → ℕVal Γ

Val : Ctx → Ty → Set
-- Unlike Bowman's version, we rule out the possibility of 'Ne'utral '⊤'s. This
-- way, we enforce values are η-normal for '⊤' and '_⇒_'
Val Γ ⊤'      = ⊤
Val Γ ℕ'      = ℕVal Γ
-- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
-- a sequence of additional 'Var'iables which can be thrown onto the front
-- of the context
-- The original lisp code avoids this complexity by using named variables
Val Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A

wk*-val {A = ⊤'}    Δ tt     = tt
wk*-val {A = ℕ'}    Δ ze     = ze
wk*-val {A = ℕ'}    Δ (su n) = su (wk*-val Δ n)
wk*-val {A = A ⇒ B} Δ t Θ u  = t (Δ ++ Θ) u
wk*-val {A = ℕ'}    Δ (ne t) = ne (wk*-ne Δ t)

reify   : Val Γ A → Nf Γ A
reflect : Ne Γ A → Val Γ A

open import Env Val wk*-val (reflect (` vz))

eval      : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
ℕ-rec-val : Val Γ A → (Val Γ (A ⇒ A)) → Val Γ ℕ' → Val Γ A

eval ρ (` i)         = eval ρ i
eval (ρ , t) vz      = t
eval (ρ , t) (vs i)  = eval ρ i
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
reify {A = ℕ'}    ze     = ze
reify {A = ℕ'}    (su n) = su (reify n)
reify {A = ℕ'}    (ne n) = ne n
reify {A = A ⇒ B} t      = ƛ reify (t (ε , A) (reflect (` vz)))

reflect {A = ℕ'}    n     = ne n
-- η for '⊤'
reflect {A = ⊤'}    t     = tt
-- η for '_⇒_'
reflect {A = A ⇒ B} t Δ u = reflect (wk*-ne Δ t · reify u)

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)

module Example-Norm where
  open import Examples
  open Example-ChurchNats

  -- Now 'reify' and 'reflect' always block on the type, we have to instantiate
  -- with a concrete type (e.g. 'ℕ') to normalise a term
  test-Ctwo-ℕ : norm (Ctwo {Γ = Γ} {A = ℕ'}) 
              ≡ ƛ (ƛ ne (` vs vz · ne (` vs vz · ne (` vz))))
  test-Ctwo-ℕ = refl

  -- On the upside, blocking on the type means we can implement type-directed
  -- reductions; in other words, we can respect eta-equalities!
  test-Ctwo-⊤ : norm (Ctwo {Γ = Γ} {A = ⊤'}) 
              ≡ ƛ ƛ tt
  test-Ctwo-⊤ = refl

  open Example-Apply
  
  test-apply1 : norm (apply {Γ = Γ} {A = ℕ'} {B = ℕ'})
              ≡ ƛ (ƛ ne (` vs vz · ne (` vz)))
  test-apply1 = refl

  test-apply2 : norm (apply {Γ = Γ} {A = ℕ' ⇒ ℕ'} {B = ℕ' ⇒ ℕ'})
              ≡ ƛ ƛ ƛ ne (` vs (vs vz) · (ƛ ne (` vs (vs vz) 
                                       · ne (` vz))) · ne (` vz))
  test-apply2 = refl
   