{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)

module NbE where

infixr 5 _⇒_
infixl  4  _,_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_

data Sort : Set where
  V   : Sort
  T>V : ∀ v → v ≡ V → Sort

pattern T = T>V V refl

_⊔_ : Sort → Sort → Sort
T ⊔ q = T
V ⊔ q = q

data Ctx : Set
data Ty  : Set
data Tm[_] : Sort → Ctx → Ty → Set
Var = Tm[ V ]
Tm  = Tm[ T ]

variable
  q r s : Sort
  Γ Δ Θ Ξ : Ctx
  A B C D E : Ty
  i j k : Var Γ A
  t u v : Tm Γ A
  x y z : Tm[ q ] Γ A

data Ctx where
  ε   : Ctx
  _,_ : Ctx → Ty → Ctx

data Ty where
  ⊤'  : Ty
  ℕ'  : Ty 
  _⇒_ : Ty → Ty → Ty

data Tm[_] where
  vz    : Var (Γ , A) A
  vs    : Var Γ B → Var (Γ , A) B
  
  `_    : Var Γ A → Tm Γ A
  _·_   : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ_    : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  
  tt    : Tm Γ ⊤'
  
  ze    : Tm Γ ℕ'
  su    : Tm Γ ℕ' → Tm Γ ℕ'
  ℕ-rec : Tm Γ A → Tm Γ (A ⇒ A) → Tm Γ ℕ' → Tm Γ A

tm⊑ : Tm[ q ] Γ A → Tm Γ A
tm⊑ {q = V} i = ` i
tm⊑ {q = T} t = t

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  `_    : Var Γ A → Ne Γ A
  _·_   : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  
  ℕ-rec : Nf Γ A → Nf Γ (A ⇒ A) → Ne Γ ℕ' → Ne Γ A 

data Nf where
  ne  : Ne Γ A → Nf Γ A
  ƛ_  : Nf (Γ , A) B → Nf Γ (A ⇒ B)
  
  -- We could get away with putting 'tt' in 'Ne'utrals given there is no 
  -- recursor, but this feels more consistent
  tt  : Nf Γ ⊤'
  
  ze  : Nf Γ ℕ'
  su  : Nf Γ ℕ' → Nf Γ ℕ'

module Examples1 where
  church-zero : Tm Γ (A ⇒ B ⇒ B)
  church-zero = ƛ ƛ ` vz

  church-add-1 : Tm Γ (((A ⇒ C) ⇒ (B ⇒ A)) ⇒ (A ⇒ C) ⇒ B ⇒ C)
  church-add-1 = ƛ ƛ ƛ (` vs vz · ((` vs (vs vz) · ` vs vz) · ` vz))

-- De Bruijn indices are ugly. We define a more readable syntax based on PHOAS.
_++_ : Ctx → Ctx → Ctx
Γ ++ ε       = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

++-assoc : Γ ++ (Δ ++ Θ) ≡ (Γ ++ Δ) ++ Θ
++-assoc {Θ = ε}     = refl
++-assoc {Θ = Θ , A} = cong₂ _,_ (++-assoc {Θ = Θ}) refl

{-# REWRITE ++-assoc #-}

vs* : ∀ Δ → Var Γ A → Var (Γ ++ Δ) A
vs* ε i       = i
vs* (Δ , B) i = vs (vs* Δ i)

-- Context-indexed PHOAS. Just so we can name the variables in our examples
-- Indexing by context lets us easily convert into de Bruijn terms (by 
-- structural recursion)
-- TODO: Add 'tt', 'ze', 'su' and 'ℕ-rec' to this syntax.
data PHOAS (V : Ctx → Ty → Set) : Ctx → Ty → Set where
  `_  : V Γ A → PHOAS V (Γ ++ Δ) A
  ƛ_  : (V (Γ , A) A → PHOAS V (Γ , A) B) → PHOAS V Γ (A ⇒ B)
  _·_ : PHOAS V Γ (A ⇒ B) → PHOAS V Γ A → PHOAS V Γ B

module _ {V : Ctx → Ty → Set} where
  `0_ : V Γ A → PHOAS V Γ A
  `0_ = `_ {Δ = ε}

  `1_ : V Γ B → PHOAS V (Γ , A) B
  `1_ = `_ {Δ = ε , _}

  `2_ : V Γ C → PHOAS V (Γ , A , B) C
  `2_ = `_ {Δ = ε , _ , _}

  `3_ : V Γ D → PHOAS V (Γ , A , B , C) D
  `3_ = `_ {Δ = ε , _ , _ , _}

  pattern `[_]_ Δ i = `_ {Δ = Δ} i 

  ƛ2_ : (V (Γ , A) A → V (Γ , A , B) B → PHOAS V (Γ , A , B) C) 
      → PHOAS V Γ (A ⇒ B ⇒ C)
  ƛ2 t = ƛ λ x → ƛ t x

  ƛ3_ : (V (Γ , A) A → V (Γ , A , B) B → V (Γ , A , B , C) C 
      → PHOAS V (Γ , A , B , C) D)
      → PHOAS V Γ (A ⇒ B ⇒ C ⇒ D)
  ƛ3 t = ƛ2 λ x y → ƛ t x y

  ƛ4_ : (V (Γ , A) A → V (Γ , A , B) B → V (Γ , A , B , C) C
      → V (Γ , A , B , C , D) D → PHOAS V (Γ , A , B , C , D) E)
      → PHOAS V Γ (A ⇒ B ⇒ C ⇒ D ⇒ E)
  ƛ4 t = ƛ3 λ x y z → ƛ t x y z

⌜_⌝ : PHOAS Var Γ A → Tm Γ A
⌜ `[ Δ ] i ⌝ = ` (vs* Δ i)
⌜ ƛ t ⌝ = ƛ ⌜ t vz ⌝
⌜ t · u ⌝ = ⌜ t ⌝ · ⌜ u ⌝

module Examples1-PHOAS where
  Cℕ : Ty → Ty
  Cℕ A = (A ⇒ A) ⇒ A ⇒ A

  Czero : Tm Γ (Cℕ A)
  Czero = ⌜ ƛ2 (λ s z → `0 z) ⌝

  Csuc : Tm Γ (Cℕ A ⇒ Cℕ A) 
  Csuc = ⌜ ƛ3 (λ n s z → (`1 s · (`2 n · `1 s · `0 z))) ⌝

  C+ : Tm Γ (Cℕ A ⇒ Cℕ A ⇒ Cℕ A)
  C+ = ⌜ ƛ4 (λ x y s z → (`3 x · `1 s) · (`2 y · `1 s · `0 z)) ⌝

-- As a last step before we get on to normalisation, we need to derive 
-- substitutions. Technically, we only *really* need weakening, but we might as
-- well define substitutions in their full generality!
-- Thorsten Altenkirch originally came up with the trick that lets us do this
-- without copy and paste.
module Substitution where
  data Tms[_] (q : Sort) : Ctx → Ctx → Set where
    ε   : Tms[ q ] Δ ε
    _,_ : Tms[ q ] Δ Γ → Tm[ q ] Δ A → Tms[ q ] Δ (Γ , A)

  Vars = Tms[ V ]
  Tms  = Tms[ T ]

  vz[_] : ∀ q → Tm[ q ] (Γ , A) A
  vz[ V ] = vz
  vz[ T ] = ` vz


  suc[_] : ∀ q → Tm[ q ] Γ B → Tm[ q ] (Γ , A) B
  _⁺     : Tms[ q ] Δ Γ → Tms[ q ] (Δ , A) Γ
  _^_    : Tms[ q ] Δ Γ → ∀ A → Tms[ q ] (Δ , A) (Γ , A)
  _[_]   : Tm[ q ] Γ A → Tms[ s ] Δ Γ → Tm[ q ⊔ s ] Δ A 
  id[_]  : ∀ q → Tms[ q ] Γ Γ
  
  id     : Vars Γ Γ
  id = id[ V ]
  {-# INLINE id #-} 

  suc[ V ]   = vs
  suc[ T ] t = t [ id ⁺ ]
  
  ε ⁺       = ε
  (δ , t) ⁺ = δ ⁺ , suc[ _ ] t

  δ ^ A = δ ⁺ , vz[ _ ]

  id[_] {Γ = ε} _     = ε
  id[_] {Γ = Γ , A} _ = id[ _ ] ^ A

  vz          [ δ , t ] = t
  vs i        [ δ , t ] = i [ δ ]
  (` i)       [ δ ]     = tm⊑ (i [ δ ])
  (t · u)     [ δ ]     = t [ δ ] · u [ δ ]
  (ƛ t)       [ δ ]     = ƛ (t [ δ ^ _ ])
  tt          [ δ ]     = tt
  ze          [ δ ]     = ze
  su n        [ δ ]     = su (n [ δ ])
  ℕ-rec z s n [ δ ]     = ℕ-rec (z [ δ ]) (s [ δ ]) (n [ δ ])

  wk*[_] : ∀ q Δ → Tms[ q ] (Γ ++ Δ) Γ
  wk*[ q ] ε       = id[ q ]
  wk*[ q ] (Δ , A) = wk*[ q ] Δ ⁺

  wk* : ∀ Δ → Vars (Γ ++ Δ) Γ
  wk* = wk*[ V ]
  
  _[_]ne : Ne Γ A → Vars Δ Γ → Ne Δ A
  _[_]nf : Nf Γ A → Vars Δ Γ → Nf Δ A

  (` i)       [ δ ]ne = ` (i [ δ ])
  (t · u)     [ δ ]ne = t [ δ ]ne · u [ δ ]nf
  ℕ-rec z s n [ δ ]ne = ℕ-rec (z [ δ ]nf) (s [ δ ]nf) (n [ δ ]ne)

  ne t  [ δ ]nf = ne (t [ δ ]ne)
  (ƛ t) [ δ ]nf = ƛ  (t [ δ ^ _ ]nf)
  tt    [ δ ]nf = tt
  ze    [ δ ]nf = ze
  su n  [ δ ]nf = su (n [ δ ]nf)

  wk*-ne  : ∀ Δ → Ne Γ B → Ne (Γ ++ Δ) B
  wk*-ne Δ t = t [ wk* Δ ]ne

open Substitution public

module Attempt1 where
  -- We must define 'Val' recursively to satisfy Agda's positivity checking.
  -- This can be seen as a non-dependent version of a logical relation: i.e.
  -- we compute a predicate by recursion on types (only the predicate doesn't
  -- need to depend on the term, because we are not trying to prove stability/
  -- completeness... yet)
  Val : Ty → Set
  Val ⊤'      = ⊤
  Val ℕ'      = ℕ
  Val (A ⇒ B) = (Val A → Val B)

  data Env : Ctx → Set where
    ε   : Env ε
    _,_ : Env Γ → Val A → Env (Γ , A)

  ℕ-recurse : ∀ {A : Set} → A → (A → A) → ℕ → A
  ℕ-recurse z s zero    = z
  ℕ-recurse z s (suc n) = s (ℕ-recurse z s n)

  eval : Env Γ → Tm[ q ] Γ A → Val A
  eval (ρ , t) vz      = t
  eval (ρ , t) (vs i)  = eval ρ i
  eval ρ (` i)         = eval ρ i
  eval ρ (t · u)       = (eval ρ t) (eval ρ u)
  eval ρ (ƛ t) u       = eval (ρ , u) t
  eval ρ tt            = tt
  eval ρ ze            = zero
  eval ρ (su n)        = suc (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-recurse (eval ρ z) (eval ρ s) (eval ρ n)

  module Examples1-eval where
    open Examples1-PHOAS

    church-two : Val (Cℕ A)
    church-two = eval ε (C+ · (Csuc · Czero)  · (Csuc · Czero))

    test : church-two {A = A} ≡ λ s z → s (s z)
    test = refl

  -- Doesn't work! Var'iables are not 'Val'ues
  -- Though... if we stuck with just '⊤' and '_⇒_' type formers, I think we
  -- could actually implement a 'reflect : Ne Γ A → Val Γ A'. I'll give this
  -- a try in a bit...
  reify : Val A → Nf Γ A
  reify {A = ⊤'}    tt     = tt
  reify {A = ℕ'}    zero   = ze
  reify {A = ℕ'}   (suc n) = su (reify n)
  reify {A = A ⇒ B} t      = ƛ reify (t {!vz!})


module Choice1-Attempt1 where
  Val    : Ctx → Ty → Set
  PreVal : Ctx → Ty → Set
  
  Val Γ A = PreVal Γ A ⊎ Var Γ A
  PreVal Γ ⊤'      = ⊤
  PreVal Γ ℕ'      = ℕ
  PreVal Γ (A ⇒ B) = Val Γ A → Val Γ B

  pattern var i = inj₂ i
  pattern val t = inj₁ t

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  app-val   : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  suc-val   : Val Γ ℕ' → Val Γ ℕ'
  ℕ-rec-val : Val Γ A → Val Γ (A ⇒ A) → Val Γ ℕ' → Val Γ A

  eval : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)        = val λ u → eval (ρ , u) t
  eval ρ tt           = val tt
  eval ρ ze            = val zero
  eval ρ (su n)        = suc-val (eval ρ n)
  eval ρ (ℕ-rec z s n) = ℕ-rec-val (eval ρ z) (eval ρ s) (eval ρ n)

  -- Stuck again! 'Ne'utrals are *also* not 'Val'ues
  app-val (val t) u = t u
  app-val (var i) u = {!!}

  -- Also stuck implementing the 'ℕ' constructor/recursor on 'Val's. We need
  -- 'suc' to accept neutrals
  suc-val (val n) = val (suc n)
  suc-val (var i) = {!!}

  ℕ-rec-val z s (val zero)    = z
  ℕ-rec-val z s (val (suc n)) = app-val s (ℕ-rec-val z s (val n))
  ℕ-rec-val z s (var i) = {!!}


-- We start with 'Choice{2}' because it comes out much more nicely in Agda
module Choice2 where
  data ⊤Val (Γ : Ctx) : Set where
    tt : ⊤Val Γ
    -- We could remove the 'Ne'utral case here to get η for '⊤'
    -- In fact, whether we allow 'Ne'utral values for each type can be seen
    -- as a decision of whether we want η or not (though, I don't think it is
    -- possible to remove the 'Ne'utral case from 'ℕVal' and still implement
    -- 'reflect' - I am not sure what distinguishes the types for which η is
    -- easy)
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


module Choice11 where
  -- I don't know how to encode the 'Val'ues of 'Choice {1,1}' in Agda without
  -- disabling positivity checking. Putting 'Val' in neutrals is quite cursed.
  Val        : Ctx → Ty → Set
  data NeVal : Ctx → Ty → Set
  
  data ⊤Val (Γ : Ctx) : Set where
    tt    : ⊤Val Γ
    ne    : NeVal Γ ⊤' → ⊤Val Γ

  data ℕVal (Γ : Ctx) : Set where
    ze  : ℕVal Γ
    su  : ℕVal Γ → ℕVal Γ
    ne  : NeVal Γ ℕ' → ℕVal Γ

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

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  wk*-val   : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
  wk*-neval : ∀ Δ → NeVal Γ A → NeVal (Γ ++ Δ) A
  wk*-env   : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

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

  wk*-env Θ ε       = ε
  wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

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

  _^e_ : Env Δ Γ → ∀ A → Env (Δ , A) (Γ , A)
  ρ ^e A = wk*-env (ε , A) ρ , reflect (` vz)

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
  reify {A = A ⇒ B} (clo ρ t) = ƛ reify (eval (ρ ^e A) t)
  reify {A = ⊤'}    (ne t)     = ne t
  reify {A = ℕ'}    (ne t)     = ne t
  reify {A = A ⇒ B} (ne t)     = ne t
