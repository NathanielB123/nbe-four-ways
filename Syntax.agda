{-# OPTIONS --rewriting --local-confluence-check #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

module Syntax where

-- TODO: Think about fixities
infixr 5 _⇒_
-- infix   3  _⊢[_]_
-- infix   3  _⊨[_]_
infixl  4  _,_
-- infix   5  _∘_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_
-- infix   8  _^_
-- infix   8  _⁺_
-- infix   8  _[_]

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
  o   : Ty
  _⇒_ : Ty → Ty → Ty

data Tm[_] where
  vz  : Var (Γ , A) A
  vs  : Var Γ B → Var (Γ , A) B
  `_  : Var Γ A → Tm Γ A
  _·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ_  : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  tt  : Tm Γ o

tm⊑ : Tm[ q ] Γ A → Tm Γ A
tm⊑ {q = V} i = ` i
tm⊑ {q = T} t = t

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  `_  : Var Γ A → Ne Γ A
  _·_ : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
  tt  : Ne Γ o

data Nf where
  ne  : Ne Γ A → Nf Γ A
  ƛ_  : Nf (Γ , A) B → Nf Γ (A ⇒ B)

module Examples1 where
  church-zero : Tm Γ (A ⇒ B ⇒ B)
  church-zero = ƛ ƛ ` vz

  church-add-1 : Tm Γ (((A ⇒ C) ⇒ (B ⇒ A)) ⇒ (A ⇒ C) ⇒ B ⇒ C)
  church-add-1 = ƛ ƛ ƛ (` vs vz · ((` vs (vs vz) · ` vs vz) · ` vz))

-- De Bruijn indices are ugly. We define a shorthand based on PHOAS...
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
  ℕ : Ty → Ty
  ℕ A = (A ⇒ A) ⇒ A ⇒ A

  zero : Tm Γ (ℕ A)
  zero = ⌜ ƛ2 (λ s z → `0 z) ⌝

  suc : Tm Γ (ℕ A ⇒ ℕ A) 
  suc = ⌜ ƛ3 (λ n s z → (`1 s · (`2 n · `1 s · `0 z))) ⌝

  + : Tm Γ (ℕ A ⇒ ℕ A ⇒ ℕ A)
  + = ⌜ ƛ4 (λ x y s z → (`3 x · `1 s) · (`2 y · `1 s · `0 z)) ⌝

-- As a last step before we get on to normalisation, we need to derive 
-- substitutions. Technically, we only *really* need weakening, but we might as
-- well define substitutions in their full generality!
-- Thorsten Altenkirch originally came up with the trick that lets us do this.
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

  vz      [ δ , t ] = t
  vs i    [ δ , t ] = i [ δ ]
  (` i)   [ δ ]     = tm⊑ (i [ δ ])
  (t · u) [ δ ]     = t [ δ ] · u [ δ ]
  (ƛ t)   [ δ ]     = ƛ (t [ δ ^ _ ])
  tt      [ δ ]     = tt

  wk* : ∀ Δ → Vars (Γ ++ Δ) Γ
  wk* ε       = id
  wk* (Δ , A) = wk* Δ ⁺

  _[_]ne : Ne Γ A → Vars Δ Γ → Ne Δ A
  _[_]nf : Nf Γ A → Vars Δ Γ → Nf Δ A

  (` i)   [ δ ]ne = ` (i [ δ ])
  (t · u) [ δ ]ne = t [ δ ]ne · u [ δ ]nf
  tt      [ δ ]ne = tt

  ne t  [ δ ]nf = ne (t [ δ ]ne)
  (ƛ t) [ δ ]nf = ƛ  (t [ δ ^ _ ]nf)

  wk*-ne  : ∀ Δ → Ne Γ B → Ne (Γ ++ Δ) B
  wk*-ne Δ t = t [ wk* Δ ]ne

open Substitution public

module Attempt1 where
  Val : Ty → Set
  Val o       = ⊤
  Val (A ⇒ B) = (Val A → Val B)

  data Env : Ctx → Set where
    ε   : Env ε
    _,_ : Env Γ → Val A → Env (Γ , A)

  eval : Env Γ → Tm[ q ] Γ A → Val A
  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ tt           = tt
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = (eval ρ t) (eval ρ u)
  eval ρ (ƛ t) u      = eval (ρ , u) t

  module Examples1-eval where
    open Examples1-PHOAS

    church-two : Val (ℕ A)
    church-two = eval ε (+ · (suc · zero)  · (suc · zero))

    test : church-two {A = A} ≡ λ s z → s (s z)
    test = refl

  -- Doesn't work!
  reify-1 : Val A → Nf Γ A
  reify-1 {A = o}     tt = ne tt
  reify-1 {A = A ⇒ B} t  = ƛ (reify-1 (t {!vz!}))


module Choice1-Attempt1 where
  Val    : Ctx → Ty → Set
  PreVal : Ctx → Ty → Set
  
  Val Γ A = PreVal Γ A ⊎ Var Γ A
  PreVal Γ o       = ⊤
  PreVal Γ (A ⇒ B) = Val Γ A → Val Γ B

  pattern var i = inj₂ i
  pattern val t = inj₁ t

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B

  eval : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)        = val λ u → eval (ρ , u) t
  eval ρ tt           = val tt

  -- Stuck again!
  app-val (val t) u = t u
  app-val (var i) u = {!!}

-- We start with 'Choice {1,2}' instead of 'Choice {1,1}' because it comes out
-- nicer in Agda
module Choice12 where
  Val    : Ctx → Ty → Set
  PreVal : Ctx → Ty → Set
  
  Val Γ A = PreVal Γ A ⊎ Ne Γ A
  PreVal Γ o       = ⊤
  -- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
  -- a sequence of additional variables which can be thrown onto the front
  -- of the context
  -- The original post avoids this complexity by using named variables
  PreVal Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

  pattern neu t = inj₂ t
  pattern val t = inj₁ t

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
  wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

  wk*-val {A = o}     Δ (val tt) = val tt
  wk*-val {A = A ⇒ B} Δ (val t)  = val λ Θ u → t (Δ ++ Θ) u
  wk*-val             Δ (neu t)  = neu (wk*-ne Δ t)

  wk*-env Θ ε       = ε
  wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

  app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  reify : Val Γ A → Nf Γ A

  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)        = val (λ Δ u → eval (wk*-env Δ ρ , u) t)
  eval ρ tt           = val tt

  app-val (val t) u = t ε u
  app-val (neu i) u = neu (i · reify u)

  reify {A = o}     (val t) = ne tt
  reify {A = A ⇒ B} (val t) = ƛ reify (t (ε , A) (neu (` vz)))
  reify             (neu t) = ne t


module Choice11 where
  -- I don't know how to encode the 'Val'ues of 'Choice {1,1}' in Agda without
  -- disabling positivity checking. Putting 'Val' in neutrals is quite cursed.
  Val        : Ctx → Ty → Set
  PreVal     : Ctx → Ty → Set
  data NeVal : Ctx → Ty → Set
  
  Val Γ A = PreVal Γ A ⊎ NeVal Γ A
  PreVal Γ o       = ⊤
  -- To enable weakening 'Val's, we need to parameterise the '_⇒_' case over
  -- a sequence of additional variables which can be thrown onto the front
  -- of the context
  -- The original post avoids this complexity by using named variables
  PreVal Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

  {-# NO_POSITIVITY_CHECK #-}
  data NeVal where
    `_  : Var Γ A → NeVal Γ A
    _·_ : NeVal Γ (A ⇒ B) → Val Γ A → NeVal Γ B
    tt  : NeVal Γ o

  pattern neu t = inj₂ t
  pattern val t = inj₁ t

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  wk*-val   : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
  wk*-neval : ∀ Δ → NeVal Γ A → NeVal (Γ ++ Δ) A
  wk*-env   : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

  wk*-val {A = o}     Δ (val tt) = val tt
  wk*-val {A = A ⇒ B} Δ (val t)  = val λ Θ u → t (Δ ++ Θ) u
  wk*-val             Δ (neu t)  = neu (wk*-neval Δ t)

  wk*-neval Δ (` i)   = ` (i [ wk* Δ ])
  wk*-neval Δ (t · u) = wk*-neval Δ t · wk*-val Δ u
  wk*-neval Δ tt      = tt

  wk*-env Θ ε       = ε
  wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

  app-val : Val Γ (A ⇒ B) → Val Γ A → Val Γ B
  eval  : Env Δ Γ → Tm[ q ] Γ A → Val Δ A

  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = app-val (eval ρ t) (eval ρ u)
  eval ρ (ƛ t)        = val (λ Δ u → eval (wk*-env Δ ρ , u) t)
  eval ρ tt           = val tt

  app-val (val t) u = t ε u
  app-val (neu i) u = neu (i · u)

  reify    : Val Γ A → Nf Γ A
  reify-ne : NeVal Γ A → Ne Γ A
  
  reify {A = o}     (val t) = ne tt
  reify {A = A ⇒ B} (val t) = ƛ reify (t (ε , A) (neu (` vz)))
  reify             (neu t) = ne (reify-ne t)

  reify-ne (` i)   = ` i
  reify-ne (t · u) = reify-ne t · reify u
  reify-ne tt      = tt


module Choice2 where
  Val : Ctx → Ty → Set
  Val Γ o       = ⊤ ⊎ Ne Γ o      
  Val Γ (A ⇒ B) = ∀ Δ → Val (Γ ++ Δ) A → Val (Γ ++ Δ) B

  pattern neu t  = inj₂ t
  pattern tt-val = inj₁ tt

  data Env (Δ : Ctx) : Ctx → Set where
    ε   : Env Δ ε
    _,_ : Env Δ Γ → Val Δ A → Env Δ (Γ , A)

  wk*-val  : ∀ Δ → Val Γ A → Val (Γ ++ Δ) A
  wk*-env  : ∀ Θ → Env Δ Γ → Env (Δ ++ Θ) Γ

  wk*-val {A = o}     Δ tt-val  = tt-val
  wk*-val {A = o}     Δ (neu t) = neu (wk*-ne Δ t)
  wk*-val {A = A ⇒ B} Δ t Θ u   = t (Δ ++ Θ) u

  wk*-env Θ ε       = ε
  wk*-env Θ (ρ , t) = wk*-env Θ ρ , wk*-val Θ t

  eval : Env Δ Γ → Tm[ q ] Γ A → Val Δ A
  eval (ρ , t) vz     = t
  eval (ρ , t) (vs i) = eval ρ i
  eval ρ (` i)        = eval ρ i
  eval ρ (t · u)      = (eval ρ t) ε (eval ρ u)
  eval ρ (ƛ t)        = λ Δ u → eval (wk*-env Δ ρ , u) t
  eval ρ tt           = tt-val

  reify   : Val Γ A → Nf Γ A
  reflect : Ne Γ A → Val Γ A

  reify {A = o} tt-val  = ne tt
  reify {A = o} (neu t) = ne t
  reify {A = A ⇒ B} t   = ƛ (reify (t (ε , A) (reflect (` vz))))

  reflect {A = o}     t     = neu t
  reflect {A = A ⇒ B} t Δ u = reflect (wk*-ne Δ t · reify u)
