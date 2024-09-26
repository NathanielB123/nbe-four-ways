open import Utils

-- If we only include type formers for which η is easy (e.g. '⊤', '_⇒_') we can
-- actually define 'eval' and 'reify' without adding 'Var'iables/'Ne'utrals to
-- to 'Val'ues. 
-- Of course, this is cheating. In this restricted language, we can trivially 
-- build the unique normal form term of any type, 'A', by recursion on 'A' 
-- alone.

module ExtremeEta where

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
  _⇒_ : Ty → Ty → Ty

data Tm[_] where
  vz    : Var (Γ , A) A
  vs    : Var Γ B → Var (Γ , A) B
  
  `_    : Var Γ A → Tm Γ A
  _·_   : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ƛ_    : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  
  tt    : Tm Γ ⊤'

tm⊑ : Tm[ q ] Γ A → Tm Γ A
tm⊑ {q = V} i = ` i
tm⊑ {q = T} t = t

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  `_    : Var Γ A → Ne Γ A
  _·_   : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  ne  : Ne Γ A → Nf Γ A
  ƛ_  : Nf (Γ , A) B → Nf Γ (A ⇒ B)
  tt  : Nf Γ ⊤'

Val : Ty → Set
Val ⊤'      = ⊤
Val (A ⇒ B) = (Val A → Val B)

data Env : Ctx → Set where
  ε   : Env ε
  _,_ : Env Γ → Val A → Env (Γ , A)

eval : Env Γ → Tm[ q ] Γ A → Val A
eval (ρ , t) vz     = t
eval (ρ , t) (vs i) = eval ρ i
eval ρ (` i)        = eval ρ i
eval ρ (t · u)      = (eval ρ t) (eval ρ u)
eval ρ (ƛ t) u      = eval (ρ , u) t
eval ρ tt           = tt

reify   : Val A → Nf Γ A
reflect : Ne Γ A → Val A 

reify {A = ⊤'}    tt     = tt
reify {A = A ⇒ B} t      = ƛ reify (t (reflect (` vz {Γ = ε})))

reflect {A = ⊤'}    t   = tt
reflect {A = A ⇒ B} t u = reflect (t · reify u)

idᴱ : Env Γ
idᴱ {Γ = ε}     = ε
-- We don't even need to weaken the 'Env'ironment on the LHS here because
-- weakening on our 'Val'ues is a no-op
idᴱ {Γ = Γ , A} = idᴱ , reflect (` vz {Γ = ε})

norm : Tm Γ A → Nf Γ A
norm t = reify (eval idᴱ t)

module Example where
  foo : Tm Γ (A ⇒ A)
  foo = (ƛ ` vz) · (ƛ ` vz)

  foo-norm : norm (foo {Γ = Γ} {A = ⊤'}) ≡ ƛ tt
  foo-norm = refl

  foo-norm2 : norm (foo {Γ = Γ} {A = ⊤' ⇒ ⊤'}) ≡ ƛ (ƛ tt)
  foo-norm2 = refl

-- As mentioned at the start, this isn't as interesting a result as it might
-- initially look. Here's a normaliser that doesn't even use the 'Tm' it is 
-- given!
trivial-norm : Tm Γ A → Nf Γ A
trivial-norm _ = build-nf _
  where build-nf : ∀ A → Nf Γ A
        build-nf ⊤'      = tt
        build-nf (A ⇒ B) = ƛ (build-nf B)
