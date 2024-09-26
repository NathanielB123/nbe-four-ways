open import Utils

module Syntax where

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
