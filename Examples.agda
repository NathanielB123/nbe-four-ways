{-# OPTIONS --rewriting --local-confluence-check #-}

open import Utils
open import Syntax
open import Subst

module Examples where

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

module Example-ChurchNats where
  Cℕ : Ty → Ty
  Cℕ A = (A ⇒ A) ⇒ A ⇒ A

  Czero : Tm Γ (Cℕ A)
  Czero = ⌜ ƛ2 (λ s z → `0 z) ⌝

  Csuc : Tm Γ (Cℕ A ⇒ Cℕ A) 
  Csuc = ⌜ ƛ3 (λ n s z → (`1 s · (`2 n · `1 s · `0 z))) ⌝

  C+ : Tm Γ (Cℕ A ⇒ Cℕ A ⇒ Cℕ A)
  C+ = ⌜ ƛ4 (λ x y s z → (`3 x · `1 s) · (`2 y · `1 s · `0 z)) ⌝

  Ctwo : Tm Γ (Cℕ A)
  Ctwo = C+ · (Csuc · Czero)  · (Csuc · Czero)

module Example-Apply where
  apply : Tm Γ ((A ⇒ B) ⇒ A ⇒ B)
  apply = ⌜ ƛ2 (λ f g → `1 f · `0 g) ⌝
