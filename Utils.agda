module Utils where

open import Level using (Level) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥) public
open import Data.Product using (∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; dcong₂; subst; sym)
  renaming (trans to infixr 4 _∙_)
  public
open import Data.Bool using (Bool; true; false) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Nat using (ℕ) renaming (zero to ze; suc to su) public

variable
  ℓ : Level

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B 
        → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

infix 4 _≡[_]≡_
