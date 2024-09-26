module Utils where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥) public
open import Data.Product using (∃; _×_; proj₁; proj₂)
  renaming (_,_ to _Σ,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
  public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Nat using (ℕ) renaming (zero to ze; suc to su) public
