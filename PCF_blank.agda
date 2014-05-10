module PCF_blank where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product hiding (map)
open import Data.Sum
open import Data.List
open import Data.List.Any hiding (map)
open Data.List.Any.Membership-≡
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Relation.Nullary using (¬_; yes; no)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

Name : Set
Name = String

-- raw terms (typeless) 
data Term : Set where
  var : Name → Term
  ƛ : Name → Term → Term
  _·_ : Term → Term → Term
  Y : Name → Term → Term
  zero : Term 
  suc : Term → Term
  ifz : Term → Term → Name → Term → Term

open import Assoc

Cxt : Set
Cxt = Assoc Name Type

infixl 0 _⊢_∶_

-- Typing rules for PCF
data _⊢_∶_ : Cxt → Term → Type → Set where
  var : ∀ {Γ x τ}
        → DomDist Γ
        → (x , τ) ∈ Γ → Γ ⊢ var x ∶ τ
  ƛ : ∀ {Γ x σ e τ}
      → (x , σ) ∷ Γ ⊢ e ∶ τ
      → Γ ⊢ (ƛ x e) ∶ (σ ⇒ τ)
  _·_ : ∀ {Γ e₁ e₂ σ τ}
        → Γ ⊢ e₁ ∶ (σ ⇒ τ) 
        → Γ ⊢ e₂ ∶ σ
        → Γ ⊢ (e₁ · e₂) ∶ τ
  Y : ∀ {Γ x e σ}
      → (x , σ) ∷ Γ ⊢ e ∶ σ
      → Γ ⊢ Y x e ∶ σ
  zero : ∀ {Γ}
         → DomDist Γ
         → Γ ⊢ zero ∶ nat
  suc : ∀ {Γ e}
        → Γ ⊢ e ∶ nat
        → Γ ⊢ suc e ∶ nat
  ifz : ∀ {Γ e e₀ n e₁ τ}
        → Γ ⊢ e ∶ nat
        → Γ ⊢ e₀ ∶ τ
        → (n , nat) ∷ Γ ⊢ e₁ ∶ τ
        → Γ ⊢ ifz e e₀ n e₁ ∶ τ

-- substitution 
[_/_] : Term → Name → Term → Term
[ f / x ] (var y) with x ≟S y
... | yes _ = f
... | no  _ = var y
[ f / x ] (ƛ y e) with x ≟S y
... | yes _ = ƛ y e
... | no  _ = ƛ y ([ f / x ] e)
[ f / x ] (e₁ · e₂) = [ f / x ] e₁ · [ f / x ] e₂
[ f / x ] (Y y e) with x ≟S y
... | yes _ = (Y y e)
... | no  _ = (Y y ([ f / x ] e))
[ f / x ] zero  = zero
[ f / x ] (suc e) = suc ([ f / x ] e) 
[ f / x ] (ifz e e₁ y e₂) with x ≟S y
... | yes _ = ifz e e₁ y e₂
... | no  _ =
  ifz ([ f / x ] e) ([ f / x ] e₁) y ([ f / x ] e₂) 

-- closed values
data Val : Term → Set where
  zero : Val zero
  suc  : ∀ {n} → Val n → Val (suc n)
  lam  : ∀ {x e} → Val (ƛ x e)

-- Small-step semantics

infixr 2 _⟼_
data _⟼_ : Term → Term → Set where
  suc  : ∀ {e₁ e₂}
          → e₁ ⟼ e₂ → suc e₁ ⟼ suc e₂ 
  appL : ∀ {e₁ e₁' e₂}
          → e₁ ⟼ e₁'
          → e₁ · e₂ ⟼ e₁' · e₂
  ifz : ∀ {e e' e₀ n e₁}
        → e ⟼ e'
        → ifz e e₀ n e₁ ⟼ ifz e' e₀ n e₁
  app : ∀ {x e₁ e₂}
        → (ƛ x e₁) · e₂ ⟼ [ e₂ / x ] e₁
  ifz₀ : ∀ {e₀ e₁ n}
        → ifz zero e₀ n e₁ ⟼ e₀
  ifz₁ : ∀ {n e₀ x e₁} → Val (suc n)
        → ifz (suc n) e₀ x e₁ ⟼ [ n / x ] e₁
  Y : ∀ {x e}
      → Y x e ⟼ [ (Y x e) / x ] e 

-- Well-typed terms don't get stuck! 
progress : ∀ {e : Term} {τ} → [] ⊢ e ∶ τ
             → Val e ⊎ (∃ λ e' → e ⟼ e')
progress = ?

postulate
 ⊢-weaken : ∀ Γ x τ Δ {e σ}
            → x ∉ dom Γ → x ∉ dom Δ
            → Γ ++ Δ ⊢ e ∶ σ
            → Γ ++ [(x , τ)] ++ Δ ⊢ e ∶ σ

⊢-DD : ∀ Γ {e σ} → Γ ⊢ e ∶ σ → DomDist Γ
⊢-DD = ?

⊢-subst : ∀ Γ x τ Δ {e t σ}
          → (Γ ++ [(x , τ)] ++ Δ ⊢ e ∶ σ)
          → (Γ ++ Δ ⊢ t ∶ τ)
          → Γ ++ Δ ⊢ [ t / x ] e ∶ σ
⊢-subst = ?

preservation : ∀ {e e' : Term} {τ}
               → [] ⊢ e ∶ τ 
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
preservation = ?

-- big step semantics 
data _⇓_ : Term → Term → Set where
  zero : zero ⇓ zero
  suc  : ∀ {t n} → t ⇓ n → suc t ⇓ suc n
  Y  : ∀ {x e v} → [(Y x e) / x ] e ⇓ v → Y x e ⇓ v
  lam  : ∀ {x e} → (ƛ x e) ⇓ (ƛ x e)
  app  : ∀ {t x e n v} → t ⇓ (ƛ x e) → [ n / x ] e ⇓ v → (t · n) ⇓ v
  ifz₀ : ∀ {t t₀ n t₁ v} → t ⇓ zero → t₀ ⇓ v → ifz t t₀ n t₁ ⇓ v
  ifz₁ : ∀ {t n t₀ x t₁ v} → t ⇓ suc n → [ n / x ] t₁ ⇓ v → ifz t t₀ x t₁ ⇓ v

-- if t ⇓ v then v is a closed value. 
⇓-Val : ∀ {t v} → t ⇓ v → Val v
⇓-Val = ?

-- every closed value v can be reduced to itself by ⇓ 
v⇓v : ∀ {v} → Val v → v ⇓ v
v⇓v = ?

-- many step reduction relation
infixr 2 _⟼*_

data _⟼*_ : Term → Term → Set where
  refl  : ∀ {t} → t ⟼* t
  trans : ∀ {t u v} → t ⟼ u → u ⟼* v → t ⟼* v

-- ⟼* is reflexive by construction
-- also it is transitive 
⟼*-trans : ∀ {t u v} → t ⟼* u → u ⟼* v → t ⟼* v
⟼*-trans refl d₂ = d₂
⟼*-trans (trans x d₁) d₂ = trans x (⟼*-trans d₁ d₂)

⟼*-suc : ∀ {t u} → t ⟼* u → suc t ⟼* suc u
⟼*-suc refl = refl
⟼*-suc (trans x d) = trans (suc x) (⟼*-suc d)

⟼*-app : ∀ {t u v} → (t ⟼* u) → t · v ⟼* u · v
⟼*-app refl = refl
⟼*-app (trans x d) = trans (appL x) (⟼*-app d)

⟼*-ifz : ∀ {t u t₀ x t₁} → t ⟼* u → ifz t t₀ x t₁ ⟼* ifz u t₀ x t₁
⟼*-ifz refl = refl
⟼*-ifz (trans x d) = trans (ifz x) (⟼*-ifz d)

-- the agreement of small-step and big-step semantics
⇓to⟼* : ∀ {t u} → t ⇓ u → t ⟼* u
⇓to⟼* = ?

⟼⇓to⇓ : ∀ {t u v} → t ⟼ u → u ⇓ v → t ⇓ v
⟼⇓to⇓ = ?

⟼*⇓to⇓ : ∀ {t u v} → t ⟼* u → u ⇓ v → t ⇓ v
⟼*⇓to⇓ = ?

⟼*to⇓ : ∀ {t v} → t ⟼* v → Val v → t ⇓ v
⟼*to⇓ d val = ?