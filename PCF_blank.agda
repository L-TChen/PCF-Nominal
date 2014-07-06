module PCF_blank where

{-
  A formalisation of PCF in Agda 
    by Shin-Cheng Mu and Liang-Ting Chen

  Abstract. This files formalises Type Safety of PCF
  and the agreement of the big-step semantics and
  the one-step semantics.
-}

open import Data.Nat
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product hiding (map)
open import Data.Sum
open import Data.List
open import Data.List.Any hiding (map)
open Data.List.Any.Membership-≡
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Relation.Nullary using (¬_; yes; no)

open import Assoc 

Name : Set
Name = String

-- Term formation rules 
data Term : Set where
  var : Name → Term
  ƛ : Name → Term → Term
  _·_ : Term → Term → Term
  Y : Name → Term → Term
  zero : Term 
  suc : Term → Term
  ifz : Term → Term → Name → Term → Term

-- (simplified) substitution 
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

infixl 5 _·_

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

infixr 5 _⇒_

Cxt : Set
Cxt = List (Name × Type)

infixl 0 _⊢_∶_

-- Typing rules for PCF
data _⊢_∶_ : Cxt → Term → Type → Set where
  var : ∀ {Γ x τ}
        → (D : DomDist Γ)
        → (x∈Γ : (x , τ) ∈ Γ)
        ---------------------- (var)
        → Γ ⊢ var x ∶ τ

  ƛ : ∀ {Γ x σ e τ}
      → (x , σ) ∷ Γ ⊢ e ∶ τ
      ---------------------------- (abs)        
      → Γ ⊢ ƛ x e ∶ σ ⇒ τ

  _·_ : ∀ {Γ e₁ e₂ σ τ}
        → Γ ⊢ e₁ ∶ σ ⇒ τ 
        → Γ ⊢ e₂ ∶ σ
      ------------------------ (app)
        → Γ ⊢ e₁ · e₂ ∶ τ

  Y : ∀ {Γ x e σ}
      → (x , σ) ∷ Γ ⊢ e ∶ σ
      ---------------------------- (Y)
      → Γ ⊢ Y x e ∶ σ

  zero : ∀ {Γ}
         → (D : DomDist Γ)
        ------------------- (z)
         → Γ ⊢ zero ∶ nat

  suc : ∀ {Γ e}
        → Γ ⊢ e ∶ nat
        -------------------- (s)
        → Γ ⊢ suc e ∶ nat

  ifz : ∀ {Γ e e₀ n e₁ τ}
        → Γ ⊢ e ∶ nat
        → Γ ⊢ e₀ ∶ τ
        → (n , nat) ∷ Γ ⊢ e₁ ∶ τ
        ------------------------ (ifz)
        → Γ ⊢ ifz e e₀ n e₁ ∶ τ

-- Values
data Val : Term → Set where
  zero : 
        ----------
         Val zero

  suc  : ∀ {n}
         → Val n
        ----------
         → Val (suc n)

  lam  : ∀ {x e} → 
        ----------
         Val (ƛ x e)

-- Small-step semantics

infixr 2 _⟼_
data _⟼_ : Term → Term → Set where
  suc  : ∀ {e₁ e₂}
          → e₁ ⟼ e₂ 
          → suc e₁ ⟼ suc e₂ 

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
progress : ∀ {e τ} 
           → [] ⊢ e ∶ τ
           → Val e ⊎ (∃ λ e' → e ⟼ e')
progress = {!!}

-- Beginning of Substitution Lemma 
postulate 
  ⊢-weaken : ∀ Γ x τ Δ {e σ}
             → x ∉ dom Γ → x ∉ dom Δ
             → Γ ++ Δ ⊢ e ∶ σ
             → Γ ++ [(x , τ)] ++ Δ ⊢ e ∶ σ

⊢-DD : ∀ Γ {e σ} → Γ ⊢ e ∶ σ → DomDist Γ
⊢-DD Γ (var DD _) = DD
⊢-DD Γ (ƛ ⊢e) with ⊢-DD _ ⊢e
... | x∉ ∷ DD = DD
⊢-DD Γ (⊢e · ⊢e₁) = ⊢-DD Γ ⊢e
⊢-DD Γ (Y ⊢e) with ⊢-DD _ ⊢e
... | x∉ ∷ DD = DD
⊢-DD Γ (zero DD) = DD
⊢-DD Γ (suc ⊢e) = ⊢-DD Γ ⊢e
⊢-DD Γ (ifz ⊢e ⊢e₁ ⊢e₂) = ⊢-DD Γ ⊢e

⊢-subst : ∀ Γ x τ Δ {e t σ}
          → (Γ ++ [(x , τ)] ++ Δ ⊢ e ∶ σ)
          → (Γ ++ Δ ⊢ t ∶ τ)
          → Γ ++ Δ ⊢ [ t / x ] e ∶ σ
⊢-subst Γ x τ Δ (var .{_} {y} {σ} D y∈) ⊢t with x ≟S y
... | yes x≡y rewrite x≡y | assoc-≡ Γ y Δ D y∈ = ⊢t
... | no  x≢y = var (assoc-rm Γ x Δ D) (assoc-≠ Γ x Δ y D x≢y y∈)
⊢-subst Γ x τ Δ (Y .{_} {y} {e} {σ} ⊢e) ⊢t with x ≟S y
... | yes x≡y rewrite x≡y = ⊥-elim (DomDist-nodup Γ y σ τ Δ (⊢-DD _ ⊢e))
... | no  x≢y = Y (⊢-subst ((y , σ) ∷ Γ) x τ Δ {e} {_} {σ} ⊢e
  (⊢-weaken [] y σ (Γ ++ Δ) (λ ()) y∉ ⊢t))
  where y∉ : y ∉ dom (Γ ++ Δ)
        y∉ with assoc-rm ((y , σ) ∷ Γ) x Δ (⊢-DD _ ⊢e) 
        ... | y∉ ∷ _ = y∉
⊢-subst Γ x τ Δ (ƛ .{_} {y} {σ} {e} {ρ} ⊢e) ⊢t with x ≟S y
... | yes x≡y rewrite x≡y = ⊥-elim (DomDist-nodup Γ y σ τ Δ (⊢-DD _ ⊢e))
... | no  x≢y = ƛ (⊢-subst ((y , σ) ∷ Γ) x τ Δ ⊢e 
                  (⊢-weaken [] y σ (Γ ++ Δ) (λ ()) y∉ ⊢t))
  where y∉ : y ∉ dom (Γ ++ Δ)
        y∉ with assoc-rm ((y , σ) ∷ Γ) x Δ (⊢-DD _ ⊢e) 
        ... | y∉ ∷ _ = y∉
⊢-subst Γ x τ Δ (ifz .{_} {e} {e₀} {n} {e₁} ⊢e ⊢e₀ ⊢e₁) ⊢t with x ≟S n
... | yes x≡n rewrite x≡n = ⊥-elim (DomDist-nodup Γ n nat τ Δ (⊢-DD _ ⊢e₁))
... | no  x≢n = ifz
  (⊢-subst Γ x τ Δ ⊢e ⊢t)
  (⊢-subst Γ x τ Δ ⊢e₀ ⊢t)
  (⊢-subst ((n , nat) ∷ Γ) x τ Δ ⊢e₁
    (⊢-weaken [] n nat (Γ ++ Δ) (λ ()) n∉ ⊢t))
  where n∉ : n ∉ dom (Γ ++ Δ)
        n∉ with assoc-rm ((n , nat) ∷ Γ) x Δ (⊢-DD _ ⊢e₁) 
        ... | y∉ ∷ _ = y∉
⊢-subst Γ x τ Δ (⊢e₁ · ⊢e₂) ⊢t =
  ⊢-subst Γ x τ Δ ⊢e₁ ⊢t · ⊢-subst Γ x τ Δ ⊢e₂ ⊢t
⊢-subst Γ x τ Δ (zero y) ⊢t = zero (⊢-DD _ ⊢t)
⊢-subst Γ x τ Δ (suc ⊢e) ⊢t = suc (⊢-subst Γ x τ Δ ⊢e ⊢t)

-- the end of Substitution Lemma

preservation : ∀ {e e' τ}
               → [] ⊢ e ∶ τ 
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
preservation = {!!}

infixr 2 _⟼*_
data _⟼*_ : Term → Term → Set where
  refl  : ∀ {t} → t ⟼* t
  trans : ∀ {t u v} → t ⟼ u → u ⟼* v → t ⟼* v

-- big step semantics 
data _⇓_ : Term → Term → Set where
  zero : zero ⇓ zero

  suc  : ∀ {t n} 
         → t ⇓ n 
         → suc t ⇓ suc n

  Y  : ∀ {x e v} 
       → [(Y x e) / x ] e ⇓ v 
       → Y x e ⇓ v

  lam  : ∀ {x e} 
         → (ƛ x e) ⇓ (ƛ x e)

  app  : ∀ {t x e n v}
         → t ⇓ (ƛ x e) 
         → [ n / x ] e ⇓ v 
         → (t · n) ⇓ v

  ifz₀ : ∀ {t t₀ n t₁ v} 
         → t ⇓ zero 
         → t₀ ⇓ v 
         → ifz t t₀ n t₁ ⇓ v

  ifz₁ : ∀ {t n t₀ x t₁ v} 
         → t ⇓ suc n 
         → [ n / x ] t₁ ⇓ v 
         → ifz t t₀ x t₁ ⇓ v

-- if t ⇓ v then v is a closed value. 
⇓-Val : ∀ {t v} → t ⇓ v → Val v
⇓-Val = {!!}

-- every closed value v can be reduced to itself by ⇓ 
v⇓v : ∀ {v} → Val v → v ⇓ v
v⇓v = {!!}

-- many step reduction relation

-- the agreement of small-step and big-step semantics
⇓to⟼* : ∀ {t u} → t ⇓ u → t ⟼* u
⇓to⟼* = {!!}

⟼⇓to⇓ : ∀ {t u v} → t ⟼ u → u ⇓ v → t ⇓ v
⟼⇓to⇓ = {!!}

⟼*⇓to⇓ : ∀ {t u v} → t ⟼* u → u ⇓ v → t ⇓ v
⟼*⇓to⇓ = {!!}

⟼*to⇓ : ∀ {t v} → t ⟼* v → Val v → t ⇓ v
⟼*to⇓ d val = ⟼*⇓to⇓ d (v⇓v val)
