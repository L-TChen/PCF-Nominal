module Transitive-Closure where

Rel : Set → Set₁
Rel A = A → A → Set

data [_] {A}(R : Rel A) : Rel A where
  refl  : ∀ {x} → [ R ] x x
  trans : ∀ {x y z} → R x y → [ R ] y z → [ R ] x z 

Trans : ∀ {A} → Rel A → Set
Trans R = ∀ {x y z} → R x y → R y z → R x z

Refl : ∀ {A} → Rel A → Set
Refl R = ∀ {x} → R x x

_⊆_ : ∀ {A} → (R S : Rel A) → Set
R ⊆ S = ∀ {x y} → R x y → S x y

[R]-refl : ∀ {A} → (R : Rel A) → Refl [ R ]
[R]-refl = {!!}

[R]-trans : ∀ {A : Set}{R : Rel A} → Trans [ R ]
[R]-trans = {!!}

Closure : ∀ {A : Set}{S R : Rel A}
  → Refl S
  → Trans S
  → R ⊆ S
  → [ R ] ⊆ S
Closure = {!!}
