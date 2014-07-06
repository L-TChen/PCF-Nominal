module Transitive-Closure where

Rel : Set → Set₁
Rel A = A → A → Set

data [_] {A}(R : Rel A) : Rel A where
  refl  : ∀ {x} → [ R ] x x
  trans : ∀ {x y z} → R x y → [ R ] y z → [ R ] x z 

Transitive : ∀ {A} → Rel A → Set
Transitive R = ∀ {x y z} → R x y → R y z → R x z

Reflexive : ∀ {A} → Rel A → Set
Reflexive R = ∀ {x} → R x x

_⊆_ : ∀ {A} → (R S : Rel A) → Set
R ⊆ S = ∀ {x y} → R x y → S x y

[R]-refl : ∀ {A} → (R : Rel A) → Reflexive [ R ]
[R]-refl = {!!}

[R]-trans : ∀ {A : Set}{R : Rel A} → Transitive [ R ]
[R]-trans = {!!}

RTClosure : ∀ {A : Set}{S R : Rel A}
  → Reflexive S
  → Transitive S
  → R ⊆ S
  → [ R ] ⊆ S -- the "smallest" condition
RTClosure = {!!}
