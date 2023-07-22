open import Agda.Primitive

data Maybe (A : Set) : Set where
 just : A → Maybe A
 nothing : Maybe A

bind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bind (just x) k = k x
bind nothing k = nothing

