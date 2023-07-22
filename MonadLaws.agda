open import Agda.Primitive

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

data Maybe (A : Set) : Set where
 just : Maybe A
 nothing : Maybe A

bind : (A B : Set) → Maybe A → (A → Maybe B) → Maybe B
bind (just x) k = k x
bind nothing = nothing
