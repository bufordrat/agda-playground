open import Agda.Primitive

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

data Maybe (A : Set) : Set where
 just : A → Maybe A
 nothing : Maybe A

bind : (A B : Set) → Maybe A → (A → Maybe B) → Maybe B
bind A B (just x) k = k x
bind A B nothing = nothing
