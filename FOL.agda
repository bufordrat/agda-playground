module FOL where

open import Data.Product

teller5-1-a : {A : Set} ->
              {x : A} ->
              {k : A} ->
              {P D : A -> Set} -> 
              ((x : A) -> P x × D x) ->
              D k
teller5-1-a {A} {x} {k} prf = {!!}
