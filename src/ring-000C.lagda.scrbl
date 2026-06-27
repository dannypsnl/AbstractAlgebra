@title{Ideals contain zero}
@taxon{Proposition}

@agda|{
module ring-000C where

open import MLTT.Spartan
open import UF.Powerset

open import ring-0000
open Ring {{...}}
open import ring-000B
}|

@p{這個命題說每個 Ideal 都有元素 @m{0}}

@agda|{
proposition-7 : {R : 𝓤 ̇ } {{_ : Ring R}} {i : R} (I : 𝓟 R) → IsIdeal I → i ∈ I → 0r ∈ I
proposition-7 {_}{R} {i} I is-ideal i∈I = transport (_∈ I) cancel m
  where
  open IsIdeal is-ideal

  neg : - i ∈ I
  neg = close-neg i∈I
  m : (i +ᴿ - i) ∈ I
  m = close-+ i∈I neg
}|
