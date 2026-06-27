@title{Ideal}
@taxon{Definition}

@agda|{
module ring-000B where

open import MLTT.Spartan
open import UF.Powerset

open import ring-0000
open Ring {{...}}
}|

@agda|{
record IsIdeal {R : 𝓤 ̇ } {{_ : Ring R}} (I : 𝓟 R) : 𝓤 ̇  where
  no-eta-equality
  field
    close-+ : ∀ {i} {i2} → i ∈ I → i2 ∈ I → (i +ᴿ i2) ∈ I
    close-neg : ∀ {i} → i ∈ I → (- i) ∈ I
    closeL : ∀ r {i} → i ∈ I → r · i ∈ I
    closeR : ∀ r {i} → i ∈ I → i · r ∈ I
}|
