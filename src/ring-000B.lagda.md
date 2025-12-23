```agda
module ring-000B where

open import MLTT.Spartan
open import UF.Powerset

open import ring-0000
open Ring {{...}}
```

```
record IsIdeal {R : 𝓤 ̇ } {{_ : Ring R}} (I : 𝓟 R) : 𝓤 ̇  where
  no-eta-equality
  field
    closeL : ∀ x {i} → i ∈ I → x · i ∈ I
    closeR : ∀ x {i} → i ∈ I → i · x ∈ I
```
