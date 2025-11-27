```
module Group.KerBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)

open import Group.Def
open Group {{...}}
open import Group.DefHom
open import Group.DefKer
open import Group.HomBasic
```

## Proposition 8

這個命題是說，如果 group homomorphism $i : H \to G$ 是 inclusion，那 Kernel 的元素其實只有單位元素 $e_H$。

```
proposition-8 : {H G : 𝓤 ̇} {{∈H : Group H}} {{∈G : Group G}}
  (i : H → G) → (is-hom : IsGroupHomomorphism H G i)
  → left-cancellable i
  → ((y : Ker H G i is-hom) → e ＝ y .pr₁)
proposition-8 {𝓤} {H}{G}{{∈H}}{{∈G}} i is-hom inclusion (h , p) = inclusion I
  where
  I : i e ＝ i h
  I = (proposition-4 i is-hom) then (sym p)
```

這也順便說明了，用 Propopsition 4 就已經知道 $\text{Ker}\ i$ 最少最少也有一個 $e_H$，因此任何 Kernel 都不是空集合。
