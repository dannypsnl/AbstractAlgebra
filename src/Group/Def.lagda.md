```agda
module Group.Def where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
```

A group is a nonempty set $G$, endowed with a binary operation

$$
\bullet : G \times G \to G
$$

such that

1. the operation is associative
2. there exists an identity element
3. each element of $G$ has an inverse with respect to the operation

```agda
record Group (G : 𝓤 ̇) : 𝓤 ̇ where
  field
    size : is-set G
    _∙_ : G → G → G
    ∙-assoc : associative _∙_
    e : G
    neu-l : left-neutral e _∙_
    neu-r : right-neutral e _∙_
    _⁻¹ : G → G
    cancel : {x : G} → ((x ⁻¹) ∙ x ＝ e) × (x ∙ (x ⁻¹) ＝ e)

  infix 40 _⁻¹
  infixl 20 _∙_
```
